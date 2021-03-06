﻿namespace MBrace.Thespian.Runtime

open System
open System.Threading

open Nessos.FsPickler
open Nessos.Vagabond
open Nessos.Thespian

open MBrace.Core
open MBrace.Core.Internals
open MBrace.Runtime
open MBrace.Runtime.Utils.PrettyPrinters

/// Describes a pickled MBrace job.
/// Can be used without any need for assembly dependencies being loaded.
type internal Pickle =
    /// Single cloud job
    | Single of job:Pickle<CloudJob>
    /// Cloud job is part of a batch enqueue.
    /// Pickled together for size optimization reasons.
    | Batch of index:int * jobs:Pickle<CloudJob []>
with
    /// Size of pickle in bytes
    member p.Size =
        match p with
        | Single sp -> sp.Bytes.LongLength
        | Batch(_,sp) -> sp.Bytes.LongLength

/// Pickled MBrace job entry.
/// Can be used without need for assembly dependencies being loaded.
type internal PickledJob =
    {
        /// Parent task entry as recorded in cluster.
        TaskEntry : ICloudTaskCompletionSource
        /// Unique job identifier
        JobId : string
        /// Job type enumeration
        JobType : JobType
        /// Job pretty printed return type
        Type : string
        /// Declared target worker for job
        Target : IWorkerId option
        /// Pickled job contents
        Pickle : Pickle
    }

/// Messages accepted by a job monitoring actor
type internal JobLeaseMonitorMsg =
    /// Declare job completed
    | Completed
    /// Declare job execution resulted in fault
    | WorkerDeclaredFault of ExceptionDispatchInfo
    /// Declare worker executing job has died
    | WorkerDeath

type private JobQueueMsg =
    | Enqueue of PickledJob * JobFaultInfo
    | BatchEnqueue of PickledJob []
    | TryDequeue of IWorkerId * IReplyChannel<(PickledJob * JobFaultInfo * ActorRef<JobLeaseMonitorMsg>) option>

module private JobLeaseMonitor =
    
    /// <summary>
    ///     Creates an local actor that monitors job execution progress.
    ///     It is tasked to re-enqueue the job in case of fault/worker death.
    /// </summary>
    /// <param name="workerMonitor">Cluster worker monitor.</param>
    /// <param name="queue">Parent job queue actor.</param>
    /// <param name="faultInfo">Current fault state of the job.</param>
    /// <param name="job">Job instance being monitored.</param>
    /// <param name="interval">Monitor interval.</param>
    /// <param name="worker">Executing worker id.</param>
    let create (workerMonitor : WorkerManager) (queue : ActorRef<JobQueueMsg>) 
                (faultInfo : JobFaultInfo) (job : PickledJob) 
                (interval : TimeSpan) (worker : IWorkerId) =

        let cts = new CancellationTokenSource()

        // no tail recursive loop, expected to receive single message
        let behaviour (self : Actor<JobLeaseMonitorMsg>) = async {
            let! msg = self.Receive()
            match msg with
            | Completed -> return ()
            | WorkerDeclaredFault edi ->
                let faultCount = faultInfo.FaultCount + 1
                let faultInfo = FaultDeclaredByWorker(faultCount, edi, worker)
                do! queue.AsyncPost(Enqueue (job, faultInfo))

            | WorkerDeath ->
                let faultCount = faultInfo.FaultCount + 1
                let faultInfo = WorkerDeathWhileProcessingJob(faultCount, worker)
                do! queue.AsyncPost(Enqueue (job, faultInfo))

            cts.Cancel()
        }

        let ref = Actor.bind behaviour |> Actor.Publish |> Actor.ref
        let rec poller () = async {
            let! isAlive = workerMonitor.IsAlive worker |> Async.Catch
            match isAlive with
            | Choice1Of2 true | Choice2Of2 _ ->
                do! Async.Sleep(int interval.TotalMilliseconds)
                return! poller ()

            | Choice1Of2 false ->
                ref <-- WorkerDeath
        }

        Async.Start(poller(), cts.Token)
        ref

/// Job lease token implementation, received when dequeuing a job from the queue.
type JobLeaseToken internal (pjob : PickledJob, faultInfo : JobFaultInfo, leaseMonitor : ActorRef<JobLeaseMonitorMsg>) =

    interface ICloudJobLeaseToken with
        member x.DeclareCompleted() = async {
            leaseMonitor <-- Completed
        }
        
        member x.DeclareFaulted(edi: ExceptionDispatchInfo) = async {
            leaseMonitor <-- WorkerDeclaredFault edi
        }

        member x.Type = pjob.Type

        member x.JobType = pjob.JobType

        member x.TargetWorker = pjob.Target

        member x.Size = pjob.Pickle.Size

        member x.TaskEntry = pjob.TaskEntry
        
        member x.FaultInfo = faultInfo
        
        member x.GetJob(): Async<CloudJob> = async {
            return
                match pjob.Pickle with
                | Single pj -> Config.Serializer.UnPickleTyped pj
                | Batch(i,pjs) -> let js = Config.Serializer.UnPickleTyped pjs in js.[i]
        }
        
        member x.Id: string = pjob.JobId


/// Job Queue actor state
type private QueueState = 
    {
        Queue : JobQueueTopic
        LastCleanup : DateTime
    }
with
    static member Empty = { Queue = JobQueueTopic.Empty ; LastCleanup = DateTime.Now }

and private JobQueueTopic = TopicQueue<IWorkerId, PickledJob * JobFaultInfo>

/// Provides a distributed, fault-tolerant queue implementation
[<AutoSerializable(true)>]
type JobQueue private (source : ActorRef<JobQueueMsg>) =

    interface IJobQueue with
        member x.BatchEnqueue(jobs: CloudJob []) = async {
            // TODO: sifting & cloud values
            let pickle = Config.Serializer.PickleTyped jobs
            let mkPickle (index:int) (job : CloudJob) =
                {
                    TaskEntry = job.TaskEntry
                    JobId = job.Id
                    Type = Type.prettyPrint job.Type
                    Target = job.TargetWorker
                    JobType = job.JobType
                    Pickle = Batch(index, pickle)
                }

            let items = jobs |> Array.mapi mkPickle
            do! source.AsyncPost (BatchEnqueue items)
        }
        
        member x.Enqueue (job: CloudJob) = async {
            let item =
                {
                    TaskEntry = job.TaskEntry
                    JobId = job.Id
                    JobType = job.JobType
                    Type = Type.prettyPrint job.Type
                    Target = job.TargetWorker
                    Pickle = Single(Config.Serializer.PickleTyped job)
                }

            do! source.AsyncPost (Enqueue (item, NoFault))
        }
        
        member x.TryDequeue(worker : IWorkerId) = async {
            let! result = source <!- fun ch -> TryDequeue(worker, ch)
            match result with
            | Some(msg, faultState, leaseMonitor) ->
                let leaseToken = new JobLeaseToken(msg, faultState, leaseMonitor)
                return Some(leaseToken :> ICloudJobLeaseToken)
            | None -> return None
        }

    /// <summary>
    ///     Creates a new job queue instance running in the local process.
    /// </summary>
    /// <param name="workerMonitor">Worker monitor instance.</param>
    /// <param name="cleanupInterval">Topic queue cleanup interval. Defaults to 10 seconds.</param>
    static member Create(workerMonitor : WorkerManager, ?cleanupInterval : TimeSpan) =
        let cleanupThreshold = defaultArg cleanupInterval (TimeSpan.FromSeconds 10.)

        let behaviour (self : Actor<JobQueueMsg>) (state : QueueState) (msg : JobQueueMsg) = async {
            match msg with
            | Enqueue (pJob, faultState) -> 
                let queue' = state.Queue.Enqueue((pJob, faultState), ?topic = pJob.Target)
                return { state with Queue = queue' }

            | BatchEnqueue(pJobs) ->
                let queue' = (state.Queue, pJobs) ||> Array.fold (fun q j -> q.Enqueue((j, NoFault), ?topic = j.Target))
                return { state with Queue = queue' }

            | TryDequeue(worker, rc) ->
                let state =
                    if DateTime.Now - state.LastCleanup > cleanupThreshold then
                        // remove jobs from worker topics if inactive.
                        let removed, state' = state.Queue.Cleanup (workerMonitor.IsAlive >> Async.RunSync >> not)
                        let appendRemoved (s:JobQueueTopic) (j : PickledJob, faultState : JobFaultInfo) =
                            let worker = Option.get j.Target
                            let j = { j with Target = None }
                            let faultCount = faultState.FaultCount + 1
                            let faultState = IsTargetedJobOfDeadWorker(faultCount, worker)
                            s.Enqueue((j, faultState), ?topic = None)

                        let queue2 = removed |> Seq.fold appendRemoved state'
                        { Queue = queue2 ; LastCleanup = DateTime.Now }
                    else
                        state

                let! isDeclaredAlive = workerMonitor.IsAlive worker
                match state.Queue.TryDequeue worker with
                | Some((pj,fs), queue') when isDeclaredAlive ->
                    let jlm = JobLeaseMonitor.create workerMonitor self.Ref fs pj (TimeSpan.FromSeconds 1.) worker
                    do! rc.Reply(Some(pj, fs, jlm))
                    return { state with Queue = queue' }

                | _ ->
                    do! rc.Reply None
                    return state

        }

        let ref =
            Actor.SelfStateful QueueState.Empty behaviour
            |> Actor.Publish
            |> Actor.ref

        new JobQueue(ref)
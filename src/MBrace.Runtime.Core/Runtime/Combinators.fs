﻿module internal MBrace.Runtime.Combinators

open System.Runtime.Serialization

open MBrace.Core
open MBrace.Core.Internals

open Nessos.FsPickler
open Nessos.Vagabond

open MBrace.Core
open MBrace.Core.Internals
open MBrace.Runtime.Utils
open MBrace.Runtime.Utils.PrettyPrinters
open MBrace.Runtime.InMemoryRuntime

#nowarn "444"

let inline private withCancellationToken (cts : ICloudCancellationToken) (ctx : ExecutionContext) =
    { ctx with CancellationToken = cts }

let private asyncFromContinuations f =
    Cloud.FromContinuations(fun ctx cont -> JobExecutionMonitor.ProtectAsync ctx (f ctx cont))

let private ensureSerializable (t : 'T) =
    try FsPickler.EnsureSerializable t ; None
    with e -> Some e

let private extractWorkerId (runtime : IRuntimeManager) (worker : IWorkerRef option) =
    match worker with
    | None -> None
    | Some(:? WorkerRef as w) when areReflectiveEqual w.RuntimeId runtime.Id  -> Some w.WorkerId
    | _ -> invalidArg "target" <| sprintf "WorkerRef '%O' does not belong to the cluster." worker

let private extractWorkerIds (runtime : IRuntimeManager) (computations : (#Cloud<'T> * IWorkerRef option) []) =
    computations
    |> Array.map (fun (c,w) -> c, extractWorkerId runtime w)

/// <summary>
///     Defines a workflow that schedules provided cloud workflows for parallel computation.
/// </summary>
/// <param name="runtime">Runtime management object.</param>
/// <param name="parentTask">Parent task info object.</param>
/// <param name="faultPolicy">Current cloud job being executed.</param>
/// <param name="computations">Computations to be executed in parallel.</param>
let runParallel (runtime : IRuntimeManager) (parentTask : ICloudTaskCompletionSource) 
                (faultPolicy : FaultPolicy) (computations : seq<#Cloud<'T> * IWorkerRef option>) : Cloud<'T []> =

    asyncFromContinuations(fun ctx cont -> async {
        match (try Seq.toArray computations |> Choice1Of2 with e -> Choice2Of2 e) with
        | Choice2Of2 e -> cont.Exception ctx (ExceptionDispatchInfo.Capture e)
        // Early detect if return type is not serializable.
        | Choice1Of2 _ when not <| FsPickler.IsSerializableType<'T>() ->
            let msg = sprintf "Cloud.Parallel workflow uses non-serializable type '%s'." (Type.prettyPrint typeof<'T>)
            let e = new SerializationException(msg)
            cont.Exception ctx (ExceptionDispatchInfo.Capture e)

        | Choice1Of2 [| |] -> cont.Success ctx [||]
        // schedule single-child parallel workflows in current job
        // force copy semantics by cloning the workflow
        | Choice1Of2 [| (comp, None) |] ->
            let clone = try FsPickler.Clone ((comp, cont)) |> Choice1Of2 with e -> Choice2Of2 e
            match clone with
            | Choice1Of2 (comp, cont) -> 
                let cont' = Continuation.map (fun t -> [| t |]) cont
                Cloud.StartWithContinuations(comp, cont', ctx)

            | Choice2Of2 e ->
                let msg = sprintf "Cloud.Parallel<%s> workflow uses non-serializable closures." (Type.prettyPrint typeof<'T>)
                let se = new SerializationException(msg, e)
                cont.Exception ctx (ExceptionDispatchInfo.Capture se)


        | Choice1Of2 computations ->
            // distributed computation, ensure that closures are serializable
            match ensureSerializable (computations, cont) with
            | Some e ->
                let msg = sprintf "Cloud.Parallel<%s> workflow uses non-serializable closures." (Type.prettyPrint typeof<'T>)
                let se = new SerializationException(msg, e)
                cont.Exception ctx (ExceptionDispatchInfo.Capture se)

            | None ->

            // ensure that target workers are valid in the current cluster context
            let computations = extractWorkerIds runtime computations

            // request runtime resources required for distribution coordination
            let currentCts = ctx.CancellationToken
            let! childCts = CloudCancellationToken.Create(runtime.CancellationEntryFactory, [|currentCts|], elevate = true)
            let! resultAggregator = runtime.ResultAggregatorFactory.CreateResultAggregator<'T>(capacity = computations.Length)
            let! cancellationLatch = runtime.CounterFactory.CreateCounter(initialValue = 0)

            let onSuccess i ctx (t : 'T) = 
                async {
                    // check if result value can be serialized first.
                    match ensureSerializable t with
                    | Some e ->
                        let! latchCount = cancellationLatch.Increment()
                        if latchCount = 1 then // is first job to request workflow cancellation, grant access
                            childCts.Cancel()
                            let msg = sprintf "Cloud.Parallel<%s> workflow failed to serialize result." (Type.prettyPrint typeof<'T>) 
                            let se = new SerializationException(msg, e)
                            cont.Exception (withCancellationToken currentCts ctx) (ExceptionDispatchInfo.Capture se)

                        else // cancellation already triggered by different party, just declare job completed.
                            JobExecutionMonitor.TriggerCompletion ctx
                    | None ->
                        let! isCompleted = resultAggregator.SetResult(i, t, overwrite = true)
                        if isCompleted then 
                            // this is the last child callback, aggregate result and call parent continuation
                            let! results = resultAggregator.ToArray()
                            childCts.Cancel()
                            cont.Success (withCancellationToken currentCts ctx) results

                        else // results pending, just declare job completed.
                            JobExecutionMonitor.TriggerCompletion ctx
                } |> JobExecutionMonitor.ProtectAsync ctx

            let onException ctx e =
                async {
                    match ensureSerializable e with
                    | Some e ->
                        let! latchCount = cancellationLatch.Increment()
                        if latchCount = 1 then // is first job to request workflow cancellation, grant access
                            childCts.Cancel()
                            let msg = sprintf "Cloud.Parallel<%s> workflow failed to serialize result." (Type.prettyPrint typeof<'T>) 
                            let se = new SerializationException(msg, e)
                            cont.Exception (withCancellationToken currentCts ctx) (ExceptionDispatchInfo.Capture se)

                        else // cancellation already triggered by different party, just declare job completed.
                            JobExecutionMonitor.TriggerCompletion ctx
                        
                    | None ->
                        let! latchCount = cancellationLatch.Increment()
                        if latchCount = 1 then // is first job to request workflow cancellation, grant access
                            childCts.Cancel()
                            cont.Exception (withCancellationToken currentCts ctx) e
                        else // cancellation already triggered by different party, declare job completed.
                            JobExecutionMonitor.TriggerCompletion ctx

                } |> JobExecutionMonitor.ProtectAsync ctx

            let onCancellation ctx c =
                async {
                    let! latchCount = cancellationLatch.Increment()
                    if latchCount = 1 then // is first job to request workflow cancellation, grant access
                        childCts.Cancel()
                        cont.Cancellation ctx c
                    else // cancellation already triggered by different party, declare job completed.
                        JobExecutionMonitor.TriggerCompletion ctx
                } |> JobExecutionMonitor.ProtectAsync ctx

            // Create jobs and enqueue
            do!
                computations
                |> Array.mapi (fun i (c,w) -> CloudJob.Create(parentTask, childCts, faultPolicy, onSuccess i, onException, onCancellation, JobType.ParallelChild(i, computations.Length), c, ?target = w))
                |> runtime.JobQueue.BatchEnqueue
                    
            JobExecutionMonitor.TriggerCompletion ctx })

/// <summary>
///     Defines a workflow that schedules provided nondeterministic cloud workflows for parallel computation.
/// </summary>
/// <param name="runtime">Runtime management object.</param>
/// <param name="parentTask">Parent task info object.</param>
/// <param name="faultPolicy">Current cloud job being executed.</param>
/// <param name="computations">Computations to be executed in parallel.</param>
let runChoice (runtime : IRuntimeManager) (parentTask : ICloudTaskCompletionSource) 
                (faultPolicy : FaultPolicy) (computations : seq<#Cloud<'T option> * IWorkerRef option>) =

    asyncFromContinuations(fun ctx cont -> async {
        match (try Seq.toArray computations |> Choice1Of2 with e -> Choice2Of2 e) with
        | Choice2Of2 e -> cont.Exception ctx (ExceptionDispatchInfo.Capture e)
        | Choice1Of2 [||] -> cont.Success ctx None
        // schedule single-child parallel workflows in current job
        // force copy semantics by cloning the workflow
        | Choice1Of2 [| (comp, None) |] -> 
            let clone = try FsPickler.Clone ((comp, cont)) |> Choice1Of2 with e -> Choice2Of2 e
            match clone with
            | Choice1Of2 (comp, cont) -> Cloud.StartWithContinuations(comp, cont, ctx)
            | Choice2Of2 e ->
                let msg = sprintf "Cloud.Choice<%s> workflow uses non-serializable closures." (Type.prettyPrint typeof<'T>)
                let se = new SerializationException(msg, e)
                cont.Exception ctx (ExceptionDispatchInfo.Capture se)

        | Choice1Of2 computations ->
            // distributed computation, ensure that closures are serializable
            match ensureSerializable (computations, cont) with
            | Some e ->
                let msg = sprintf "Cloud.Choice<%s> workflow uses non-serializable closures." (Type.prettyPrint typeof<'T>)
                let se = new SerializationException(msg, e)
                cont.Exception ctx (ExceptionDispatchInfo.Capture se)

            | None ->

            // ensure that target workers are valid in the current cluster context
            let computations = extractWorkerIds runtime computations

            // request runtime resources required for distribution coordination
            let n = computations.Length // avoid capturing computation array in continuation closures
            let currentCts = ctx.CancellationToken
            let! childCts = CloudCancellationToken.Create(runtime.CancellationEntryFactory, [|currentCts|], elevate = true)
            let! completionLatch = runtime.CounterFactory.CreateCounter(initialValue = 0)
            let! cancellationLatch = runtime.CounterFactory.CreateCounter(initialValue = 0)

            let onSuccess ctx (topt : 'T option) =
                async {
                    if Option.isSome topt then // 'Some' result, attempt to complete workflow
                        let! latchCount = cancellationLatch.Increment()
                        if latchCount = 1 then 
                            // first child to initiate cancellation, grant access to parent scont
                            childCts.Cancel ()
                            cont.Success (withCancellationToken currentCts ctx) topt
                        else
                            // workflow already cancelled, declare job completion
                            JobExecutionMonitor.TriggerCompletion ctx
                    else
                        // 'None', increment completion latch
                        let! completionCount = completionLatch.Increment ()
                        if completionCount = n then 
                            // is last job to complete with 'None', pass None to parent scont
                            childCts.Cancel()
                            cont.Success (withCancellationToken currentCts ctx) None
                        else
                            // other jobs pending, declare job completion
                            JobExecutionMonitor.TriggerCompletion ctx
                } |> JobExecutionMonitor.ProtectAsync ctx

            let onException ctx e =
                async {
                    let! latchCount = cancellationLatch.Increment()
                    if latchCount = 1 then // is first job to request workflow cancellation, grant access
                        childCts.Cancel ()
                        cont.Exception (withCancellationToken currentCts ctx) e
                    else // cancellation already triggered by different party, declare job completed.
                        JobExecutionMonitor.TriggerCompletion ctx
                } |> JobExecutionMonitor.ProtectAsync ctx

            let onCancellation ctx c =
                async {
                    let! latchCount = cancellationLatch.Increment()
                    if latchCount = 1 then // is first job to request workflow cancellation, grant access
                        childCts.Cancel()
                        cont.Cancellation (withCancellationToken currentCts ctx) c
                    else // cancellation already triggered by different party, declare job completed.
                        JobExecutionMonitor.TriggerCompletion ctx
                } |> JobExecutionMonitor.ProtectAsync ctx

            // create child jobs
            do!
                computations
                |> Array.mapi (fun i (c,w) -> CloudJob.Create(parentTask, childCts, faultPolicy, onSuccess, onException, onCancellation, JobType.ChoiceChild(i, computations.Length), c, ?target = w))
                |> runtime.JobQueue.BatchEnqueue
                    
            JobExecutionMonitor.TriggerCompletion ctx })

/// <summary>
///     Executes provided cloud workflow as a cloud task using the provided resources and parameters.
/// </summary>
/// <param name="runtime">Runtime management object.</param>
/// <param name="dependencies">Vagabond dependencies for computation.</param>
/// <param name="taskId">Task id for computation.</param>
/// <param name="faultPolicy">Fault policy for computation.</param>
/// <param name="token">Optional cancellation token for computation.</param>
/// <param name="target">Optional target worker identifier.</param>
/// <param name="computation">Computation to be executed.</param>
let runStartAsCloudTask (runtime : IRuntimeManager) (dependencies : AssemblyId[]) (taskName : string option)
                        (faultPolicy:FaultPolicy) (token : ICloudCancellationToken option) 
                        (target : IWorkerRef option) (computation : Cloud<'T>) = async {

    if not <| FsPickler.IsSerializableType<'T> () then
        let msg = sprintf "Cloud task returns non-serializable type '%s'." (Type.prettyPrint typeof<'T>)
        return raise <| new SerializationException(msg)
    else

    match ensureSerializable computation with
    | Some e ->
        let msg = sprintf "Cloud task of type '%s' uses non-serializable closure." (Type.prettyPrint typeof<'T>)
        return raise <| new SerializationException(msg, e)

    | None ->

        // ensure that target worker is valid in current cluster context
        let target = extractWorkerId runtime target

        let! cts = async {
            match token with
            | Some ct -> return! CloudCancellationToken.Create(runtime.CancellationEntryFactory, parents = [|ct|], elevate = true)
            | None -> return! CloudCancellationToken.Create(runtime.CancellationEntryFactory, elevate = true)
        }

        let taskInfo =
            {
                Name = taskName
                CancellationTokenSource = cts
                Dependencies = dependencies
                ReturnTypeName = Type.prettyPrint typeof<'T>
                ReturnType = runtime.Serializer.PickleTyped typeof<'T>
            }

        let! tcs = runtime.TaskManager.CreateTask taskInfo

        let setResult ctx (result : TaskResult) status = 
            async {
                match ensureSerializable result with
                | Some e ->
                    let msg = sprintf "Could not serialize result for task '%s' of type '%s'." tcs.Id (Type.prettyPrint typeof<'T>)
                    let se = new SerializationException(msg, e)
                    let! _ = tcs.TrySetResult(Exception (ExceptionDispatchInfo.Capture se))
                    do! tcs.DeclareStatus Faulted
                | None ->
                    let! _ = tcs.TrySetResult(result)
                    do! tcs.DeclareStatus status

                cts.Cancel()
                JobExecutionMonitor.TriggerCompletion ctx
            } |> JobExecutionMonitor.ProtectAsync ctx

        let scont ctx t = setResult ctx (Completed t) CloudTaskStatus.Completed
        let econt ctx e = setResult ctx (Exception e) CloudTaskStatus.UserException
        let ccont ctx c = setResult ctx (Cancelled c) CloudTaskStatus.Canceled

        let job = CloudJob.Create (tcs, cts, faultPolicy, scont, econt, ccont, JobType.TaskRoot, computation, ?target = target)
        do! runtime.JobQueue.Enqueue job
        return new CloudTask<'T>(tcs)
}
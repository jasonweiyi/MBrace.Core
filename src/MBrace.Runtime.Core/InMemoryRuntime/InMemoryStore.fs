﻿namespace MBrace.Runtime.InMemoryRuntime

open System
open System.Collections.Generic
open System.Collections.Concurrent
open System.Runtime.Serialization
open System.Threading
open System.Threading.Tasks

open Nessos.FsPickler
open Nessos.FsPickler.Hashing

open MBrace.Core
open MBrace.Core.Internals

open MBrace.Runtime.Utils

[<AutoSerializable(false); CloneableOnly>]
type InMemoryValue<'T> internal (value : 'T, hash : HashResult) =
    interface ICloudValue<'T> with
        member x.Id: string = hash.Id
        member x.Size: int64 = hash.Length
        member x.StorageLevel : StorageLevel = StorageLevel.MemoryOnly
        member x.Type: Type = typeof<'T>
        member x.GetBoxedValueAsync(): Async<obj> = async { return value :> obj }
        member x.GetValueAsync(): Async<'T> = async { return value }
        member x.IsCachedLocally: bool = true
        member x.Value: 'T = value
        member x.GetBoxedValue () : obj = value :> obj
        member x.Dispose() = async.Return()

[<AutoSerializable(false); Sealed; CloneableOnly>]
type InMemoryArray<'T> internal (value : 'T [], hash : HashResult) =
    inherit InMemoryValue<'T[]> (value, hash)

    interface ICloudArray<'T> with
        member x.Length = value.Length

    interface ICloudCollection<'T> with
        member x.IsKnownCount: bool = true
        member x.IsKnownSize: bool = true
        member x.IsMaterialized: bool = true
        member x.GetCount(): Async<int64> =  async { return value.LongLength }
        member x.GetSize(): Async<int64> = async { return hash.Length }
        member x.ToEnumerable(): Async<seq<'T>> = async { return value :> _ }

/// Provides an In-Memory CloudValue implementation
[<Sealed; AutoSerializable(false)>] 
type InMemoryValueProvider () =
    let id = mkUUID()
    let cache = new ConcurrentDictionary<string, ICloudValue>()

    let partitionBySize (threshold:int64) (ts:seq<'T>) =
        let accumulated = new ResizeArray<'T []>()
        let array = new ResizeArray<'T> ()
        let pickler = FsPickler.GeneratePickler<'T>()
        let mutable size = 0L
        use enum = ts.GetEnumerator()
        while enum.MoveNext() do
            let t = enum.Current
            array.Add t
            size <- size + FsPickler.ComputeSize(t, pickler = pickler)
            if size > threshold then
                accumulated.Add(array.ToArray())
                array.Clear()
                size <- 0L

        if array.Count > 0 then
            accumulated.Add(array.ToArray())
            array.Clear()

        accumulated :> seq<'T []>

    let computeHash (payload : 'T) =
        try FsPickler.ComputeHash payload
        with e ->
            let msg = sprintf "Value '%A' is not serializable." payload
            raise <| new SerializationException(msg, e)

    let createArray (payload : 'T []) =
        let hash = computeHash payload
        cache.GetOrAdd(hash.Id, fun id -> new InMemoryArray<'T>(payload, hash) :> ICloudValue) :?> ICloudArray<'T>

    let createValue (payload : 'T) =
        let hash = computeHash payload
        cache.GetOrAdd(hash.Id,
            fun id ->
                let t = typeof<'T>
                if t.IsArray && t.GetArrayRank() = 1 then
                    let et = t.GetElementType()
                    let eet = Existential.FromType et
                    eet.Apply 
                        { new IFunc<ICloudValue> with 
                            member __.Invoke<'et> () = 
                                new InMemoryArray<'et>(payload :> obj :?> 'et [], hash) :> ICloudValue }
                else
                    new InMemoryValue<'T>(payload, hash) :> ICloudValue) :?> ICloudValue<'T>

    interface ICloudValueProvider with
        member x.Id: string = id
        member x.Name: string = "In-Memory Value Provider"
        member x.DefaultStorageLevel : StorageLevel = StorageLevel.MemoryOnly
        member x.IsSupportedStorageLevel (level : StorageLevel) = StorageLevel.MemoryOnly = level
        member x.CreateCloudValue(payload: 'T, _ : StorageLevel): Async<ICloudValue<'T>> = async {
            return createValue payload
        }

        member x.CreatePartitionedArray(payload : seq<'T>, _ : StorageLevel, ?partitionThreshold : int64) = async {
            match partitionThreshold with
            | None -> return [| createArray (Seq.toArray payload) |]
            | Some pt -> return partitionBySize pt payload |> Seq.map createArray |> Seq.toArray
        }
        
        member x.Dispose(_: ICloudValue): Async<unit> = async.Zero()
        member x.DisposeAllValues(): Async<unit> = async { return cache.Clear() }
        member x.GetById(id : string) : Async<ICloudValue> = async { return cache.[id] }
        member x.GetAllValues(): Async<ICloudValue []> = async { return cache |> Seq.map (fun kv -> kv.Value) |> Seq.toArray }


[<AutoSerializable(false); Sealed; CloneableOnly>]
type InMemoryAtom<'T> internal (id : string, initial : 'T, mode : MemoryEmulation) =
    // false: always clone value when reading payload
    let clone (t:'T) = EmulatedValue.create mode false t

    let mutable atom = Some <| Atom.create (clone initial)
    let getAtom() =
        match atom with
        | None -> raise <| new ObjectDisposedException(id)
        | Some a -> a

    interface ICloudAtom<'T> with
        member x.Id = id
        member x.Value = async { return getAtom().Value.Value }

        member x.Transact(updater : 'T -> 'R * 'T, _) = async { 
            let transacter (ct : EmulatedValue<'T>) : EmulatedValue<'T> * 'R =
                let r,t' = updater ct.Value
                clone t', r

            return getAtom().Transact transacter
        }

        member x.Force(value:'T) = async { 
            return getAtom().Force(clone value)
        }

        member x.Dispose () = async { return atom <- None }

[<Sealed; AutoSerializable(false)>]
type InMemoryAtomProvider (mode : MemoryEmulation) =
    let id = mkUUID()

    /// <summary>
    ///     Creates an In-Memory Atom configuration object.
    /// </summary>
    /// <param name="mode">Memory emulation mode.</param>
    static member CreateConfiguration(mode : MemoryEmulation) =
        let imap = new InMemoryAtomProvider(mode)
        CloudAtomConfiguration.Create(imap)

    interface ICloudAtomProvider with
        member __.Name = "InMemoryAtomProvider"
        member __.Id = id
        member __.IsSupportedValue _ = true
        member __.CreateAtom<'T>(_, init : 'T) = async { 
            let id = mkUUID()
            return new InMemoryAtom<'T>(id, init, mode) :> _ 
        }

        member __.CreateUniqueContainerName () = mkUUID()
        member __.DisposeContainer _ = raise <| new NotSupportedException()


[<Sealed; AutoSerializable(false); CloneableOnly>]
type InMemoryQueue<'T> internal (id : string, mode : MemoryEmulation) =
    // true: value will be dequeued only once so clone on eqnueue only
    let clone (t : 'T) = EmulatedValue.create mode true t
    let mutable isDisposed = false
    let checkDisposed () =
        if isDisposed then raise <| new ObjectDisposedException("Queue has been disposed.")

    let mbox = new MailboxProcessor<EmulatedValue<'T>>(fun _ -> async.Zero())

    interface ICloudQueue<'T> with
        member x.Id: string = id

        member x.Count: Async<int64> = async {
            checkDisposed()
            return int64 mbox.CurrentQueueLength
        }
        
        member x.Dequeue(?timeout: int): Async<'T> = async {
            checkDisposed()
            let! ev = mbox.Receive(?timeout = timeout)
            return ev.Value
        }
        
        member x.Dispose(): Async<unit> = async {
            isDisposed <- true
        }
        
        member x.Enqueue(message: 'T): Async<unit> = async {
            checkDisposed()
            return mbox.Post (clone message)
        }
        
        member x.EnqueueBatch(messages: seq<'T>): Async<unit> = async {
            do
                checkDisposed()
                for m in messages do mbox.Post (clone m)
        }
        
        member x.TryDequeue(): Async<'T option> = async {
            checkDisposed()
            let! result = mbox.TryReceive(timeout = 0)
            return result |> Option.map (fun r -> r.Value)
        }

/// Defines an in-memory queue factory using mailbox processor
[<Sealed; AutoSerializable(false)>]
type InMemoryQueueProvider (mode : MemoryEmulation) =
    let id = mkUUID()

    /// <summary>
    ///     Creates an In-Memory Queue configuration object.
    /// </summary>
    /// <param name="mode">Memory emulation mode.</param>
    static member CreateConfiguration(mode : MemoryEmulation) =
        let imqp = new InMemoryQueueProvider(mode)
        CloudQueueConfiguration.Create(imqp)

    interface ICloudQueueProvider with
        member __.Name = "InMemoryQueueProvider"
        member __.Id = id
        member __.CreateUniqueContainerName () = mkUUID()

        member __.CreateQueue<'T> (container : string) = async {
            if not <| MemoryEmulation.isShared mode && not <| FsPickler.IsSerializableType<'T>() then
                let msg = sprintf "Cannot create queue for non-serializable type '%O'." typeof<'T>
                raise <| new SerializationException(msg)

            let id = sprintf "%s/%s" container <| mkUUID()
            return new InMemoryQueue<'T>(id, mode) :> ICloudQueue<'T>
        }

        member __.DisposeContainer _ = async.Zero()

[<Sealed; AutoSerializable(false); CloneableOnly>]
type InMemoryDictionary<'T> internal (mode : MemoryEmulation) =
    let id = mkUUID()
    let clone (t:'T) = EmulatedValue.create mode true t
    let dict = new ConcurrentDictionary<string, EmulatedValue<'T>> ()
    
    interface ICloudDictionary<'T> with
        member x.Add(key : string, value : 'T) : Async<unit> =
            async { return dict.[key] <- clone value }

        member x.TryAdd(key: string, value: 'T): Async<bool> = 
            async { return dict.TryAdd(key, clone value) }
                    
        member x.Transact(key: string, transacter: 'T option -> 'R * 'T, _): Async<'R> = async {
            let result = ref Unchecked.defaultof<'R>
            let updater (curr : EmulatedValue<'T> option) =
                let currv = curr |> Option.map (fun c -> c.Value)
                let r, t = transacter currv
                result := r
                clone t

            let _ = dict.AddOrUpdate(key, (fun _ -> updater None), fun _ curr -> updater (Some curr))
            return result.Value
        }
                    
        member x.ContainsKey(key: string): Async<bool> = 
            async { return dict.ContainsKey key }

        member x.IsKnownCount = true
        member x.IsKnownSize = true
        member x.IsMaterialized = true
                    
        member x.GetCount(): Async<int64> = 
            async { return int64 dict.Count }

        member x.GetSize(): Async<int64> = 
            async { return int64 dict.Count }
                    
        member x.Dispose(): Async<unit> = async.Zero()

        member x.Id: string = id
                    
        member x.Remove(key: string): Async<bool> = 
            async { return dict.TryRemove key |> fst }
                    
        member x.ToEnumerable(): Async<seq<KeyValuePair<string, 'T>>> = 
            async { return dict |> Seq.map (fun kv -> new KeyValuePair<_,_>(kv.Key, kv.Value.Value)) }
                    
        member x.TryFind(key: string): Async<'T option> = 
            async { return let ok,v = dict.TryGetValue key in if ok then Some v.Value else None }

/// Defines an in-memory dictionary factory using ConcurrentDictionary
[<Sealed; AutoSerializable(false)>]
type InMemoryDictionaryProvider (mode : MemoryEmulation) =
    let id = mkUUID()

    interface ICloudDictionaryProvider with
        member s.Name = "InMemoryDictionaryProvider"
        member s.Id = id
        member s.IsSupportedValue _ = true
        member s.Create<'T> () = async {
            if not <| MemoryEmulation.isShared mode && not <| FsPickler.IsSerializableType<'T>() then
                let msg = sprintf "Cannot create queue for non-serializable type '%O'." typeof<'T>
                raise <| new SerializationException(msg)

            return new InMemoryDictionary<'T>(mode) :> ICloudDictionary<'T>
        }
﻿namespace MBrace.Core

open System.Runtime.Serialization

open MBrace.Core.Internals

// Cloud<'T> is a continuation-based computation that can be distributed.
// It takes two parameters, an ExecutionContext and a continuation triple.
// Importantly, the two values must remain distinct in order for distribution
// to be actuated effectively. ExecutionContext contains resources specific
// to the local executing process (like System.Threading.CancellationToken or open sockets)
// and is therefore not serializable, whereas Continuation<'T> is intended for
// distribution. This is the reason why continuations themselves carry the type signature
//
//      ExecutionContext -> contValue -> unit
//
// to avoid capturing local-only state in closures. In other words, this means that
// cloud workflows form a continuation over reader monad.
type internal Body<'T> = 
    abstract Apply : ExecutionContext -> Continuation<'T> -> unit

/// Representation of an MBrace workflow, which, when run 
/// will produce a value of type 'T, or raise an exception.
[<DataContract>]
type Cloud<'T> =
    [<DataMember(Name = "Body")>]
    val mutable private body : Body<'T>
    internal new (body : Body<'T>) = { body = body }
    member internal __.Body = __.body

/// Representation of an in-memory computation, which, when run 
/// will produce a value of type 'T, or raise an exception.
[<Sealed; DataContract>]
type Local<'T> internal (body : Body<'T>) = 
    inherit Cloud<'T>(body)

/// Denotes handle to a distributable resource that can be disposed of.
type ICloudDisposable =
    /// Releases any storage resources used by this object.
    abstract Dispose : unit -> Async<unit>
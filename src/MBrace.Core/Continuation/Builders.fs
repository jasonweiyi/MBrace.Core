namespace MBrace.Core

//  Cloud builder implementation

open System
open MBrace.Core.Internals

#nowarn "444"

[<AutoOpen>]
module internal BuilderImpl =

    // Implementation of expression builder combinators over Body<'T>

    let inline mkCloud body = new Cloud<'T>(body)
    let inline mkLocal body = new Local<'T>(body)

    let inline capture (e : 'exn) = ExceptionDispatchInfo.Capture e
    let inline extract (edi : ExceptionDispatchInfo) = edi.Reify(false, false)
    let inline protect f s = try Choice1Of2 <| f s with e -> Choice2Of2 e
    let inline getMetadata (t : 'T) = t.GetType().FullName
    let inline appendToStacktrace functionName (edi : ExceptionDispatchInfo) =
        let entry = sprintf "   at %s" functionName
        edi.AppendToStackTrace entry

    type Continuation<'T> with
        member inline c.Cancel ctx = c.Cancellation ctx (new System.OperationCanceledException())

        member inline c.Choice (ctx, choice : Choice<'T, exn>) =
            match choice with
            | Choice1Of2 t -> c.Success ctx t
            | Choice2Of2 e -> c.Exception ctx (capture e)

        member inline c.Choice2 (ctx, choice : Choice<#Cloud<'T>, exn>) =
            match choice with
            | Choice1Of2 wf -> wf.Body.Apply ctx c
            | Choice2Of2 e -> c.Exception ctx (capture e)

        member inline c.Choice3 (ctx, choice : Choice<Body<'T>, exn>) =
            match choice with
            | Choice1Of2 f -> f.Apply ctx c
            | Choice2Of2 e -> c.Exception ctx (capture e)

    type ExecutionContext with
        member inline ctx.IsCancellationRequested = ctx.CancellationToken.IsCancellationRequested

    type LambdaBody<'T>(f : ExecutionContext -> Continuation<'T> -> unit) =
        interface Body<'T> with
            member __.Apply ctx cont = if ctx.IsCancellationRequested then cont.Cancel ctx else f ctx cont

    type Return<'T>(t : 'T) =
        interface Body<'T> with
            member __.Apply ctx cont = if ctx.IsCancellationRequested then cont.Cancel ctx else cont.Success ctx t

    type RetFunc<'T>(f : unit -> 'T) =
        interface Body<'T> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else
                match protect f () with
                | Choice1Of2 t -> cont.Success ctx t
                | Choice2Of2 e -> cont.Exception ctx (capture e)

    type Raise<'T>(e : exn) =
        interface Body<'T> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else cont.Exception ctx (capture e)


    type AsyncBody<'T>(asyncWorkflow : Async<'T>) =
        interface Body<'T> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else
                Async.StartWithContinuations(asyncWorkflow, cont.Success ctx, capture >> cont.Exception ctx, cont.Cancellation ctx, ctx.CancellationToken.LocalToken)

    type Delay<'T>(delayed : unit -> Body<'T>) =
        interface Body<'T> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else
                if Trampoline.IsBindThresholdReached() then 
                    Trampoline.QueueWorkItem (fun () -> cont.Choice3(ctx, protect delayed ()))
                else
                    cont.Choice3(ctx, protect delayed ())

    type DelayCloud<'T, 'Cloud when 'Cloud :> Cloud<'T>>(delayed : unit -> 'Cloud) =
        interface Body<'T> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else
                if Trampoline.IsBindThresholdReached() then 
                    Trampoline.QueueWorkItem (fun () -> cont.Choice2(ctx, protect delayed ()))
                else
                    cont.Choice2(ctx, protect delayed ())

    type Bind<'T, 'S>(f : Body<'T>, g : 'T -> Body<'S>) =
        interface Body<'S> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else
                let cont' = {
                    Success = 
                        fun ctx t ->
                            if ctx.IsCancellationRequested then cont.Cancel ctx
                            elif Trampoline.IsBindThresholdReached() then
                                Trampoline.QueueWorkItem(fun () -> cont.Choice3(ctx, protect g t))
                            else
                                cont.Choice3(ctx, protect g t)

                    Exception = 
                        fun ctx e -> 
                            if ctx.IsCancellationRequested then cont.Cancel ctx
                            elif Trampoline.IsBindThresholdReached() then
                                Trampoline.QueueWorkItem(fun () -> cont.Exception ctx e)
                            else
                                cont.Exception ctx e

                    Cancellation = cont.Cancellation
                }

                if Trampoline.IsBindThresholdReached() then 
                    Trampoline.QueueWorkItem (fun () -> f.Apply ctx cont')
                else
                    f.Apply ctx cont'

    type BindCloud<'T, 'S, 'SCloud when 'SCloud :> Cloud<'S>>(f : Body<'T>, g : 'T -> 'SCloud) =
        interface Body<'S> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else
                let cont' = {
                    Success = 
                        fun ctx t ->
                            if ctx.IsCancellationRequested then cont.Cancel ctx
                            elif Trampoline.IsBindThresholdReached() then
                                Trampoline.QueueWorkItem(fun () -> cont.Choice2(ctx, protect g t))
                            else
                                cont.Choice2(ctx, protect g t)

                    Exception = 
                        fun ctx e -> 
                            if ctx.IsCancellationRequested then cont.Cancel ctx
                            elif Trampoline.IsBindThresholdReached() then
                                Trampoline.QueueWorkItem(fun () -> cont.Exception ctx e)
                            else
                                cont.Exception ctx e

                    Cancellation = cont.Cancellation
                }

                if Trampoline.IsBindThresholdReached() then 
                    Trampoline.QueueWorkItem (fun () -> f.Apply ctx cont')
                else
                    f.Apply ctx cont'

    type Combine<'T, 'S>(f : Body<'T>, g : Body<'S>) =
        interface Body<'S> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else
                let cont' = {
                    Success = 
                        fun ctx _ ->
                            if ctx.IsCancellationRequested then cont.Cancel ctx
                            elif Trampoline.IsBindThresholdReached() then
                                Trampoline.QueueWorkItem(fun () -> g.Apply ctx cont)
                            else
                                g.Apply ctx cont

                    Exception = 
                        fun ctx e -> 
                            if ctx.IsCancellationRequested then cont.Cancel ctx
                            elif Trampoline.IsBindThresholdReached() then
                                Trampoline.QueueWorkItem(fun () -> cont.Exception ctx e)
                            else
                                cont.Exception ctx e

                    Cancellation = cont.Cancellation
                }

                if Trampoline.IsBindThresholdReached() then 
                    Trampoline.QueueWorkItem (fun () -> f.Apply ctx cont')
                else
                    f.Apply ctx cont'

    type TryWith<'T, 'TCloud when 'TCloud :> Cloud<'T>>(f : Body<'T>, handler : exn -> 'TCloud) =
        interface Body<'T> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else
                let cont' = {
                    Success = 
                        fun ctx t -> 
                            if ctx.IsCancellationRequested then cont.Cancel ctx
                            elif Trampoline.IsBindThresholdReached() then
                                Trampoline.QueueWorkItem(fun () -> cont.Success ctx t)
                            else
                                cont.Success ctx t
                
                    Exception =
                        fun ctx edi ->
                            if ctx.IsCancellationRequested then cont.Cancel ctx
                            elif Trampoline.IsBindThresholdReached() then
                                Trampoline.QueueWorkItem(fun () -> cont.Choice2(ctx, protect handler (extract edi)))
                            else
                                cont.Choice2(ctx, protect handler (extract edi))

                    Cancellation = cont.Cancellation
                }

                if Trampoline.IsBindThresholdReached() then 
                    Trampoline.QueueWorkItem (fun () -> f.Apply ctx cont')
                else
                    f.Apply ctx cont'

    type TryFinally<'T>(body : Body<'T>, finalizer : Body<unit>) =
        interface Body<'T> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else

                let cont' = {
                    Success =
                        fun ctx t -> 
                            if ctx.IsCancellationRequested then cont.Cancel ctx else
                            let cont' = Continuation.map (fun () -> t) cont
                            if Trampoline.IsBindThresholdReached() then
                                Trampoline.QueueWorkItem(fun () -> finalizer.Apply ctx cont')
                            else
                                finalizer.Apply ctx cont'

                    Exception = 
                        fun ctx edi -> 
                            if ctx.IsCancellationRequested then cont.Cancel ctx else
                            let cont' = Continuation.failwith (fun () -> (extract edi)) cont
                            if Trampoline.IsBindThresholdReached() then
                                Trampoline.QueueWorkItem(fun () -> finalizer.Apply ctx cont')
                            else
                                finalizer.Apply ctx cont'

                    Cancellation = cont.Cancellation
                }

                if Trampoline.IsBindThresholdReached() then 
                    Trampoline.QueueWorkItem (fun () -> body.Apply ctx cont')
                else
                    body.Apply ctx cont'

    // wraps workflow in a nested execution context which can be updated
    // once computation is completed.
    type ContextWrapper<'T>(update : ExecutionContext -> ExecutionContext, revert : ExecutionContext -> ExecutionContext, body : Body<'T>) =
        interface Body<'T> with
            member __.Apply ctx cont =
                if ctx.IsCancellationRequested then cont.Cancel ctx else

                match protect update ctx with
                | Choice1Of2 ctx' -> 
                    // update immediate continuation so that execution context is reverted as soon as provided workflow is completed.
                    let cont' =
                        { 
                            Success = fun ctx t -> match protect revert ctx with Choice1Of2 ctx' -> cont.Success ctx' t | Choice2Of2 e -> cont.Exception ctx (capture e)
                            Exception = fun ctx e -> match protect revert ctx with Choice1Of2 ctx' -> cont.Exception ctx' e | Choice2Of2 e -> cont.Exception ctx (capture e)
                            Cancellation = fun ctx c -> match protect revert ctx with Choice1Of2 ctx' -> cont.Cancellation ctx' c | Choice2Of2 _ -> cont.Cancellation ctx c
                        }

                    body.Apply ctx' cont'
                | Choice2Of2 e -> cont.Exception ctx (capture e)


    let inline ret (t : 'T) = new Return<'T>(t) :> Body<'T>
    let inline retFunc (f : unit -> 'T) = new RetFunc<'T>(f) :> Body<'T>
    let inline ofLambda (f : ExecutionContext -> Continuation<'T> -> unit) = new LambdaBody<'T>(f) :> Body<'T>
    let inline raiseM e : Body<'T> = new Raise<'T>(e) :> Body<'T>
    let inline ofAsync (workflow : Async<'T>) = new AsyncBody<'T>(workflow) :> Body<'T>
    let inline delay (f : unit -> #Cloud<'T>) = new DelayCloud<'T,_>(f) :> Body<'T>
    let inline delay' (f : unit -> Body<'T>) = new Delay<'T>(f) :> Body<'T>
    let inline bind (f : Body<'T>) (cont : 'T -> #Cloud<'S>) = new BindCloud<'T, 'S, _>(f, cont) :> Body<'S>
    let inline bind' (f : Body<'T>) (cont : 'T -> Body<'S>) = new Bind<'T, 'S>(f , cont) :> Body<'S>
    let inline combine (f : Body<'T>) (g : Body<'S>) = new Combine<'T, 'S>(f, g) :> Body<'S>
    let inline tryWith (f : Body<'T>) (cont : exn -> #Cloud<'T>) = new TryWith<'T, _>(f, cont) :> Body<'T>
    let inline tryFinally (f : Body<'T>) (finalizer : Body<unit>) = new TryFinally<'T>(f, finalizer) :> Body<'T>
    let inline dispose (d : ICloudDisposable) = ofAsync (async { return! d.Dispose() })
    let inline withNestedContext (update : ExecutionContext -> ExecutionContext)
                                  (revert : ExecutionContext -> ExecutionContext) 
                                  (body : Body<'T>) : Body<'T> = new ContextWrapper<'T>(update, revert, body) :> Body<'T>

    let zero : Body<unit> = ret ()

    let inline usingIDisposable (t : #IDisposable) (g : #IDisposable -> #Cloud<'S>) : Body<'S> =
        tryFinally (bind (ret t) g) (retFunc t.Dispose)

    let inline usingICloudDisposable (t : #ICloudDisposable) (g : #ICloudDisposable -> #Cloud<'S>) : Body<'S> =
        tryFinally (bind (ret t) g) (dispose t)

    let inline forArray (body : 'T -> #Cloud<unit>) (ts : 'T []) : Body<unit> =
        let rec loop i () =
            if i = ts.Length then zero
            else
                match protect body ts.[i] with
                | Choice1Of2 b -> bind' b.Body (loop (i+1))
                | Choice2Of2 e -> raiseM e

        delay' (loop 0)

    let inline forList (body : 'T -> #Cloud<unit>) (ts : 'T list) : Body<unit> =
        let rec loop ts () =
            match ts with
            | [] -> zero
            | t :: ts ->
                match protect body t with
                | Choice1Of2 b -> bind' b.Body (loop ts)
                | Choice2Of2 e -> raiseM e

        delay' (loop ts)

    let inline forSeq (body : 'T -> #Cloud<unit>) (ts : seq<'T>) : Body<unit> =
        delay' <|
            fun () ->
                let enum = ts.GetEnumerator()
                let rec loop () =
                    if enum.MoveNext() then
                        match protect body enum.Current with
                        | Choice1Of2 b -> bind' b.Body loop
                        | Choice2Of2 e -> raiseM e
                    else
                        ret ()

                tryFinally (loop ()) (retFunc enum.Dispose)

    let inline whileM (pred : unit -> bool) (body : Body<unit>) : Body<unit> =
        let rec loop () =
            match protect pred () with
            | Choice1Of2 true -> bind' body loop
            | Choice1Of2 false -> zero
            | Choice2Of2 e -> raiseM e

        delay' loop

/// A collection of builder implementations for MBrace workflows
[<AutoOpen>]
module Builders =

    /// Cloud workflow expression builder
    type CloudBuilder () =
        let czero : Cloud<unit> = mkCloud zero
        member __.Return (t : 'T) : Cloud<'T> = mkCloud <| ret t
        member __.Zero () : Cloud<unit> = czero
        member __.Delay (f : unit -> Cloud<'T>) : Cloud<'T> = mkCloud <| delay f
        member __.ReturnFrom (c : Cloud<'T>) : Cloud<'T> = c
        member __.ReturnFrom (c : Async<'T>) : Cloud<'T> = mkCloud <| ofAsync c
        member __.Combine(f : Cloud<unit>, g : Cloud<'T>) : Cloud<'T> = mkCloud <| combine f.Body g.Body
        member __.Bind (f : Cloud<'T>, g : 'T -> Cloud<'S>) : Cloud<'S> = mkCloud <| bind f.Body g
        member __.Bind (f : Async<'T>, g : 'T -> Cloud<'S>) : Cloud<'S> = mkCloud <| bind (ofAsync f) g

        member __.Using<'T, 'U when 'T :> ICloudDisposable>(value : 'T, bindF : 'T -> Cloud<'U>) : Cloud<'U> = 
            mkCloud <| usingICloudDisposable value bindF

        member __.TryWith(f : Cloud<'T>, handler : exn -> Cloud<'T>) : Cloud<'T> = mkCloud <| tryWith f.Body handler
        member __.TryFinally(f : Cloud<'T>, finalizer : unit -> unit) : Cloud<'T> = 
            mkCloud <| tryFinally f.Body (retFunc finalizer)

        member __.For(ts : 'T [], body : 'T -> Cloud<unit>) : Cloud<unit> = mkCloud <| forArray body ts
        member __.For(ts : 'T list, body : 'T -> Cloud<unit>) : Cloud<unit> = mkCloud <| forList body ts
        [<CompilerMessage("For loops indexed on IEnumerable not recommended; consider explicitly converting to list or array instead.", 443)>]
        member __.For(ts : seq<'T>, body : 'T -> Cloud<unit>) : Cloud<unit> = 
            match ts with
            | :? ('T []) as ts -> mkCloud <| forArray body ts
            | :? ('T list) as ts -> mkCloud <| forList body ts
            | _ -> mkCloud <| forSeq body ts

        [<CompilerMessage("While loops in distributed computation not recommended; consider using an accumulator pattern instead.", 443)>]
        member __.While(pred : unit -> bool, body : Cloud<unit>) : Cloud<unit> = mkCloud <| whileM pred body.Body

    /// Local workflow expression builder
    type LocalBuilder () =
        let lzero : Local<unit> = mkLocal zero
        member __.Return (t : 'T) : Local<'T> = mkLocal <| ret t
        member __.Zero () : Local<unit> = lzero
        member __.Delay (f : unit -> Local<'T>) : Local<'T> = mkLocal <| delay f
        member __.ReturnFrom (c : Local<'T>) : Local<'T> = c
        member __.ReturnFrom (c : Async<'T>) : Local<'T> = mkLocal (ofAsync c)
        member __.Combine(f : Local<unit>, g : Local<'T>) : Local<'T> = mkLocal <| combine f.Body g.Body
        member __.Bind (f : Local<'T>, g : 'T -> Local<'S>) : Local<'S> = mkLocal <| bind f.Body g
        member __.Bind (f : Async<'T>, g : 'T -> Local<'S>) : Local<'S> = mkLocal <| bind (ofAsync f) g

        member __.Using<'T, 'U, 'p when 'T :> IDisposable>(value : 'T, bindF : 'T -> Local<'U>) : Local<'U> = 
            mkLocal <| usingIDisposable value bindF
        member __.Using<'T, 'U when 'T :> ICloudDisposable>(value : 'T, bindF : 'T -> Local<'U>) : Local<'U> = 
            mkLocal <| usingICloudDisposable value bindF

        member __.TryWith(f : Local<'T>, handler : exn -> Local<'T>) : Local<'T> = mkLocal <| tryWith f.Body handler
        member __.TryFinally(f : Local<'T>, finalizer : unit -> unit) : Local<'T> = 
            mkLocal <| tryFinally f.Body (retFunc finalizer)

        member __.For(ts : 'T [], body : 'T -> Local<unit>) : Local<unit> = mkLocal <| forArray body ts
        member __.For(ts : 'T list, body : 'T -> Local<unit>) : Local<unit> = mkLocal <| forList body ts
        member __.For(ts : seq<'T>, body : 'T -> Local<unit>) : Local<unit> = 
            match ts with
            | :? ('T []) as ts -> mkLocal <| forArray body ts
            | :? ('T list) as ts -> mkLocal <| forList body ts
            | _ -> mkLocal <| forSeq body ts

        member __.While(pred : unit -> bool, body : Local<unit>) : Local<unit> = mkLocal <| whileM pred body.Body


    /// local builder instance
    let local = new LocalBuilder ()

    /// cloud builder instance
    let cloud = new CloudBuilder ()
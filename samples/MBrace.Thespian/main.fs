﻿module internal MBrace.Thespian.Runtime.Main

open System

open Nessos.Thespian
open Nessos.Thespian.Remote.Protocols
open MBrace.Core.Internals
open MBrace.Runtime

let maxConcurrentJobs = 20
let useAppDomainIsolation = true

[<EntryPoint>]
let main (args : string []) =
    try
        let hostname = System.Net.Dns.GetHostName()
        let pid = System.Diagnostics.Process.GetCurrentProcess().Id
        Console.Title <- sprintf "MBrace.Thespian Worker [pid:%d]" pid 

        let logger = new ConsoleLogger()
        logger.Logf LogLevel.Info "Initializing MBrace.Thespian worker instance."
        logger.Logf LogLevel.Info "Hostname: %s" hostname
        logger.Logf LogLevel.Info "Process Id: %d" pid

        do Config.Initialize(populateDirs = true)
        logger.Logf LogLevel.Info "Thespian initialized with address: %s" Config.LocalAddress

        let state = RuntimeState.FromBase64 args.[0]
        logger.Logf LogLevel.Info "Connected to MBrace cluster '%O' at %s. " state.Id state.Address

        let agent =
            Worker.initialize useAppDomainIsolation state logger maxConcurrentJobs 
            |> Async.RunSync
            
        while true do System.Threading.Thread.Sleep 10000
        0

    with e ->
        printfn "Unhandled exception : %O" e
        let _ = System.Console.ReadKey()
        1

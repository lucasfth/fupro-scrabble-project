namespace QWERTY_Quitters

open ScrabbleUtil
open ScrabbleUtil.ServerCommunication

open System.IO

open ScrabbleUtil.DebugPrint

// The RegEx module is only used to parse human input. It is not used for the final product.

module RegEx =
    open System.Text.RegularExpressions

    let (|Regex|_|) pattern input =
        let m = Regex.Match(input, pattern)

        if m.Success then
            Some(List.tail [ for g in m.Groups -> g.Value ])
        else
            None

    let parseMove ts =
        let pattern = @"([-]?[0-9]+[ ])([-]?[0-9]+[ ])([0-9]+)([A-Z]{1})([0-9]+)[ ]?"

        Regex.Matches(ts, pattern)
        |> Seq.cast<Match>
        |> Seq.map (fun t ->
            match t.Value with
            | Regex pattern [ x; y; id; c; p ] -> ((x |> int, y |> int), (id |> uint32, (c |> char, p |> int)))
            | _ -> failwith "Failed (should never happen)")
        |> Seq.toList

module Print =

    let printHand pieces hand =
        hand
        |> MultiSet.fold (fun _ x i -> forcePrint (sprintf "%d -> (%A, %d)\n" x (Map.find x pieces) i)) ()

module State =
    open Trie
    // Make sure to keep your state localised in this module. It makes your life a whole lot easier.
    // Currently, it only keeps track of your hand, your player numer, your board, and your dictionary,
    // but it could, potentially, keep track of other useful
    // information, such as number of players, player turn, etc.

    type state =
        { board: Parser.board
          dict: Dictionary.Dict
          playerNumber: uint32
          hand: MultiSet.MultiSet<uint32> 
          lastPlay: MultiSet.MultiSet<uint32> 
          myTurn: bool
          numberOfPlayers: uint32 }

    let mkState b d pn h n =
        { board = b
          dict = d
          playerNumber = pn
          hand = h
          lastPlay = MultiSet.empty
          myTurn = true 
          numberOfPlayers = n }

    let board st = st.board
    let dict st = st.dict
    let playerNumber st = st.playerNumber
    let hand st = st.hand

module Scrabble =
    open System.Threading
    open MultiSet
    open Trie

    let playGame cstream pieces (st: State.state) =
        
        forcePrint (if Dictionary.lookup "HELLO" st.dict then "HELLO Y" else "HELLO N")
        forcePrint (if Dictionary.lookup "HELL" st.dict then "HELL Y" else "HELL N")
        

        let rec aux (st: State.state) =
            Print.printHand pieces (State.hand st)
            
            // Check if it is our turn
            if st.myTurn then
                // remove the force print when you move on from manual input (or when you have learnt the format)
                forcePrint
                    "Input move (format '(<x-coordinate> <y-coordinate> <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"

                // TODO implement some logic that figures out the next play
                let input = System.Console.ReadLine()
                let move = RegEx.parseMove input

                debugPrint (sprintf "Player %d -> Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.
                send cstream (SMPlay move)

                // I dunno what the below debug line does different from the above one...
                // It used to be below "let msg {...}" but because of the if-statement, 
                // I pulled it into the same scope as "let move {...}" 
                debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

            let msg = recv cstream

            match msg with
            | RCM(CMPlaySuccess(ms, points, newPieces)) ->
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                
                // Hand:
                // Remove the last played pieces from current hand state
                let handWithoutUsedPieces = MultiSet.subtract st.hand st.lastPlay
                // Add new pieces to the hand state
                let newHand = List.fold (fun acc (x, k) -> MultiSet.add x k acc) handWithoutUsedPieces newPieces
                
                let st': State.state = {
                    playerNumber = st.playerNumber
                    board = st.board
                    dict = st.dict
                    hand = newHand
                    lastPlay = st.hand // Maybe wrong
                    myTurn = if st.numberOfPlayers <> 1u then false else true // single player game should continue to be my turn
                    numberOfPlayers = st.numberOfPlayers
                } // This state needs to be updated
                aux st'
            | RCM(CMPlayed(pid, ms, points)) ->
                (* Successful play by other player. Update your state *)
                let st': State.state = {
                    playerNumber = st.playerNumber
                    board = st.board
                    dict = st.dict
                    hand = st.hand
                    lastPlay = MultiSet.empty // Should not matter to keep their last play right now
                    myTurn = if ((pid+1u) % st.numberOfPlayers = st.playerNumber) then true else false
                    numberOfPlayers = st.numberOfPlayers
                }
                    // This state needs to be updated
                aux st'
            | RCM(CMPlayFailed(pid, ms)) ->
                (* Failed play. Update your state *)
                let st' = st // This state needs to be updated
                aux st'
            | RCM(CMGameOver _) -> ()
            | RCM a -> failwith (sprintf "not implmented: %A" a)
            | RGPE err ->
                printfn "Gameplay Error:\n%A" err
                aux st


        aux st

    let startGame
        (boardP: boardProg)
        (dictf: bool -> Dictionary.Dict)
        (numPlayers: uint32)
        (playerNumber: uint32)
        (playerTurn: uint32)
        (hand: (uint32 * uint32) list)
        (tiles: Map<uint32, tile>)
        (timeout: uint32 option)
        (cstream: Stream)
        =
        debugPrint (
            sprintf
                "Starting game!
                      number of players = %d
                      player id = %d
                      player turn = %d
                      hand =  %A
                      timeout = %A\n\n"
                numPlayers
                playerNumber
                playerTurn
                hand
                timeout
        )

        //let dict = dictf true // Uncomment if using a gaddag for your dictionary
        // let dict = dictf false // Uncomment if using a trie for your dictionary
        let dict = dictf false

        let board = Parser.mkBoard boardP

        let handSet = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty hand

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber handSet numPlayers)

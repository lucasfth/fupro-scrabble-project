namespace QWERTY_Quitters

open ScrabbleUtil
open ScrabbleLib
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
    open MultiSet

    let printHand pieces hand =
        hand
        |> MultiSet.fold (fun _ x i -> forcePrint (sprintf "%d -> (%A, %d)\n" x (Map.find x pieces) i)) ()

    let printWordOptions (pieces: Map<uint32, tile>) (options: MultiSet<list<uint32>>) =

        forcePrint "Printing all options:\n"

        MultiSet.fold
            (fun _ opt count ->
                forcePrint "WORD OPTION:\n\n"
                printHand pieces (MultiSet.ofList opt))
            ()
            options

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
          numberOfPlayers: uint32
          anchorPoints : (coord * char) list
          boardProg: (coord -> bool) 
          usedTile: Map<coord, char> }

    let mkState b d pn h n bp map =
        { board = b
          dict = d
          playerNumber = pn
          hand = h
          lastPlay = MultiSet.empty
          myTurn = true
          numberOfPlayers = n 
          anchorPoints = [] 
          boardProg = bp 
          usedTile = map }

    let board st = st.board
    let dict st = st.dict
    let playerNumber st = st.playerNumber
    let hand st = st.hand

module Scrabble =
    open System.Threading
    open MultiSet
    open Trie

    let usedTile coord map =
        let opt = Map.tryFind coord map
        match opt with
        | Some _ -> true
        | None -> false

    let findPlayCoords usedTilesMap ((initialX, initialY), letters) = 
        let rec aux (shouldGoRight : bool) x y (remainingLetters: 'd list) acc =
            if
                List.isEmpty remainingLetters
            then
                acc
            else
                let (nextX, nextY) =
                    if shouldGoRight then (x + 1, y)
                    else (x, y + 1)
                // Tile with coordinates appended on the back of the accumulator
                aux shouldGoRight nextX nextY remainingLetters.Tail (acc @ ([(nextX, nextY), List.head remainingLetters]))

        let reversed = List.rev letters
        
        if usedTile (initialX , initialY) usedTilesMap
        then 
            if usedTile (initialX - 1, initialY) usedTilesMap // Check direction and add one to coordinate
            then aux false initialX (initialY + 1) reversed List.empty // go down
            else aux true (initialX + 1) initialY reversed List.empty // go right
        else aux true initialX initialY reversed List.empty // Base case: First word of the game - go right
        
    let decidePlay words folder pieces
        =
        // Use folder (function) to determine which word is the best
        // pieces will be used if the folder starts requiring to know the characters on the tiles
        match words with
        | (coord, list) -> (coord, MultiSet.foldBack folder list [])

    let rec findPlay
        (hand: MultiSet.MultiSet<uint32>)
        (pieces: Map<uint32, tile>)
        (trie: Dictionary.Dict)
        (coord: coord)
//        (initialTile: char)
        =
        // Use Dictionary.step to go recursively through the trie we have (This uses our implementation of Trie.step)
        // Hand contains a set of integers which we need to use Map.find on the pieces Map to figure out what letter they represent
        // Preferably, we find longer words (this makes it easier to complete a game)
        // To do so, we should step through the Trie and add all results to a list and find the longest word of these and return it
        // Otherwise use some sort of continuation to find a legal word and then continue and if a longer word is found, use this instead
        // We should handle two cases: One where the first letter is pre-determined and one where it is not (if we start the game or not)
        // One way to handle this is to call this method after the step method for the first letter

        let rec aux // This returns a MultiSet of options, where an option is a list of uint32 representing tileIDs for a given word
            (currHand: MultiSet<uint32>)
            (currTrie: Dictionary.Dict)
            (currWord: list<uint32 * char * int>)
            (cont: MultiSet<(uint32 * char * int) list>)
            =
            match (MultiSet.size currHand) with
            | 0u -> cont // Return continuation if no pieces left in hand
            | _ -> // Equivalent to pieces left in hand

                // This iterates over tiles in our hand
                MultiSet.fold
                    (fun subContinuation nextTileId countOfThisLetter ->
                        // For each tile left in our hand: (can be wildcards)
                        let (nextTile: tile) = Map.find nextTileId pieces

                        // This iterates over each possible character value of a tile
                        Set.fold
                            (fun subSubContinuation (nextChar, pointvalue) ->

                                // Step into next trie node
                                let subTrieOption = Dictionary.step nextChar currTrie
                        
                                match subTrieOption with
                                // If the current node of the trie exists, then it is "Some"
                                | Some(isWord, subTrie) ->
                                    let (currWord : list<uint32 * char * int>) = ((nextTileId, nextChar, pointvalue) :: currWord)

                                    let newContinuation =
                                        // if current node is also a word, then add the word to the result list
                                        if isWord then
                                            MultiSet.addSingle currWord subSubContinuation
                                        // if not then do not add the word
                                        else
                                            subSubContinuation

                                    // Union the result of the recursive call (subnode) with the current node
                                    MultiSet.union
                                        (aux
                                            (MultiSet.removeSingle nextTileId currHand)
                                            subTrie
                                            currWord
                                            newContinuation)
                                        subSubContinuation
                                | None -> subSubContinuation)
                            subContinuation // TODO This needs to change
                            nextTile)
                    cont // TODO This need to change
                    currHand

        (coord, aux hand trie [] MultiSet.empty)

    let findPlayFromAnchorPoint
        (anchorpoints: (coord * char) list)
        (hand: MultiSet.MultiSet<uint32>)
        (pieces: Map<uint32, tile>)
        (trie: Dictionary.Dict)
        =
        let rec aux anchorpoints =
            match anchorpoints with
            | [] -> 
                forcePrint "There was not found any legal plays"
                failwith "No legal play found"
            | (coord, char) :: tail -> 
                let initialTrieOption = Dictionary.step char trie

                match initialTrieOption with
                | Some(isWord, subTrie) ->
                    let play = findPlay hand pieces subTrie coord
                    if MultiSet.size (snd play) = 0u
                        then aux tail
                        else play
                | None -> aux tail
        aux anchorpoints


    let playGame cstream pieces (st: State.state) =

        let rec aux (st: State.state) =
            Print.printHand pieces (State.hand st)

            // Check if it is our turn
            if st.myTurn then
                // remove the force print when you move on from manual input (or when you have learnt the format)
                forcePrint
                    "Input move (format '(<x-coordinate> <y-coordinate> <piece id><character><point-value> )*', note the absence of space between the last inputs)\n\n"

                let B: tile = Set.ofList [ ('B', 0) ]
                let A: tile = Set.ofList [ ('A', 0) ]
                let M: tile = Set.ofList [ ('M', 0) ]
                let P: tile = Set.ofList [ ('P', 0) ]
                // AMP
                let debugPieces: Map<uint32, tile> =
                    Map.ofList [ (1u, B); (2u, A); (3u, M); (4u, P) ]

                let debugHand: MultiSet<uint32> = MultiSet.ofList [ 1u; 2u; 3u; 4u ]

                // some logic that figures out the next play
                let nextPlay = 
                    if List.isEmpty st.anchorPoints
                    then findPlay st.hand pieces st.dict (-1, 0) // This is the first play of the game, anchor point needed = hardcode (-1, 0)
                    else
                        findPlayFromAnchorPoint st.anchorPoints st.hand pieces st.dict // Anchor point needed

                // let nextPlay = findPlay (* st.hand *) debugHand (* pieces *) debugPieces st.dict

                // folder function that gives longest element of list
                let folder = (fun element count currentWord -> if (List.length element) > (List.length currentWord) then element else currentWord)

                // call function using folder to determine best play
                let play = decidePlay nextPlay folder pieces

                // find coordinates for play
                
                let playWithCoords = findPlayCoords st.usedTile play

                // Print.printWordOptions pieces nextPlay
                
                forcePrint (sprintf "Wordlength: %A\n" (List.length (snd play)))

                forcePrint (sprintf "Word decided: %A\n" (List.rev (snd play)))

                forcePrint (sprintf "Has char 0,0: %A - 1,1: %A - -1,0: %A  --boardprog\n" (st.boardProg (0, 0)) (st.boardProg (1, 1)) (st.boardProg (-1, 0)))

                forcePrint (sprintf "Used tiles %A\n" playWithCoords)

                // Print.printWordOptions pieces nextPlay

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

                // Assuming ms used first letter as anchorpoint, we ignore the first value
                // let newAnchorPoints =
                //     List.foldBack
                //         (fun el acc ->
                //             (fst el, fst (snd (snd el))) :: acc) // Should take (coord, char) from element and add to anchorPoints
                //         ms
                //         st.anchorPoints
                
                let newAnchorPoints = 
                    List.foldBack 
                        (fun el acc -> 
                            match el with 
                            | (coord, (_, (char, _))) -> (coord, char) :: acc) // Should take (coord, char) from element and add to anchorPoints
                        ms // We don't want to use the first character 
                        st.anchorPoints
                
                let newUsedTiles =
                    List.foldBack
                        (fun el acc ->
                            match el with
                            | (coord, (_, (char, _))) -> Map.add coord char acc )
                        ms
                        st.usedTile

                // Hand:
                // Remove the last played pieces from current hand state
                let handWithoutUsedPieces = MultiSet.subtract st.hand st.lastPlay
                // Add new pieces to the hand state
                let newHand =
                    List.fold (fun acc (x, k) -> MultiSet.add x k acc) handWithoutUsedPieces newPieces

                let st': State.state =
                    { playerNumber = st.playerNumber // doesn't change
                      board = st.board // I don't think this should change
                      dict = st.dict // doesn't change
                      hand = newHand // correct
                      lastPlay = MultiSet.empty // lastPlay is empty on succesful play
                      myTurn = if st.numberOfPlayers <> 1u then false else true // single player game should continue to be my turn
                      numberOfPlayers = st.numberOfPlayers // doesn't change
                      anchorPoints = newAnchorPoints // correct
                      boardProg = st.boardProg
                      usedTile = newUsedTiles } // This state needs to be updated

                aux st'
            | RCM(CMPlayed(pid, ms, points)) ->
                (* Successful play by other player. Update your state *)
                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board
                      dict = st.dict
                      hand = st.hand
                      lastPlay = MultiSet.empty // Should not matter to keep their last play right now
                      myTurn =
                        if ((pid + 1u) % st.numberOfPlayers = st.playerNumber) then
                            true
                        else
                            false
                      numberOfPlayers = st.numberOfPlayers 
                      anchorPoints = st.anchorPoints // Update this with new play
                      boardProg = st.boardProg
                      usedTile = st.usedTile}
                // This state needs to be updated
                aux st'
            | RCM(CMPlayFailed(pid, ms)) ->
                (* Failed play. Update your state *)
                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board
                      dict = st.dict
                      hand = st.hand
                      lastPlay = MultiSet.empty // Should not matter to keep their last play right now
                      myTurn =
                        if ((pid + 1u) % st.numberOfPlayers = st.playerNumber) then
                            true
                        else
                            false
                      numberOfPlayers = st.numberOfPlayers
                      anchorPoints = st.anchorPoints 
                      boardProg = st.boardProg
                      usedTile = st.usedTile }

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

        let boardprog = ScrabbleLib.simpleBoardLangParser.parseSimpleBoardProg boardP

        let handSet = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty hand

        fun () -> playGame cstream tiles (State.mkState board dict playerNumber handSet numPlayers boardprog Map.empty)

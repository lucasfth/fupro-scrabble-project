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
    open StateMonad

    let usedTile coord map =
        let opt = Map.tryFind coord map
        match opt with
        | Some _ -> true
        | None -> false

    let findPlayCoords usedTilesMap ((initialX, initialY), letters) = 
        let rec aux (shouldGoRight : bool) x y (remainingLetters) acc =
            if
                List.isEmpty remainingLetters
            then
                acc
            else
                let (nextX, nextY) =
                    if shouldGoRight then (x + 1, y)
                    else (x, y + 1)
                // Tile with coordinates appended on the back of the accumulator
                aux shouldGoRight nextX nextY remainingLetters.Tail (acc @ ([(nextX, nextY), (List.head remainingLetters)]))

        let reversed = List.rev letters
        
        if usedTile (initialX , initialY) usedTilesMap
        then 
            if usedTile (initialX - 1, initialY) usedTilesMap // Check direction and add one to coordinate
            then 
                // forcePrint "trying to go down"
                aux false initialX (initialY) reversed List.empty // go down
            else 
                // forcePrint "trying to go right"
                aux true (initialX) initialY reversed List.empty // go right
        else aux true initialX initialY reversed List.empty // Base case: First word of the game - go right
        
    let decidePlay words folder pieces
        =
        // Use folder (function) to determine which word is the best
        // pieces will be used if the folder starts requiring to know the characters on the tiles
        MultiSet.foldBack folder words []

    let rec findPlay
        (hand: MultiSet.MultiSet<uint32>)
        (pieces: Map<uint32, tile>)
        (trie: Dictionary.Dict)
        (coord: coord)
        folder
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
            (currWord: list<uint32 * (char * int)>)
            (cont: MultiSet<(uint32 * (char * int)) list>)
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
                                    let (currWord) = ((nextTileId, (nextChar, pointvalue)) :: currWord)

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
        let possibleWords = aux hand trie [] MultiSet.empty

        (coord, decidePlay possibleWords folder pieces)

    let shouldBuildRight (x, y) usedTilesMap =
       if usedTile (x - 1, y) usedTilesMap // Check direction and add one to coordinate
            then 
                false // go down
            else 
                true // go right 

    let rec maxLengthOfWord currentTiles (x, y) wordLength isBuildingRight
        =
        let isIllegalPlay (x, y) =
            usedTile (x, y) currentTiles || // check current
            usedTile (x+1, y) currentTiles || // check right
            usedTile (x, y+1) currentTiles || // check down
            if isBuildingRight
                then usedTile (x, y-1) currentTiles // check up
                else usedTile (x-1, y) currentTiles // check left
        if wordLength > 8 // don't continue further than 9 letter words
            then wordLength
            else if
                (if isBuildingRight
                    then isIllegalPlay (x+1, y)
                    else isIllegalPlay (x, y+1))
                then wordLength
                else if isBuildingRight 
                    then maxLengthOfWord currentTiles (x+1, y) (wordLength+1) isBuildingRight // continue right
                    else maxLengthOfWord currentTiles (x, y+1) (wordLength+1) isBuildingRight  // continue down
                

    let findPlayFromAnchorPoint
        (anchorpoints: (coord * char) list)
        (hand: MultiSet.MultiSet<uint32>)
        (pieces: Map<uint32, tile>)
        (trie: Dictionary.Dict)
        (usedTiles: Map<coord,char>) =
        let rec aux anchorpoints =
            match anchorpoints with
            | [] -> 
                forcePrint "There was not found any legal plays"
                ((0, 0), [])
            | (coord, char) :: tail -> 
            
                let maxLengthOfWord = 
                    shouldBuildRight coord usedTiles |> maxLengthOfWord usedTiles coord 0
                
                let folder = (fun element count currentBestWord -> 
                    if (List.length element) > (List.length currentBestWord) && 
                       (List.length element <= maxLengthOfWord)
                    then element 
                    else currentBestWord)

                let initialTrieOption = Dictionary.step char trie

                match initialTrieOption with
                | Some(isWord, subTrie) ->
                    let play = findPlay hand pieces subTrie coord folder
                    if List.length (snd play) = 0
                        then aux tail
                        else play
                | None -> aux tail
        aux anchorpoints


    let playGame cstream pieces (st: State.state) =

        let rec aux (st: State.state) =
            Print.printHand pieces (State.hand st)

            // Check if it is our turn
            if st.myTurn then

                let B: tile = Set.ofList [ ('B', 0) ]
                let A: tile = Set.ofList [ ('A', 0) ]
                let M: tile = Set.ofList [ ('M', 0) ]
                let P: tile = Set.ofList [ ('P', 0) ]
                // AMP
                let debugPieces: Map<uint32, tile> =
                    Map.ofList [ (1u, B); (2u, A); (3u, M); (4u, P) ]

                let debugHand: MultiSet<uint32> = MultiSet.ofList [ 1u; 2u; 3u; 4u ]

                // some logic that figures out the next play
                let findLongestWord = (fun element count currentBestWord -> 
                    if (List.length element) > (List.length currentBestWord)
                    then element 
                    else currentBestWord)

                let play = 
                    if List.isEmpty st.anchorPoints
                    then findPlay st.hand pieces st.dict (-1, 0) findLongestWord // This is the first play of the game, anchor point needed = hardcode (-1, 0)
                    else
                        findPlayFromAnchorPoint st.anchorPoints st.hand pieces st.dict st.usedTile // Anchor point needed

                if List.isEmpty (snd play)
                    then
                        forcePrint "Changing hands...\n"
                        send cstream (SMChange (MultiSet.toList st.hand)) // Change whole hand
                        forcePrint "Changed hands...\n"
                    else                    
                        let playWithCoords = findPlayCoords st.usedTile play
                        send cstream (SMPlay playWithCoords)


                // I dunno what the below debug line does different from the above one...
                // It used to be below "let msg {...}" but because of the if-statement,
                // I pulled it into the same scope as "let move {...}"
                // debugPrint (sprintf "Player %d <- Server:\n%A\n" (State.playerNumber st) move) // keep the debug lines. They are useful.

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
                
                let newAnchorPoints2 = 
                    List.foldBack 
                        (fun el acc -> 
                            match el with 
                            | (coord, (_, (char, _))) -> (coord, char) :: acc) // Should take (coord, char) from element and add to anchorPoints
                        ms // We don't want to use the first character 
                        st.anchorPoints

                let newAnchorPoints =
                    List.fold
                        (fun acc (coord, (_, (char, _))) -> (coord, char) :: acc)
                        st.anchorPoints
                        ms.Tail
                
                let newUsedTiles =
                    List.foldBack
                        (fun el acc ->
                            match el with
                            | (coord, (_, (char, _))) -> 
                                forcePrint (sprintf "USED TILE: %A\n" coord)
                                Map.add coord char acc )
                        ms
                        st.usedTile

                // Hand:
                let usedIds = 
                    List.foldBack (fun (_, (tileId, _)) acc -> MultiSet.addSingle tileId acc)
                        ms
                        MultiSet.empty

                // Remove the last played pieces from current hand state
                let handWithoutUsedPieces = MultiSet.subtract st.hand usedIds

                // Add new pieces to the hand state
                // let newHand2 =
                //     List.fold (fun acc (x, k) -> MultiSet.add x k acc) handWithoutUsedPieces newPieces
                
                // forcePrint (sprintf "newPieces: %A\n" newPieces)

                let newHand =
                    List.fold (fun acc (_, (char, _)) -> MultiSet.removeSingle char acc) st.hand ms
                    |> List.foldBack (fun (x, cnt) acc -> MultiSet.add x cnt acc) newPieces

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
            | RCM(CMChangeSuccess newPieces) ->
                let newHand = List.foldBack (fun (x, cnt) acc -> MultiSet.add x cnt acc) newPieces MultiSet.empty
                // Assume whole hand is changed
                let st': State.state = {
                    playerNumber = st.playerNumber
                    board = st.board
                    dict = st.dict
                    hand = newHand
                    lastPlay = MultiSet.empty // Should not matter to keep their last play right now
                    myTurn = if st.numberOfPlayers <> 1u then false else true // single player game should continue to be my turn
                    numberOfPlayers = st.numberOfPlayers
                    anchorPoints = st.anchorPoints 
                    boardProg = st.boardProg
                    usedTile = st.usedTile 
                }

                aux st'
            | RCM(CMPlayFailed(pid, ms)) ->
                (* Failed play. Update your state *)
                send cstream (SMForfeit) // TODO: Remove
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
            // | RGPE(GPENotEnoughPieces) ->
            //     send cstream SMPass
            //     send cstream SMPass
            //     send cstream SMPass
            | RGPE err ->
                match List.head err with
                | GPENotEnoughPieces (_, piecesLeft) -> 
                    forcePrint "\n\nPrinting remaining hand:\n"
                    Print.printHand pieces st.hand
                    forcePrint "-----------------\n"

                    send cstream SMPass
                    send cstream SMPass
                    send cstream SMPass
                | err -> 
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

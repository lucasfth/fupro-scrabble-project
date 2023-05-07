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
    let printHand pieces hand =
        hand
        |> MultiSet.fold (fun _ x i -> debugPrint (sprintf "%d -> (%A, %d)\n" x (Map.find x pieces) i)) ()

module State =
    // Make sure to keep your state localised in this module. It makes your life a whole lot easier.

    type state =
        { board: Parser.board
          dict: Dictionary.Dict
          playerNumber: uint32
          hand: MultiSet.MultiSet<uint32>
          myTurn: bool
          numberOfPlayers: uint32
          remainingPlayers: uint32 list
          anchorPoints: (coord * char) list
          usedTile: Map<coord, char> }

    let mkState b d pn h n map isMyTurn initPlayerList =
        { board = b
          dict = d
          playerNumber = pn
          hand = h
          myTurn = isMyTurn
          numberOfPlayers = n
          remainingPlayers = initPlayerList
          anchorPoints = []
          usedTile = map }

    let calculateNewAnchorPoints oldAnchorPoints moves =
        List.fold (fun acc (coord, (_, (char, _))) -> (coord, char) :: acc) oldAnchorPoints moves

    let calculateNewUsedTiles oldUsedTiles moves =
        List.foldBack
            (fun el acc ->
                match el with
                | (coord, (_, (char, _))) -> Map.add coord char acc)
            moves
            oldUsedTiles


    let board st = st.board
    let dict st = st.dict
    let playerNumber st = st.playerNumber
    let hand st = st.hand

module Scrabble =
    open MultiSet
    open System.Collections.Generic

    let shouldPlay pid remainingplayers ownplayernumber =
        // Find index of pid
        // Find pid of index+1
        // Compare pid of index+1 with own playernumber
        // Also make sure to handle if pid = last remaining player
        let index = List.findIndex (fun x -> x = pid) remainingplayers

        let temp = List.length remainingplayers

        let temp2 = uint32 temp

        let nextPlayer =
            List.item (((index + 1) % List.length remainingplayers)) remainingplayers

        nextPlayer = ownplayernumber

    let usedTile coord map =
        let opt = Map.tryFind coord map

        match opt with
        | Some _ -> true
        | None -> false

    let findPlayCoords usedTilesMap (isBuildingRight, ((initialX, initialY), letters)) =
        let rec aux (shouldGoRight: bool) x y (remainingLetters) acc =
            if List.isEmpty remainingLetters then
                acc
            else
                let (nextX, nextY) = if shouldGoRight then (x + 1, y) else (x, y + 1)
                // Tile with coordinates appended on the back of the accumulator
                aux
                    shouldGoRight
                    nextX
                    nextY
                    remainingLetters.Tail
                    (acc @ ([ (nextX, nextY), (List.head remainingLetters) ]))

        let reversed = List.rev letters

        aux isBuildingRight initialX initialY reversed List.empty

    let decidePlay words folder _ =
        // Use folder (function) to determine which word is the best
        // pieces will be used if the folder starts requiring to know the characters on the tiles
        MultiSet.foldBack folder words []

    let rec findPlay
        (hand: MultiSet.MultiSet<uint32>)
        (pieces: Map<uint32, tile>)
        (trie: Dictionary.Dict)
        (coord: coord)
        folder
        =
        // Use Dictionary.step to go recursively through the trie we have (This uses our implementation of Trie.step)
        // Hand contains a set of integers which we need to use Map.find on the pieces Map to figure out what letter they represent
        // Preferably, we find longer words (this makes it easier to complete a game)
        // To do so, we should step through the Trie and add all results to a list and find the longest word of these and return it

        let rec aux // This returns a MultiSet of options, where an option is a list of uint32 representing tileIDs for a given word
            (currHand: MultiSet<uint32>)
            (currTrie: Dictionary.Dict)
            (currWord: list<uint32 * (char * int)>)
            (cont: MultiSet<(uint32 * (char * int)) list>)
            =
            match (size currHand) with
            | 0u -> cont // Return continuation if no pieces left in hand
            | _ -> // Equivalent to pieces left in hand

                // This iterates over tiles in our hand
                fold
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

        let possibleWords = aux hand trie [] empty

        (coord, decidePlay possibleWords folder pieces)

    let rec maxLengthOfWord currentTiles (x, y) wordLength isBuildingRight =
        let isIllegalPlay (x, y) =
            usedTile (x, y) currentTiles
            || // check current
            usedTile (x + 1, y) currentTiles
            || usedTile // check right
                (x, y + 1)
                currentTiles
            || if // check down
                   isBuildingRight
               then
                   usedTile (x, y - 1) currentTiles // check up
               else
                   usedTile (x - 1, y) currentTiles // check left

        if
            wordLength > 8 // don't continue further than 9 letter words
        then
            wordLength
        else if
            (if isBuildingRight then
                 isIllegalPlay (x + 1, y)
             else
                 isIllegalPlay (x, y + 1))
        then
            wordLength
        else if isBuildingRight then
            maxLengthOfWord currentTiles (x + 1, y) (wordLength + 1) isBuildingRight // continue right
        else
            maxLengthOfWord currentTiles (x, y + 1) (wordLength + 1) isBuildingRight // continue down

    let rec findPrefix (usedTiles: Map<coord, char>) ((x, y): coord) (isBuildingRight: bool) cont =
        let prefix = Map.tryFind (x, y) usedTiles

        match prefix with
        | Some char ->
            findPrefix usedTiles (if isBuildingRight then (x - 1, y) else (x, y - 1)) isBuildingRight (char :: cont)
        | None -> cont

    let findPlayFromAnchorPoint
        (anchorpoints: (coord * char) list)
        (hand: MultiSet.MultiSet<uint32>)
        (pieces: Map<uint32, tile>)
        (trie: Dictionary.Dict)
        (usedTiles: Map<coord, char>)
        =
        let rec aux anchorpoints =
            match anchorpoints with
            | [] ->
                // There was not found any legal plays. This will cause our Bot to request changing tiles.
                (false, ((0, 0), []))
            | (coord, char) :: tail ->
                let maxLengthOfWordRight = maxLengthOfWord usedTiles coord 0 true
                let maxLengthOfWordDown = maxLengthOfWord usedTiles coord 0 false

                let maxLengthOfWord =
                    if maxLengthOfWordRight > maxLengthOfWordDown then
                        (true, maxLengthOfWordRight)
                    else
                        (false, maxLengthOfWordDown)

                let folder =
                    (fun element _ currentBestWord ->
                        if
                            (List.length element) > (List.length currentBestWord)
                            && (List.length element <= snd maxLengthOfWord)
                        then
                            element
                        else
                            currentBestWord)

                let prefix = findPrefix usedTiles coord (fst maxLengthOfWord) []

                let initialTrieOption = Dictionary.step prefix.Head trie

                let initialTrie =
                    List.fold
                        (fun subtrieOption ch ->
                            match subtrieOption with
                            | Some(_, subtrie) -> Dictionary.step ch subtrie
                            | None -> None)
                        initialTrieOption
                        prefix.Tail

                match initialTrie with
                | Some(isWord, trie) ->
                    let play = findPlay hand pieces trie coord folder
                    let bool = fst maxLengthOfWord

                    if List.length (snd play) = 0 then
                        aux tail
                    else
                        (bool, play)
                | None -> aux tail

        aux anchorpoints


    let playGame cstream pieces (st: State.state) =

        let rec aux (st: State.state) =
            Print.printHand pieces (State.hand st)

            // Check if it is our turn
            if st.myTurn then
                // some logic that figures out the next play
                let findLongestWord =
                    (fun element _ currentBestWord ->
                        if (List.length element) > (List.length currentBestWord) then
                            element
                        else
                            currentBestWord)

                let play =
                    if List.isEmpty st.anchorPoints then
                        (true, findPlay st.hand pieces st.dict (-1, 0) findLongestWord) // This is the first play of the game, anchor point needed = hardcode (-1, 0)
                    else
                        findPlayFromAnchorPoint st.anchorPoints st.hand pieces st.dict st.usedTile // Anchor point needed

                if List.isEmpty (snd (snd play)) then
                    send cstream (SMChange(MultiSet.toList st.hand)) // Change whole hand
                else
                    let playWithCoords = findPlayCoords st.usedTile play
                    send cstream (SMPlay playWithCoords)

            let msg = recv cstream

            match msg with
            | RCM(CMPlaySuccess(ms, points, newPieces)) ->
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                // Hand:
                let usedIds =
                    List.foldBack (fun (_, (tileId, _)) acc -> MultiSet.addSingle tileId acc) ms MultiSet.empty

                // Remove the last played pieces from current hand state
                let handWithoutUsedPieces = MultiSet.subtract st.hand usedIds

                let newHand =
                    List.fold (fun acc (_, (char, _)) -> MultiSet.removeSingle char acc) st.hand ms
                    |> List.foldBack (fun (x, cnt) acc -> MultiSet.add x cnt acc) newPieces

                let st': State.state =
                    { playerNumber = st.playerNumber // doesn't change
                      board = st.board // I don't think this should change
                      dict = st.dict // doesn't change
                      hand = newHand // correct
                      myTurn = shouldPlay st.playerNumber st.remainingPlayers st.playerNumber
                      numberOfPlayers = st.numberOfPlayers // doesn't change
                      remainingPlayers = st.remainingPlayers // doesn't change
                      anchorPoints = State.calculateNewAnchorPoints st.anchorPoints ms // correct
                      usedTile = State.calculateNewUsedTiles st.usedTile ms } // This state needs to be updated

                aux st'
            | RCM(CMPlayed(pid, ms, points)) ->
                (* Successful play by other player. Update your state *)

                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board // do not update
                      dict = st.dict // do not update
                      hand = st.hand // do not update
                      myTurn = shouldPlay pid st.remainingPlayers st.playerNumber
                      numberOfPlayers = st.numberOfPlayers
                      remainingPlayers = st.remainingPlayers
                      anchorPoints = State.calculateNewAnchorPoints st.anchorPoints ms // Update this with new play
                      usedTile = State.calculateNewUsedTiles st.usedTile ms // Do update
                    }

                aux st'
            | RCM(CMChangeSuccess newPieces) ->
                let newHand =
                    List.foldBack (fun (x, cnt) acc -> MultiSet.add x cnt acc) newPieces MultiSet.empty
                // Assume whole hand is changed
                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board
                      dict = st.dict
                      hand = newHand
                      myTurn = shouldPlay st.playerNumber st.remainingPlayers st.playerNumber
                      numberOfPlayers = st.numberOfPlayers
                      remainingPlayers = st.remainingPlayers
                      anchorPoints = st.anchorPoints
                      usedTile = st.usedTile }

                aux st'
            | RCM(CMPlayFailed(pid, _)) ->
                (* Failed play. Update your state *)
                send cstream (SMForfeit) // TODO: Remove

                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board
                      dict = st.dict
                      hand = st.hand
                      myTurn = shouldPlay pid st.remainingPlayers st.playerNumber
                      numberOfPlayers = st.numberOfPlayers
                      remainingPlayers = st.remainingPlayers
                      anchorPoints = st.anchorPoints
                      usedTile = st.usedTile }

                aux st'
            | RCM(CMGameOver _) -> ()
            | RCM(CMForfeit(pid)) ->
                // When a player has forfeitted they should be removed from remainingPlayers list
                let index = List.findIndex (fun x -> x = pid) st.remainingPlayers
                let remainingPlayers = List.removeAt index st.remainingPlayers

                forcePrint (sprintf "Player %d has forfeitted\n" pid)

                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board
                      dict = st.dict
                      hand = st.hand
                      myTurn = shouldPlay pid st.remainingPlayers st.playerNumber
                      numberOfPlayers = st.numberOfPlayers
                      remainingPlayers = remainingPlayers
                      anchorPoints = st.anchorPoints
                      usedTile = st.usedTile }

                aux st'
            | RCM(CMPassed(pid)) ->

                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board
                      dict = st.dict
                      hand = st.hand
                      myTurn = shouldPlay pid st.remainingPlayers st.playerNumber
                      numberOfPlayers = st.numberOfPlayers
                      remainingPlayers = st.remainingPlayers
                      anchorPoints = st.anchorPoints
                      usedTile = st.usedTile }

                aux st'

            | RCM a ->
                failwith (
                    sprintf
                        "not implemented: %A for PID: %A who played in order %A"
                        a
                        st.playerNumber
                        st.remainingPlayers
                )
            | RGPE err ->
                match List.head err with
                | GPENotEnoughPieces(_, piecesLeft) ->
                    debugPrint "\n\nPrinting remaining hand:\n"
                    Print.printHand pieces st.hand

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
        let dict = dictf false // Uncomment if using a trie for your dictionary

        let board = Parser.mkBoard boardP

        let handSet = List.fold (fun acc (x, k) -> MultiSet.add x k acc) MultiSet.empty hand

        let isMyTurn = playerNumber = playerTurn

        let initPlayerList = [ 1u .. numPlayers ]

        fun () ->
            playGame
                cstream
                tiles
                (State.mkState board dict playerNumber handSet numPlayers Map.empty isMyTurn initPlayerList)

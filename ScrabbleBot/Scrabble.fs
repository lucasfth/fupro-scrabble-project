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
          remainingPlayers: uint32 list
          anchorPoints: (coord * char) list
          usedTile: Map<coord, char>
          tilesRemaining: int }

    let mkState b d pn h map isMyTurn initPlayerList k =
        { board = b
          dict = d
          playerNumber = pn
          hand = h
          myTurn = isMyTurn
          remainingPlayers = initPlayerList
          anchorPoints = []
          usedTile = map
          tilesRemaining = k }

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

    let findPlayCoords _ (isBuildingRight, ((initialX, initialY), letters)) =
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
                    (fun subContinuation nextTileId _ ->
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
                                    union
                                        (aux (removeSingle nextTileId currHand) subTrie currWord newContinuation)
                                        subSubContinuation
                                | None -> subSubContinuation)
                            subContinuation // TODO This needs to change
                            nextTile)
                    cont // TODO This need to change
                    currHand

        let possibleWords = aux hand trie [] empty

        // AKA decidePlay ⬇️
        (coord, snd (foldBack folder possibleWords (0, [])))

    // bestPlayFolder erstatter longestWordFolder som vi giver med i findplay funktionen
    //Men der den korrekt? ved ikke om det jeg har skrevet giver mening
    //ved ikke om det jeg hatr skrevet giver mening tho
    // folderen skal helst gives med i play game (vores aux funktion også kaldet main function)
    //Skal den så ikke være udenfor findplay sorry. Den skal vel også bruges i findPlayFromAnchorPoint
    // udenfor decideplay? Vi bruger ikke længere decideplay decideplay koden er blevet hevet ind i findPlay. Altså er koden under kommentaren med decidePlay
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
        let rec aux anchorpoints acc =
            match anchorpoints with
            | [] ->
                // There was not found any legal plays. This will cause our Bot to request changing tiles.
                acc
            // [ (false, ((0, 0), ([]))) ]
            | (coord, _) :: tail ->
                let maxLengthOfWordRight = maxLengthOfWord usedTiles coord 0 true
                let maxLengthOfWordDown = maxLengthOfWord usedTiles coord 0 false

                let maxLengthOfWord =
                    if maxLengthOfWordRight > maxLengthOfWordDown then
                        (true, maxLengthOfWordRight)
                    else
                        (false, maxLengthOfWordDown)

                // Similar to find best play folder but also takes maxlengthofword into account
                let folder =
                    (fun (el) _ (currentbestvalue, currentBestWord) ->
                        let pointvaluefromelement =
                            List.fold (fun totalpointvalue (id, (char, pv)) -> totalpointvalue + pv) 0 el

                        if
                            pointvaluefromelement > currentbestvalue
                            && List.length el < (snd maxLengthOfWord)
                        then
                            (pointvaluefromelement, el)
                        else
                            (currentbestvalue, currentBestWord))

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
                | Some(_, trie) ->
                    let play = findPlay hand pieces trie coord folder
                    let shouldPlayRight = fst maxLengthOfWord

                    if List.length (snd play) = 0 then
                        aux tail acc
                    else
                        aux tail ((shouldPlayRight, (fst play, snd play)) :: acc)
                | None -> aux tail acc

        let bestPlayFromEachAnchorpoint: (bool * (coord * (uint32 * (char * int)) list)) list =
            aux anchorpoints []

        let ourFolder =
            (fun el (currentBestValue, currentBestWord) ->

                let pointValueFromElement =
                    List.fold (fun totalpointvalue (_, (_, pv)) -> totalpointvalue + pv) 0 (snd (snd el))

                if pointValueFromElement > currentBestValue then
                    (pointValueFromElement, el)
                else
                    (currentBestValue, currentBestWord))

        snd (List.foldBack ourFolder bestPlayFromEachAnchorpoint (0, (false, ((0, 0), ([])))))

    let playGame cstream pieces (st: State.state) =
        let rec aux (st: State.state) =

            // Check if it is our turn
            if st.myTurn then
                // some logic that figures out the next play

                let findBestWordFolder =
                    (fun (el) _ (currentbestvalue, currentBestWord) ->
                        let pointvaluefromelement =
                            List.fold (fun totalpointvalue (_, (_, pv)) -> totalpointvalue + pv) 0 el

                        if pointvaluefromelement > currentbestvalue then
                            (pointvaluefromelement, el)
                        else
                            (currentbestvalue, currentBestWord))

                let play =
                    if List.isEmpty st.anchorPoints then
                        (true, findPlay st.hand pieces st.dict (-1, 0) findBestWordFolder) // This is the first play of the game, anchor point needed = hardcode (-1, 0)
                    else
                        findPlayFromAnchorPoint st.anchorPoints st.hand pieces st.dict st.usedTile // Anchor point needed

                if List.isEmpty (snd (snd play)) then
                    if size st.hand > (uint32 st.tilesRemaining) then
                        let rec aux lst =
                            match lst with
                            | lst when List.length lst <= st.tilesRemaining -> lst
                            | _ :: tail -> aux tail
                            | [] -> []

                        let changeList = aux (toList st.hand)

                        if List.length changeList = 0 then
                            send cstream (SMPass)
                        else
                            send cstream (SMChange(aux (toList st.hand)))
                    else
                        send cstream (SMChange(toList st.hand)) // Change whole hand
                else
                    let playWithCoords = findPlayCoords st.usedTile play
                    send cstream (SMPlay playWithCoords)

            let msg = recv cstream

            match msg with
            | RCM(CMPlaySuccess(ms, points, newPieces)) ->
                (* Successful play by you. Update your state (remove old tiles, add the new ones, change turn, etc) *)
                // Hand:
                let usedIds =
                    List.foldBack (fun (_, (tileId, _)) acc -> addSingle tileId acc) ms empty

                // Remove the last played pieces from current hand state
                let handWithoutUsedPieces = subtract st.hand usedIds

                let newHand =
                    List.fold (fun acc (_, (char, _)) -> removeSingle char acc) st.hand ms
                    |> List.foldBack (fun (x, cnt) acc -> add x cnt acc) newPieces

                let st': State.state =
                    { playerNumber = st.playerNumber // doesn't change
                      board = st.board // I don't think this should change
                      dict = st.dict // doesn't change
                      hand = newHand // correct
                      myTurn = shouldPlay st.playerNumber st.remainingPlayers st.playerNumber
                      remainingPlayers = st.remainingPlayers // doesn't change
                      anchorPoints = State.calculateNewAnchorPoints st.anchorPoints ms // correct
                      usedTile = State.calculateNewUsedTiles st.usedTile ms
                      tilesRemaining = st.tilesRemaining - (List.length newPieces) } // This state needs to be updated

                aux st'
            | RCM(CMPlayed(pid, ms, _)) ->
                (* Successful play by other player. Update your state *)

                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board // do not update
                      dict = st.dict // do not update
                      hand = st.hand // do not update
                      myTurn = shouldPlay pid st.remainingPlayers st.playerNumber
                      remainingPlayers = st.remainingPlayers
                      anchorPoints = State.calculateNewAnchorPoints st.anchorPoints ms // Update this with new play
                      usedTile = State.calculateNewUsedTiles st.usedTile ms // Do update
                      tilesRemaining =
                        st.tilesRemaining
                        - (if st.tilesRemaining < List.length ms then
                               st.tilesRemaining
                           else
                               List.length ms) }

                aux st'
            | RCM(CMChangeSuccess newPieces) ->
                let newHand = List.foldBack (fun (x, cnt) acc -> add x cnt acc) newPieces empty

                forcePrint (
                    sprintf
                        "Succesfully changed %A pieces\n"
                        (List.foldBack (fun (_, cnt) acc -> acc + cnt) newPieces 0u)
                )
                // Assume whole hand is changed
                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board
                      dict = st.dict
                      hand = newHand
                      myTurn = shouldPlay st.playerNumber st.remainingPlayers st.playerNumber
                      remainingPlayers = st.remainingPlayers
                      anchorPoints = st.anchorPoints
                      usedTile = st.usedTile
                      tilesRemaining = st.tilesRemaining }

                aux st'
            | RCM(CMGameOver _) -> ()
            | RCM(CMForfeit(pid)) ->
                // When a player has forfeitted they should be removed from remainingPlayers list
                let index = List.findIndex (fun x -> x = pid) st.remainingPlayers
                let remainingPlayers = List.removeAt index st.remainingPlayers

                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board
                      dict = st.dict
                      hand = st.hand
                      myTurn = shouldPlay pid st.remainingPlayers st.playerNumber
                      remainingPlayers = remainingPlayers
                      anchorPoints = st.anchorPoints
                      usedTile = st.usedTile
                      tilesRemaining = st.tilesRemaining }

                aux st'
            | RCM(CMPlayFailed(pid, _))
            | RCM(CMPassed(pid))
            | RCM(CMChange(pid, _)) ->

                let st': State.state =
                    { playerNumber = st.playerNumber
                      board = st.board
                      dict = st.dict
                      hand = st.hand
                      myTurn = shouldPlay pid st.remainingPlayers st.playerNumber
                      remainingPlayers = st.remainingPlayers
                      anchorPoints = st.anchorPoints
                      usedTile = st.usedTile
                      tilesRemaining = st.tilesRemaining }

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
                | GPENotEnoughPieces(_, _) ->
                    debugPrint "\n\nPrinting remaining hand:\n"
                    Print.printHand pieces st.hand
                    aux st

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

        let numTiles = 104u - (7u * numPlayers)
        let temp: Parser.square = (board.defaultSquare)

        fun () ->
            playGame
                cstream
                tiles
                (State.mkState board dict playerNumber handSet Map.empty isMyTurn initPlayerList (int numTiles))

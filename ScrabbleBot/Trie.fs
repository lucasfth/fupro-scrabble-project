module internal Trie

type Trie = 
| Data of bool * Map<char, Trie>

let empty = Data (false, Map.empty)

let insert (word : string) (root : Trie) = 
    let rec aux (subword : List<char>) currentNode = 
        match currentNode with
        | Data (isWord, nodeList) -> 
            match subword with
            | fstChar :: remaining ->
                // Insert fstChar in map if existing
                let charExists = Map.tryFind fstChar nodeList
                match charExists with
                | Some (child) ->
                    Data (isWord, Map.add fstChar (aux remaining child) nodeList)
                | None -> 
                    // Create child and then step into it
                    let child = 
                        Map.add fstChar empty nodeList |> 
                        Map.find fstChar
                    
                    Data (isWord, Map.add fstChar (aux remaining child) nodeList)
                    // Call aux on subnode
            | [] -> Data (true, nodeList) // Set to true and create a leaf

    aux (Seq.toList word) root

let trie = insert "Hello" empty |> insert "Hi" |> insert "Hell"

let step c dict : (bool * Trie) =
    match dict with
    | Data (isWord, nodes) -> 
        let trie = Map.tryFind c nodes
        match trie with
        | Some (Data (d, a)) -> (d, Data (d, a))
        | None -> (false, empty)

let mkDict (words : string seq) =
    Seq.fold (fun dict word -> insert word dict) empty words

let lookup w d =
    let rec aux word dict =
        match word with
        | fstChar :: [] -> (fst (step fstChar dict))
        | fstChar :: remaining -> aux remaining (snd (step fstChar dict))
        | [] -> failwith "Something went wrong"
    aux (Seq.toList w) d

let reverse d (b, dict) = failwith "Not implemented"

let isGaddag = fun _ -> false

// Nyt link
// https://github.com/mrandri19/trie-fsharp/blob/master/simpleTrie/trie.fsx 
// https://codereview.stackexchange.com/questions/146150/functional-immutable-trie-prefix-tree 

// dictAPI:
// empty: () -> Trie (check)
// insert: string -> Trie -> Trie (check)
// step: char -> Dict -> (bool * Dict) option (bool=true if word exist and then a dictionary for the next level)
// reverse: GADDAG only

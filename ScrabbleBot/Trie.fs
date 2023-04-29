module internal Trie

type Trie = 
| Data of bool * Map<char, Trie>

let empty = Data (false, Map.empty)

let insert (root : Trie) (word : string) = 
    let rec aux currentNode (subword : List<char>) = 
        match currentNode with
        | Data (isWord, nodeList) -> 
            match subword with
            | fstChar :: remaining ->
                // Insert fstChar in map if existing
                let charExists = Map.tryFind fstChar nodeList
                match charExists with
                | Some (child) ->
                    Data (isWord, Map.add fstChar (aux child remaining) nodeList)
                | None -> 
                    // Create subnode
                    let child = 
                        Map.add fstChar empty nodeList |> 
                        Map.find fstChar
                    
                    Data (isWord, Map.add fstChar (aux child remaining) nodeList)
                    // Call aux on subnode
            | [] -> Data (true, Map.empty) // Set to true and create a leaf

    aux root (Seq.toList word)

insert empty "Hello"




// Nyt link
// https://github.com/mrandri19/trie-fsharp/blob/master/simpleTrie/trie.fsx 
// https://codereview.stackexchange.com/questions/146150/functional-immutable-trie-prefix-tree 

// dictAPI:
// empty: () -> Trie
// insert: string -> Trie -> Trie
// step: char -> Dict -> (bool * Dict) option (bool=true if word exist and then a dictionary for the next level)
// reverse: GADDAG only

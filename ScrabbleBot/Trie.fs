namespace Trie

module Trie = 

    type Dict = 
    | Data of bool * Map<char, Dict>

    let empty = fun () -> Data (false, Map.empty)

    let insert (word : string) (root : Dict) = 
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
                            Map.add fstChar (empty()) nodeList |> 
                            Map.find fstChar
                        
                        Data (isWord, Map.add fstChar (aux remaining child) nodeList)
                        // Call aux on subnode
                | [] -> Data (true, nodeList) // Set to true and create a leaf

        aux (Seq.toList word) root

    let trie = insert "Hello" (empty()) |> insert "Hi" |> insert "Hell"

    let step c dict : option<(bool * Dict)> =
        match dict with
        | Data (isWord, nodes) -> 
            let trie = Map.tryFind c nodes
            match trie with
            | Some (Data (d, a)) -> Some (d, Data (d, a))
            | None -> None

    let mkDict (words : string seq) =
        Seq.fold (fun dict word -> insert word dict) (empty()) words

    let lookup w d =
        let rec aux word dict =
            match word with
            | fstChar :: [] ->
                match step fstChar dict with 
                | Some (a, b) -> Some a
                | None -> None
            | fstChar :: remaining ->
                match step fstChar dict with
                | Some (a, b) -> aux remaining b
                | None -> None
            | [] -> failwith "Something went wrong"
        aux (Seq.toList w) d

    let reverse d (b, dict) = failwith "Not implemented"

    let isGaddag = fun _ -> false

    type 'a dictAPI =
        (unit -> 'a) * // empty
        (string -> 'a -> 'a) * // insert
        (char -> 'a -> (bool * 'a) option) * // step
        ('a -> (bool * 'a) option) option // reverse


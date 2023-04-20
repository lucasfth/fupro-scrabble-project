// Insert your MultiSet.fs file here. All modules must be internal

module internal MultiSet

type MultiSet<'a when 'a: comparison> = MS of Map<'a, uint32>

let empty = MS Map.empty

let isEmpty s =
    match s with
    | _ when s = MS Map.empty -> true
    | _ -> false

let size (MS s) =
    Map.fold (fun acc key n -> acc + n) 0u s

let contains a (MS s) = s |> Map.containsKey a

let numItems a (MS s) =
    s |> Map.tryFind a |> Option.defaultValue 0u

let add a n s : MultiSet<'a> =
    match s with
    | MS ms when contains a s -> MS(ms |> Map.find a |> (+) n |> Map.add a <| ms)
    | MS ms -> MS(ms |> Map.add a n)

let addSingle a (MS s) = MS(s |> Map.add a 1u)

let remove a n s =
    match s with
    | MS ms when int32 (numItems a s) - (int32 n) <= 0 -> MS(ms |> Map.remove a)
    | MS ms -> MS(ms |> Map.add a ((numItems a s) - n))

let removeSingle a (s: MultiSet<'a>) = remove a 1u s

let fold f acc (MS s) = Map.fold f acc s

let foldBack f (MS s) acc = Map.foldBack f s acc

let ofList lst =
    List.foldBack (fun elm acc -> addSingle elm acc) lst empty

let toList (MS s as ms) =
    let rec toList' elm n acc =
        match n with
        | 0u -> acc
        | _ -> toList' elm (n - 1u) (elm :: acc)

    foldBack toList' ms List.Empty

let map (f: 'a -> 'b) mst =
    fold (fun acc a cnt -> add (f a) cnt acc) empty mst

let union s1 s2 =
    fold
        (fun unionset newElement cnt ->
            if cnt > (numItems newElement s1) then
                add newElement cnt unionset
            else
                unionset)
        s1
        s2

let sum s1 s2 =
    fold (fun sumset newElement cnt -> add newElement cnt sumset) s1 s2

let subtract s1 s2 =
    fold (fun subtractset subelement cnt -> remove subelement cnt subtractset) s1 s2

let intersection s1 s2 =
    fold
        (fun intersectset newElement s2cnt ->
            let s1cnt = numItems newElement s1

            if s2cnt < s1cnt then
                add newElement s2cnt intersectset
            else
                add newElement s1cnt intersectset)
        empty
        s2

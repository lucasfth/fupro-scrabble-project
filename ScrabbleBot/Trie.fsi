
module internal Trie

[<Sealed>]
type 'a dictAPI
val empty: Trie<'a>
val insert: Trie<'a>
val step: (bool * Trie)
val mkDict: Trie<'a>
val lookup: bool
val reverse: ('a -> (bool * 'a) option) option
val isGaddag: bool

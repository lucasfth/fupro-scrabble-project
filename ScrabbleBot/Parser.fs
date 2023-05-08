// ScrabbleUtil contains the types coord, boardProg, and SquareProg. Remove these from your file before proceeding.
// Also note that the modulse Ass7 and ImpParser have been merged to one module called Parser.

// Insert your Parser.fs file here from Assignment 7. All modules must be internal.

module internal Parser

open StateMonad
open ScrabbleUtil // NEW. KEEP THIS LINE.
open Eval
open FParsecLight.TextParser // Industrial parser-combinator library. Use for Scrabble Project.
open ScrabbleUtil

type word = Eval.word
type squareFun = Eval.squareFun
type square = Map<int, squareFun>
type boardFun2 = coord -> Result<square option, Error>

type board =
    { center: coord
      defaultSquare: square
      squares: boardFun2 }


let pIntToChar = pstring "intToChar"
let pPointValue = pstring "pointValue"

let pCharToInt = pstring "charToInt"
let pToUpper = pstring "toUpper"
let pToLower = pstring "toLower"
let pCharValue = pstring "charValue"

let pTrue = pstring "true"
let pFalse = pstring "false"
let pIsDigit = pstring "isDigit"
let pIsLetter = pstring "isLetter"
let pIsVowel = pstring "isVowel"

let pif = pstring "if"
let pthen = pstring "then"
let pelse = pstring "else"
let pwhile = pstring "while"
let pdo = pstring "do"
let pdeclare = pstring "declare"

let whitespaceChar = satisfy System.Char.IsWhiteSpace <?> "whitespace"
let pletter = satisfy System.Char.IsLetter <?> "letter"
let palphanumeric = satisfy System.Char.IsLetterOrDigit <?> "alphanumeric"

let spaces = many whitespaceChar <?> "spaces"
let spaces1 = many1 whitespaceChar <?> "space1"

let (.>*>.) p1 p2 = p1 .>> spaces .>>. p2
let (.>*>) p1 p2 = p1 .>*>. p2 |>> fst
let (>*>.) p1 p2 = p1 .>*>. p2 |>> snd

let parenthesise p = pchar '(' >*>. p .>*> pchar ')'

let pid =
    pletter <|> pchar '_' .>>. many (palphanumeric <|> pchar '_')
    |>> (fun (a, b) -> System.String.Concat(a :: b))

let unop op = fun p -> op >*>. p

let binop op p1 p2 = p1 .>*> op .>*>. p2

let TermParse, tref = createParserForwardedToRef<aExp> ()
let ProdParse, pref = createParserForwardedToRef<aExp> ()
let AtomParse, aref = createParserForwardedToRef<aExp> ()

let CharParse, cref = createParserForwardedToRef<cExp> ()

let AddParse = binop (pchar '+') ProdParse TermParse |>> Add <?> "Add"
let SubParse = binop (pchar '-') ProdParse TermParse |>> Sub <?> "Sub"
do tref := choice [ AddParse; SubParse; ProdParse ]

let MulParse = binop (pchar '*') AtomParse ProdParse |>> Mul <?> "Mul"
let DivParse = binop (pchar '/') AtomParse ProdParse |>> Div <?> "Div"
let ModParse = binop (pchar '%') AtomParse ProdParse |>> Mod <?> "Mod"
do pref := choice [ MulParse; DivParse; ModParse; AtomParse ]

let ParParseA = parenthesise TermParse
let ParParseC = parenthesise CharParse

let NegationParse = unop (pchar '-') TermParse |>> (fun x -> Mul(N -1, x)) <?> "Neg"
let PointValueParse = unop pPointValue ParParseA |>> PV <?> "PV"
let VariableParse = pid |>> V <?> "V"
let NParse = pint32 |>> N <?> "Int"
let CharToIntParse = unop pCharToInt ParParseC |>> CharToInt <?> "CharToInt"

do
    aref
    := choice
        [ NegationParse
          PointValueParse
          NParse
          ParParseA
          CharToIntParse
          VariableParse ]

let IntToCharParse = unop pIntToChar ParParseA |>> IntToChar <?> "CharToInt"
let ToLowerParse = unop pToLower ParParseC |>> ToLower <?> "ToLower"
let ToUpperParse = unop pToUpper ParParseC |>> ToUpper <?> "ToUpper"
let CharacterValueParse = unop pCharValue ParParseA |>> CV <?> "CV"
let CParse = pchar ('\'') >>. anyChar .>> pchar ('\'') |>> C <?> "C"

do
    cref
    := choice [ IntToCharParse; ToLowerParse; ToUpperParse; CharacterValueParse; CParse ]

let AexpParse = TermParse

let CexpParse = CharParse

let BexpParse = pstring "not implemented"

let stmntParse = pstring "not implemented"


// Probably wrong implementation but this is not used until we implement the correct (non-necessary) mkBoard
let parseSquareProg (sqp: squareProg) : square =
    sqp |> Map.map (fun a b -> (run stmntParse >> getSuccess >> stmntToSquareFun) b)

let parseBoardProg = run stmntParse >> getSuccess >> stmntToBoardFun

// makes a standard shitty board
let mkBoard (bp: boardProg) : board =
    { center = (0, 0)
      defaultSquare = Map.empty
      squares = fun _ -> Success(Some Map.empty) }

(*
let mkBoard (bp: boardProg) =
    { center = bp.center
      defaultSquare = Map.find bp.usedSquare bp.squares |> parseSquareProg
      squares =
        let m' = Map.map (fun _ m -> parseSquareProg m) bp.squares
        parseBoardProg bp.prog m' }
*)

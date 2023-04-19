// Insert your updated Eval.fs file here from Assignment 7. All modules must be internal.

module internal Eval

    open StateMonad
    open System

    let add a b = 
        a >>= fun x ->
        b >>= fun y ->
        ret (x+y)
    
    let sub a b = 
        a >>= fun x -> 
        b >>= fun y -> 
        ret (x-y)
    
    let mul a b = 
        a >>= fun x -> 
        b >>= fun y -> 
        ret (x*y)
    
    let modd a b = 
        a >>= fun x -> 
        b >>= fun y -> 
        if y <> 0 then
            ret (x%y)
                else
        fail DivisionByZero

    let div a b = 
            a >>= fun x ->
             b >>= fun y ->
            if y <> 0 then
                 ret (x/y)
                    else
            fail DivisionByZero   
    
    let aeq a b = 
        a >>= fun x ->
        b >>= fun y ->
        ret (( = ) x y)
    
    let alt a b = 
        a >>= fun x ->
        b >>= fun y ->
        ret (( < ) x y)

    let conj a b = 
        a >>= fun x ->
        b >>= fun y ->
        ret (( && ) x y)
    
    let isdigit c = 
        c >>= fun x -> 
        ret (Char.IsDigit x)
    
    let isletter c = 
        c >>= fun x -> 
        ret (Char.IsLetter x)
    
    let not c = 
        c >>= fun x -> 
        ret (not x)
    
    let isvowel c = 
        c >>= fun (x: char) -> 
        ret ("aeiouæøåAEIOUÆØÅ".Contains x)
    
    let toupper c = 
        c >>= fun x -> 
        ret (Char.ToUpper x)
    
    let tolower c = 
        c >>= fun x -> 
        ret (Char.ToLower x)
    
    let cv c = 
        c >>= fun x -> 
        characterValue x
    
    let inttochar c = 
        c >>= fun x -> 
        ret (char (x + int '0'))  

    type aExp =
        | N of int
        | V of string
        | WL
        | PV of aExp
        | Add of aExp * aExp
        | Sub of aExp * aExp
        | Mul of aExp * aExp
        | Div of aExp * aExp
        | Mod of aExp * aExp
        | CharToInt of cExp

    and cExp =
       | C  of char  (* Character value *)
       | CV of aExp  (* Character lookup at word index *)
       | ToUpper of cExp
       | ToLower of cExp
       | IntToChar of aExp

    type bExp =             
       | TT                   (* true *)
       | FF                   (* false *)

       | AEq of aExp * aExp   (* numeric equality *)
       | ALt of aExp * aExp   (* numeric less than *)

       | Not of bExp          (* boolean not *)
       | Conj of bExp * bExp  (* boolean conjunction *)

       | IsVowel of cExp      (* check for vowel *)
       | IsLetter of cExp     (* check for letter *)
       | IsDigit of cExp      (* check for digit *)

    let (.+.) a b = Add (a, b)
    let (.-.) a b = Sub (a, b)
    let (.*.) a b = Mul (a, b)
    let (./.) a b = Div (a, b)
    let (.%.) a b = Mod (a, b)

    let (~~) b = Not b
    let (.&&.) b1 b2 = Conj (b1, b2)
    let (.||.) b1 b2 = ~~(~~b1 .&&. ~~b2)
    let (.->.) b1 b2 = (~~b1) .||. b2
       
    let (.=.) a b = AEq (a, b)   
    let (.<.) a b = ALt (a, b)   
    let (.<>.) a b = ~~(a .=. b)
    let (.<=.) a b = a .<. b .||. ~~(a .<>. b)
    let (.>=.) a b = ~~(a .<. b)
    let (.>.) a b = ~~(a .=. b) .&&. (a .>=. b)

    let rec arithEval a : SM<int> = 
        match a with  
        | N n -> ret n 
        | V v -> lookup v
        | WL -> wordLength
        | PV a -> arithEval a >>= (fun r -> pointValue r)
        | Add (a, b) -> add (arithEval a) (arithEval b)
        | Sub (a, b) -> sub (arithEval a) (arithEval b)
        | Mul (a, b) -> mul (arithEval a) (arithEval b)
        | Mod (a, b) -> modd (arithEval a) (arithEval b)
        | Div (a, b) -> div (arithEval a) (arithEval b)
        | CharToInt c -> charEval c >>= (fun r -> ret (int r))      

    and charEval ch : SM<char> = 
        match ch with
        | C(ch) -> ret ch
        | ToUpper(ch) -> toupper (charEval ch)
        | ToLower(ch) -> tolower (charEval ch) 
        | CV(ch) -> cv (arithEval ch)
        | IntToChar ch -> inttochar (arithEval ch)   

    let rec boolEval b : SM<bool> = 
        match b with
        | TT -> ret true
        | FF -> ret false

        | AEq(a, b) -> aeq (arithEval a) (arithEval b)
        | ALt(a, b) ->  alt (arithEval a) (arithEval b)

        | Not(b1) -> not (boolEval b1)
        | Conj(a, b) -> conj (boolEval a) (boolEval b)

        | IsDigit(c) -> isdigit (charEval c)
        | IsLetter(c) -> isletter (charEval c)
        | IsVowel(c) -> isvowel (charEval c)


    type stm =                (* statements *)
    | Declare of string       (* variable declaration *)
    | Ass of string * aExp    (* variable assignment *)
    | Skip                    (* nop *)
    | Seq of stm * stm        (* sequential composition *)
    | ITE of bExp * stm * stm (* if-then-else statement *)
    | While of bExp * stm     (* while statement *)

    let rec stmntEval stmnt: SM<unit> = 
        match stmnt with
        | Skip -> ret ()
        | Ass (a, b) -> arithEval b >>= update a
        | Seq (stm1, stm2) -> stmntEval stm1 >>>= stmntEval stm2
        | ITE (guard, stmnt1, stmnt2) ->
                                                            push >>= fun _ -> boolEval guard >>= fun c ->
                                                                if c
                                                                then stmntEval stmnt1
                                                                else stmntEval stmnt2
                                                            >>>= pop
        | While (guard, stm) -> 
                                        push >>= fun _ -> boolEval guard >>= fun c ->
                                            if c
                                            then (stmntEval (While (guard, stmnt)))
                                            else pop
        | Declare x -> declare x

(* Part 3 (Optional) *)

    type StateBuilder() =

        member this.Bind(f, x)    = f >>= x
        member this.Return(x)     = ret x
        member this.ReturnFrom(x) = x
        member this.Delay(f)      = f ()
        member this.Combine(a, b) = a >>= (fun _ -> b)
        
    let prog = new StateBuilder()

    let arithEval2 a = failwith "Not implemented"
    let charEval2 c = failwith "Not implemented"
    let rec boolEval2 b = failwith "Not implemented"

    let stmntEval2 stm = failwith "Not implemented"

(* Part 4 *) 

    type word = (char * int) list
    type squareFun = word -> int -> int -> Result<int, Error>

    let stmntToSquareFun stm = failwith "Not implemented"


    type coord = int * int

    type boardFun = coord -> Result<squareFun option, Error> 

    let stmntToBoardFun stm m = failwith "Not implemented"

    type board = {
        center        : coord
        defaultSquare : squareFun
        squares       : boardFun
    }

    let mkBoard c defaultSq boardStmnt ids = failwith "Not implemented"
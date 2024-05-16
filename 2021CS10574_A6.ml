type exp = V of string | Abs of (string * exp) | App of (exp * exp) | Tuple of exp * exp
         | Int of int 
         | Bool of bool
         | ProjF of exp 
         | ProjS of exp 
         | Ite of exp * exp * exp
         | Plus of exp * exp 
         |Times of exp * exp 
         | And of exp * exp 
         |Or of exp * exp 
         | Not of exp 
         | Eq  of exp * exp 
         | Gt of exp * exp 
         | Case of (string * exp * ls)
                   
                   
and ls  = (ans * ans) list
  
and 
  opcode =  LOOKUP of string 
         | APP  
         | MKCLOS of string * (opcode list)
         | RET  
         | TUP 
         |FST
         | SND
         | INT of int 
         | BOOL of bool
         | PLUS | TIMES | AND | OR | NOT | EQ | GT
         | ITE of opcode list * opcode list 
         | CASE of exp * ((ans * ans) list)
                         
and ans = 
  | None
  | A_Int of int
  | A_Bool of bool
  | A_Clos of closure
  | A_Tuple of ans * ans
  (* Extend with other value types if necessary *)

and closure = string * opcode list * value_table

and value_table = (string * ans) list
    
    
let rec compile e = 
  begin
    match e with 
    | V x -> [LOOKUP x] 
    | Abs (x,e1) -> [ MKCLOS(x ,  compile( e1 ) @ [RET] )  ]
    | App (e1,e2) -> compile( e1 ) @ compile (e2  ) @ [ APP ]
    | Tuple (e1, e2) -> compile e1 @ compile e2 @ [TUP]
    | Int n -> [INT n]
    | ProjF e1 -> compile e1 @ [FST]
    | ProjS e1 -> compile e1 @ [SND]
    | Bool b -> [BOOL b]
    | Ite (e1, e2, e3) -> compile e1 @ [ITE (compile e2, compile e3)]
    | Plus (e1, e2)  ->  (compile e1) @ (compile e2) @ [PLUS] 
    | Times (e1, e2)  ->  (compile e1) @ (compile e2) @ [TIMES]  
    | And (e1, e2)  ->  (compile e1) @ (compile e2) @ [AND] 
    | Or (e1, e2)  -> (compile e1) @ (compile e2) @ [OR] 
    | Not e1 -> (compile e1) @ [NOT] 
    | Eq (e1, e2)  -> (compile e1) @ (compile e2) @ [EQ] 
    | Gt(e1, e2)  -> (compile e1) @ (compile e2) @ [GT]
    | Case ( x ,e1, l) -> (compile e1) @ [CASE (V x, l)]
                                         
                            
                    (* | Int x -> [LOOKUP x]
                      | Bool b -> [LOOKUP b] 
  | Pair (e1,e2) -> compile (e1) @ compile(e2) @ [PAIR]*)
  end

type stack  = ans list 
type dump  = (stack * value_table * (opcode list)) list 
    
type secd = stack * value_table * opcode list * dump  

exception Halt of (secd *string)
exception Return of (secd * string)
exception App of (secd * string)  
exception Stuck of (secd * string) 
    
                   
          

let rec calcStack (s,e,c,d) =
  match c with
  | [] -> (s,e,c,d)
  | LOOKUP x :: c' ->
      let rec lookup x env  = match env with 
        | [] -> raise (Halt ((s,e,c,d),("Variable not found: " ^x)))
        | (y,a)::tail -> if y=x then a else lookup x tail  
      in
      let ans = lookup x e in
      calcStack ( ans :: s , e , c' ,d )
  | APP :: c'' ->
      begin
        match s with 
        | a :: A_Clos (x,c',e') :: s' ->calcStack ( [] ,(x,a)::e' ,c' , (s',e,c'')::d) 
                                         
        | _ ->  raise (App ((s,e,c,d),("Invalid Application")) )
      end 
  
  | MKCLOS (x, c') :: c'' ->
      let ans = A_Clos(x,c',e) in 
      calcStack (ans :: s , e ,c'' ,d )

  | RET :: c' ->
      begin
        match d with 
        | (s' , e' ,c'')::d' -> calcStack ((List.hd s) :: s' , e', c'', d')
                               
        | _  ->raise  (Return ((s,e,c,d),("Invalid Return")))
      end 

  | TUP :: c' ->
      begin
        match s with
        | a :: b :: s' ->  calcStack (A_Tuple(a,b) :: s' , e ,c' ,d ) 
                             
        | _ -> raise (Halt ((s,e,c,d),"Tuple creation requires two values on the stack"))
      end
  | INT n :: c' -> calcStack (A_Int n :: s ,e, c',d ) 

  | BOOL b :: c' -> calcStack ( A_Bool b :: s ,e ,c' ,d ) 
                      
                      
  | FST :: c' -> begin
      match s with 
      | A_Tuple (x,_) :: s' -> calcStack (x :: s' , e, c', d) 

      | _ -> raise (Halt ((s,e,c,d),"Required a Tuple at the top of stack") )
    end
  | SND :: c' -> begin 
      match s with 
      |A_Tuple (_,y)::s' -> calcStack (y :: s' ,e,c', d) 
                             
      | _ -> raise (Halt ((s,e,c,d),"Required a Tuple at the top of stackInvalid Syntax"))
    end
    
  | ITE (c1, c2) :: c' ->
      begin
        match s with
        | A_Bool true :: s' -> calcStack (s',e, c1@c' ,d )
                                
        | A_Bool false :: s' ->calcStack (s', e ,c2@c' ,d )
                                                            
        | _ -> raise (Halt ((s,e,c,d),"ITE requires a boolean value on the stack"))
      end
  | CASE (V x, l):: c' -> 
      begin 
        match s with 
        | a :: s' ->  
            let rec search = function
              | [] -> calcStack (None :: s', e, c', d)
              | (a', b) :: tail -> 
                  if a = a' then 
                    calcStack (b::s', (x, b)::e, c', d)
                  else 
                    search tail
            in 
            search l
        | _ -> raise (Halt ((s, e, c, d), "Case requires a value of type ans inn stack"))
      end

  | PLUS :: c' ->
      begin 
        match s with 
        | A_Int a :: A_Int b :: s' -> calcStack ( A_Int(a+b)::s' ,e ,c' ,d )
        | _ -> raise (Halt ((s,e,c,d),"Appropriate answers missing from stack "))
      end 
  | TIMES :: c' ->
      begin 
        match s with 
        | A_Int a :: A_Int b :: s' -> calcStack ( A_Int(a*b)::s' ,e ,c' ,d )
        | _ -> raise (Halt ((s,e,c,d),"Appropriate answers missing from stack"))
      end 
  | AND :: c' ->
      begin
        match s with 
        | A_Bool a :: A_Bool b :: s' -> calcStack (A_Bool (a&&b)::s' ,e, c',d)
        | _ -> raise (Halt ((s,e,c,d),"Appropriate answers missing from stack "))
      end 
  | OR :: c' -> 
      begin 
        match s with 
        |A_Bool a :: A_Bool b :: s' -> calcStack (A_Bool (a||b)::s' ,e, c',d)
        | _ -> raise (Halt ((s,e,c,d),"Appropriate answers missing from stack "))
      end 
      
  | NOT :: c'  ->
      begin 
        match s with 
        |A_Bool a ::  s' -> calcStack (A_Bool (not a)::s' ,e, c',d)
        | _ -> raise (Halt ((s,e,c,d),"Appropriate answers missing from stack ")) 
      end 
  | EQ :: c' -> 
      begin 
        match s with 
        | A_Int a :: A_Int b :: s' -> calcStack ( A_Bool(a = b)::s' ,e ,c' ,d )
        | _ -> raise (Halt ((s,e,c,d),"Appropriate answers missing from stack ")) 
      end 

  | GT :: c' -> 
      begin 
        match s with 
        | A_Int a :: A_Int b :: s' -> calcStack ( A_Bool(a > b)::s' ,e ,c' ,d )
        | _ -> raise (Halt ((s,e,c,d),"Appropriate answers missing from stack ") )
      end 
  | _ -> raise (Stuck ((s,e,c,d) , "Unexpected Opcode"))
           
                  

           (* Test Cases 
   1.
     compile (Tuple (Int 3, Bool true)) ;;
- : opcode list = [INT 3; BOOL true; TUP]
calcStack ([],[], [INT 3; BOOL true; TUP],[]) ;;
- : stack = [A_Tuple (A_Bool true, A_Int 3)]
   
  2. 
     compile (App (Abs ("x", App (V "x", V "x")), Abs ("x", App (V "x", V "x")))) ;;
- : opcode list =
[MKCLOS ("x", [LOOKUP "x"; LOOKUP "x"; APP; RET]);
 MKCLOS ("x", [LOOKUP "x"; LOOKUP "x"; APP; RET]); APP]
   
calcStack ([],[],[MKCLOS ("x", [LOOKUP "x"; LOOKUP "x"; APP; RET]);
 MKCLOS ("x", [LOOKUP "x"; LOOKUP "x"; APP; RET]); APP],[]) ;;
     
  3.
     compile (Ite (Not (Eq (Int 5, Int 5)), Int 5, Int 10)) ;;
- : opcode list = [INT 5; INT 5; EQ; NOT; ITE ([INT 5], [INT 10])]
   
calcStack ([],[], [INT 5; INT 5; EQ; NOT; ITE ([INT 5], [INT 10])] , []) ;;
- : stack * value_table * opcode list * dump = ([A_Int 10], [], [], [])

   4.
     compile (App (Abs ("x", V "x"), V "y")) ;;
- : opcode list = [MKCLOS ("x", [LOOKUP "x"; RET]); LOOKUP "y"; APP]
calcStack( [],[],compile (App (Abs ("x", V "x"), V "y")) ,[]) ;;
Exception:
Halt
 (([A_Clos ("x", [LOOKUP "x"; RET], [])], [], [LOOKUP "y"; APP], []),
  "Variable not found: y").
   
  5 .
          compile (App (Abs ("x", V "x"), V "y")) ;;
- : opcode list = [MKCLOS ("x", [LOOKUP "x"; RET]); LOOKUP "y"; APP]
     
  calcStack( [],[("y",A_Int 5)],compile (App (Abs ("x", V "x"), V "y")) ,[]) ;;
- : stack * value_table * opcode list * dump =
([A_Int 5], [("y", A_Int 5)], [], [])
   
  6 .
     compile(ProjF (Tuple (Int 5, Bool true))) ;;
- : opcode list = [INT 5; BOOL true; TUP; FST]
     
calcStack ([],[],[INT 5; BOOL true; TUP; FST],[]) ;;
- : stack * value_table * opcode list * dump = ([A_Bool true], [], [], [])
   
  7. 
     compile(Case ("y", Times(Int 4, Int 3), [(A_Int 10, A_Int 4); (A_Int 12, A_Int 1); (A_Int 1, A_Int 42)]));;
- : opcode list =
[INT 4; INT 3; TIMES;
 CASE (V "y",
  [(A_Int 10, A_Int 4); (A_Int 12, A_Int 1); (A_Int 1, A_Int 42)])]
   
calcStack ([],[],[INT 4; INT 3; TIMES;
 CASE (V "y",
  [(A_Int 10, A_Int 4); (A_Int 12, A_Int 1); (A_Int 1, A_Int 42)])],[]) ;;
- : stack * value_table * opcode list * dump =
([A_Int 1], [("y", A_Int 1)], [], [])
   
  8. 
     compile(Case ("y", Times(Int 4, Int 3), [(A_Int 10, A_Int 4); (A_Int 2, A_Int 1); (A_Int 1, A_Int 42)])) ;;
   
- : opcode list =
[INT 4; INT 3; TIMES;
 CASE (V "y", [(A_Int 10, A_Int 4); (A_Int 2, A_Int 1); (A_Int 1, A_Int 42)])]
   
calcStack ([],[],[INT 4; INT 3; TIMES;
 CASE (V "y", [(A_Int 10, A_Int 4); (A_Int 2, A_Int 1); (A_Int 1, A_Int 42)])],[]) ;;
- : stack * value_table * opcode list * dump = ([None], [], [], [])
   
  9.
     compile (Plus (V "x", Int 5)) ;;
- : opcode list = [LOOKUP "x"; INT 5; PLUS]
   
calcStack ([], [("x", A_Int 10)], [LOOKUP "x"; INT 5; PLUS], []) ;;
- : stack * value_table * opcode list * dump =
([A_Int 15], [("x", A_Int 10)], [], [])
   
  
  10 .
     
  compile (Ite (Eq (Int 5, Int 5), App (Abs ("x", Plus (V "x", Int 1)), Int 10), App (Abs ("x", Times (V "x", Int 2)), Int 20))) ;;
- : opcode list =
[INT 5; INT 5; EQ;
 ITE ([MKCLOS ("x", [LOOKUP "x"; INT 1; PLUS; RET]); INT 10; APP],
  [MKCLOS ("x", [LOOKUP "x"; INT 2; TIMES; RET]); INT 20; APP])]
calcStack ([],[],[INT 5; INT 5; EQ;
 ITE ([MKCLOS ("x", [LOOKUP "x"; INT 1; PLUS; RET]); INT 10; APP],
  [MKCLOS ("x", [LOOKUP "x"; INT 2; TIMES; RET]); INT 20; APP])],[]) ;;
- : stack * value_table * opcode list * dump = ([A_Int 11], [], [], [])
     
  11.
     
  compile( App (
    Int 5,  (* This is an integer, not a function *)
    Int 10
  )) ;;
- : opcode list = [INT 5; INT 10; APP]
calcStack([],[],[INT 5; INT 10; APP],[]) ;;
Exception: App (([A_Int 10; A_Int 5], [], [APP], []), "Invalid Application").
*)

      
type value 
  = Int of int
  | Bool of bool
  | Closure of string * expr * value_environment
  | Ref of value ref
  | PairV of value * value
  | ListV of value list

and value_environment = (string * value) list
                               
and expr 
  = Val of value

  | Add of expr * expr
  | Sub of expr * expr
  | Mul of expr * expr
  | Div of expr * expr 

  | Lt  of expr * expr
  | Eq  of expr * expr
  | And of expr * expr
  | Not of expr

  | Let of string * typ * expr * expr
  | Id  of string

  | App of expr * expr
  | Lam of string * typ * expr

  | LetRec of string * typ * expr * expr
  | If of expr * expr * expr

  | Pair of expr * expr
  | Fst of expr
  | Snd of expr

  | Nil 
  | Cons of expr * expr
  | Head of expr
  | Tail of expr

and typ = Int_type 
        | Bool_type
        | Func_type of typ * typ
        | Pair_type of typ * typ
        | List_type of typ
        | Empty_list_type 

type type_environment = (string * typ option) list 


(* Part 1. Complete unparse *)

(*Helper function to unparse functions into int and bool types*)
(*type : t -> string *)
let rec unparse_type (t : typ) : string = 
  match t with
  | Int_type -> "int"
  | Bool_type -> "bool"
  | Func_type (t1, t2) -> "(" ^ ( unparse_type t1) ^ " -> " ^ ( unparse_type t2) ^ ")"
  | Pair_type (t1, t2) ->  "(" ^ ( unparse_type t1) ^ " * " ^ ( unparse_type t2) ^ ")"
  | List_type (t1) -> "(" ^ ( unparse_type t1) ^ " list)"

(*converts an expr value into a string similar to what we type for computations in ocaml*)
(*type : expr -> string *)
let rec unparse (e: expr) : string =
  match e with
  | Val (Int i) -> string_of_int i
  | Val (Bool b) -> string_of_bool b
  | Val (Closure (_,_,_)) -> "<fun>"
  | Val (Ref _ ) -> "reference"
  | Val PairV (v1,v2) -> "( " ^ (unparse (Val v1)) ^ " , " ^ (unparse (Val v2)) ^ " )"
  
  | Add (ex1, ex2) -> "( " ^ (unparse ex1) ^ " + " ^ (unparse ex2) ^ " )"
  | Sub (ex1, ex2) -> "( " ^ (unparse ex1) ^ " - " ^ (unparse ex2) ^ " )"
  | Mul (ex1, ex2) -> "( " ^ (unparse ex1) ^ " * " ^ (unparse ex2) ^ " )"
  | Div (ex1, ex2) -> "( " ^ (unparse ex1) ^ " / " ^ (unparse ex2) ^ " )"

  | Lt  (ex1, ex2) -> "( " ^ (unparse ex1) ^ " < " ^ (unparse ex2) ^ " )"
  | Eq  (ex1, ex2) -> "( " ^ (unparse ex1) ^ " = " ^ (unparse ex2) ^ " )"
  | And (ex1, ex2) -> "( " ^ (unparse ex1) ^ " && " ^ (unparse ex2) ^ " )"
  | Not (ex1) -> "( not " ^ (unparse ex1) ^ " )"

  | Let (str, t, ex1, ex2) -> "( let " ^ str ^ " : " ^ (unparse_type t) ^ " = " ^ (unparse ex1) ^ " in " ^ (unparse ex2) ^ ")"
  | Id  (str) -> str

  | App (ex1, ex2) -> "(" ^ (unparse ex1) ^ " " ^ (unparse ex2) ^ ")"
  | Lam (str, t, ex) -> "( fun (" ^ str ^ ": " ^ (unparse_type t) ^ ") -> " ^ (unparse ex) ^ ")"

  | LetRec (str, t, ex1, ex2) -> "( let rec " ^ str ^ " : " ^ (unparse_type t) ^ " = " ^ (unparse ex1) ^ " in " ^ (unparse ex2) ^ ")"
  | If  (ex1, ex2, ex3) -> "( if " ^ (unparse ex1) ^ " then " ^ (unparse ex2) ^ " else " ^ (unparse ex3) ^ ")"  

  | Pair (ex1, ex2) -> "( " ^ (unparse ex1) ^ " , " ^ (unparse ex2) ^ " )"
  | Fst (ex1) -> "( fst " ^ (unparse ex1) ^ " )"
  | Snd (ex1) -> "( snd " ^ (unparse ex1) ^ " )"

  | Nil -> "[]"
  | Cons (ex1, ex2) -> "( " ^ (unparse ex1) ^ " :: " ^ (unparse ex2) ^ " )"
  | Head (ex1) -> "( List.hd " ^ (unparse ex1) ^ " )"
  | Tail (ex1) -> "( List.tl " ^ (unparse ex1) ^ " )"

  | Val ListV v -> 
    let rec unparse_list (lst : value list) : string = 
    match lst with
    | [] -> ""
    | [x] -> unparse (Val x)
    | x::xs -> unparse (Val x) ^ "; " ^ unparse_list xs 
    in 
    "[ " ^ unparse_list v ^ " ]"



(* Part 2. Complete freevars *)   
(*returns a string list containing the free variables in an expression*) 
(*type : expr -> string list*)
let rec freevars (e: expr) : string list =
  match e with
  | Val _ -> []
  | Id  str -> [str]

  | Not ex -> freevars ex
  
  | Add (ex1, ex2) | Sub (ex1, ex2) | Mul (ex1, ex2) | Div (ex1, ex2) 
  | Lt (ex1, ex2)  | Eq (ex1, ex2)  | And (ex1, ex2) | App (ex1, ex2) 
  | Pair (ex1, ex2)| Cons (ex1, ex2) -> (freevars ex1) @ (freevars ex2)

  | Let (str, _, ex1, ex2) -> (freevars ex1) @ (List.filter (fun x -> x <> str) (freevars ex2) )
  | LetRec (str, _, ex1, ex2) -> (List.filter (fun x -> x <> str) (freevars ex1) ) @ (List.filter (fun x -> x <> str) (freevars ex2) )
   
  | Lam (str, _, ex) -> List.filter (fun x -> x <> str) (freevars ex)
  | If (ex1, ex2, ex3) -> (freevars ex1) @ (freevars ex2) @ (freevars ex3)

  | Fst (ex) | Snd (ex) | Head (ex) | Tail (ex) -> freevars ex
  | Nil -> []
  

       
(* Part 3. Type checking *)           
type result = OK of typ
            | Errs of (expr * string) list


(*helper function for errors where we expect an int*)
(*type : result -> expr -> (expr * string) list *)
let expect_Int (r: result) (e: expr) : (expr * string) list =
  match r with
  | OK Int_type -> []
  | OK Bool_type ->  [(e, "expected Int type") ]
  | Errs errs -> errs

(*helper function for errors where we expect a bool*)
(*type : result -> expr -> (expr * string) list *)
let expect_Bool (r: result) (e: expr) : (expr * string) list =
  match r with
  | OK Bool_type -> []
  | OK Int_type ->  [(e, "expected Bool type") ]
  | Errs errs -> errs

(*helper function for errors where we expect an int or bool*)
(*type : result -> expr -> (expr * string) list *)
let expect_Int_or_Bool (r: result) (e: expr) : (expr * string) list =
  match r with
  | OK Int_type -> []
  | OK Bool_type ->  []
  | Errs errs -> errs 

(*check if a variable exists in a type_environment and returns its value if it does *)  
(*type : type_environment -> string -> typ option *)
let rec find_var (env : type_environment) (str : string) : (typ option) = 
  match env with
  | [] -> None
  | (s, t) :: rest -> if s = str then t else find_var rest str

(*function to check for correct and incorrect types*)
(* type : expr -> type_environment -> result *)
let rec type_check (e:expr) (env: type_environment) : result =
  match e with
  | Val (Int _) -> OK Int_type
  | Val (Bool _) -> OK Bool_type
  | Val (PairV (x1, x2)) ->
     ( match (type_check (Val x1) env), (type_check (Val x2) env) with
       | OK x, OK y -> OK (Pair_type (x, y))
       | OK x, errs -> errs
       | errs, OK y -> errs
       | Errs err1, Errs err2 -> Errs (err1 @ err2)
     )
  | Val (ListV l) -> 
      let head (lst : value list) : typ = 
        if lst = [] then Empty_list_type else
        (match type_check (Val (List.hd lst)) env with
          | OK x -> x 
        )
        in 
      let rec type_check_list (lst : value list) (h : typ) : result = 
        (match lst with
        | [] -> OK (List_type h)
        | x::xs -> if type_check (Val x) env = (OK h) then (type_check_list xs h) else Errs [((Val x), "mismatched types in list")]
        )
      in 
      let th = head l
      in
      type_check_list l th

  | Add (ex1, ex2) | Sub (ex1, ex2) | Mul (ex1, ex2) | Div (ex1, ex2) -> 
   ( match (type_check ex1 env), (type_check ex2 env) with
    | OK Int_type, OK Int_type -> OK Int_type
    | v1, v2 -> Errs (expect_Int v1 ex1 @ expect_Int v2 ex2)
   )      
  
  | Lt (ex1, ex2) ->
    ( match type_check ex1 env, type_check ex2 env with
      | OK Int_type, OK Int_type -> OK Bool_type
      | r1, r2 -> Errs (expect_Int r1 ex1 @ expect_Int r2 ex2)
    )
  | Eq (ex1, ex2) -> 
    ( match type_check ex1 env, type_check ex2 env with
      | OK Bool_type, OK Bool_type -> OK Bool_type
      | OK Int_type, OK Int_type -> OK Bool_type
      | OK Pair_type (v1,v2), OK Pair_type (v3,v4) -> if (v1 = v3 && v2 = v4) then OK Bool_type else Errs [(ex1, "Pair type mismatch")]
      | OK (List_type x), OK (List_type y) -> if (x = y || x = Empty_list_type || y = Empty_list_type) then OK Bool_type else Errs [(ex2, "List type mismatch")]
      | r1, r2 -> Errs (expect_Int_or_Bool r1 ex1 @ expect_Int_or_Bool r2 ex2) 
    )
  | And (ex1, ex2) ->
    ( match type_check ex1 env, type_check ex2 env with
      | OK Bool_type, OK Bool_type -> OK Bool_type
      | r1, r2 -> Errs (expect_Bool r1 ex1 @ expect_Bool r2 ex2)
    )
  | Not (ex1) ->
    ( match type_check ex1 env with
      | OK Bool_type -> OK Bool_type
      | r1-> Errs (expect_Bool r1 ex1) 
    )
  | Let (x, t, ex1, ex2) ->
     let rex1 = type_check ex1 env
     in
     (match rex1 with
     | Errs errs -> Errs errs
     | OK ty -> if ty = t then type_check ex2 ((x, Some ty) :: env) else Errs [(e, "mismatched types, Let")]
     )
  | Id str -> 
      (match (find_var env str) with
      | None -> Errs [(Id str, "identifer not found")]
      | Some t -> OK t
      )  
  | If (ex1, ex2, ex3) -> 
      ( match type_check ex1 env, type_check ex2 env, type_check ex3 env with
       | OK Bool_type, OK x, OK y -> if x = y then OK x else Errs [(e, "mismatched type")]
       | r1, r2, r3 -> Errs (expect_Bool r1 ex1 @ expect_Bool r2 ex2 @ expect_Bool r3 ex3) 
      )  
  | App (ex1, ex2) -> 
      ( match (type_check ex1 env), (type_check ex2 env) with
        | OK Func_type (t1, t2), OK t3 -> if t1 = t3 then (OK t2) else Errs [(e, "mismatched type")]
        | r1, r2 -> Errs (expect_Int_or_Bool r1 ex1 @ expect_Int_or_Bool r2 ex2)
      )
  | Lam (str, t, ex) -> 
      ( match (type_check ex ((str, Some t) :: env)) with 
        | OK Bool_type -> OK (Func_type (t, Bool_type))
        | OK Int_type -> OK (Func_type (t, Int_type))
        | OK (Pair_type (x1,y1)) -> OK (Func_type (t, (Pair_type (x1,y1))))
        | OK (List_type x) -> OK (Func_type (t, (List_type x)))
        | Errs errs -> Errs [(e, "invalid type")]

      )
  | LetRec (str, t, ex1, ex2) ->
    let rex1 = type_check ex1 ((str, Some t) :: env) in
     (match rex1 with
     | Errs errs -> Errs errs
     | OK ty -> type_check ex2 ((str, Some ty) :: env)
     )

  | Pair (ex1, ex2) ->
    ( match (type_check ex1 env), (type_check ex2 env) with
      | (OK v1, OK v2) -> OK (Pair_type (v1, v2))
      | v1, v2 -> Errs (expect_Int_or_Bool v1 ex1 @ expect_Int_or_Bool v2 ex2)
    )   
  | Fst (ex1) -> 
    ( match type_check ex1 env with 
      | OK (Pair_type (x1,x2)) -> OK x1
      | _ -> Errs [(Fst (ex1), "expected Pair type") ]
    )
  | Snd (ex1) -> 
    ( match type_check ex1 env with 
      | OK (Pair_type (x1,x2)) -> OK x2
      | _ -> Errs [(Snd (ex1), "expected Pair type") ]
    )

  | Nil -> OK (List_type Empty_list_type)
    
  | Cons (ex1, ex2) ->  
    ( match (type_check ex1 env), (type_check ex2 env) with
      | OK t1, OK (List_type t2) -> if t1 = t2 || t2 = Empty_list_type then OK (List_type t1) else Errs [(e, "mismatched types, Cons")]
      | OK x, OK y -> Errs [(e, "expected list")]
      | Errs e1, Errs e2 -> Errs (e1 @ e2)
      | OK x, Errs errs -> Errs errs
      | Errs errs, OK y -> Errs errs
      | _ -> Errs [(ex1, "mismatched types, Cons")]
    )

  | Head (ex1) -> 
    ( match type_check ex1 env with 
      | OK (List_type l) -> OK l
      | Errs errs -> Errs errs 
      | _ -> Errs [(Head (ex1), "expected List type") ]
    )

  | Tail (ex1) -> 
    ( match type_check ex1 env with 
      | OK (List_type l) -> OK (List_type l)
      | Errs errs -> Errs errs 
      | _ -> Errs [(Tail (ex1), "expected List type") ]
    )



  
let check e = type_check e [] 


(* Part 4. Evaluation *)
(*helper function to check if a variable exists in a type_environment otherwise determines that it is unbound *)  
(*type : value_environment -> string -> (string * value) *)
let rec lookup (env : value_environment) (n: string) : (string * value) =
  match env with
  | [] -> failwith ("unbound variable"^n)
  | (x, v)::rest when x = n -> (x, v)
  | (_,_)::rest -> lookup rest n

(*helper function to create the environement for an expression*)  
(*type : string list -> value_environment -> value_environment  *)
let rec create_env (lst : string list) (env : value_environment) : value_environment = 
  match lst with
  | [] -> []
  | x :: [] -> [lookup env x]
  | x :: rest -> [lookup env x] @ create_env rest env

(*check if a variable exists in a type_environment and returns its value if it does *)  
(*type : value_environment -> string ->  value *)
let rec find_var_2 (env : value_environment) (str : string) : (value option) = 
  match env with
  | [] -> None
  | (s, t) :: rest -> if s = str then (Some t) else find_var_2 rest str


(*helper function to check if 2 lists are equal*)
(*type : 'a list -> 'a list ->  bool *)
let rec lists_equal (l1: value list) (l2: value list): bool =
  match l1, l2 with
  | [], [] -> true 
  | x::xs, [] -> false
  | [], y::ys -> false
  | x::xs, y::ys -> if x = y then lists_equal xs ys 
                    else false

(*evaluates all forms of expressions *)
(*type : value_environment -> expr ->  value *)
let rec eval (env: value_environment) (e:expr) : value =
 match e with
  | Val v -> v

  | Add (ex1, ex2) ->
     ( match eval env ex1, eval env ex2 with
       | Int v1, Int v2 -> Int (v1 + v2)
       | _ -> raise (Failure "incompatible types, Add")
     )
  | Sub (ex1, ex2) ->
     ( match eval env ex1, eval env ex2 with
       | Int v1, Int v2 -> Int (v1 - v2)
       | _ -> raise (Failure "incompatible types, Sub")
     )
  | Mul (ex1, ex2) ->
     ( match eval env ex1, eval env ex2 with
       | Int v1, Int v2 -> Int (v1 * v2)
       | _ -> raise (Failure "incompatible types, Mul")
     )
  | Div (ex1, ex2) ->
     ( match eval env ex1, eval env ex2 with
       | Int v1, Int v2 -> Int (v1 / v2)
       | _ -> raise (Failure "incompatible types, Div")
     )

  | Lt (ex1, ex2) ->
     ( match eval env ex1, eval env ex2 with
       | Int v1, Int v2 -> Bool (v1 < v2)
       | _ -> raise (Failure "incompatible types, Lt")
     )
  | Eq (ex1, ex2) ->
     ( match eval env ex1, eval env ex2 with
       | Int v1, Int v2 -> Bool (v1 = v2)
       | Bool v1, Bool v2 -> Bool (v1 = v2)
       | PairV (v1,v2), PairV (v3,v4) -> Bool (v1 = v3 && v2 = v4)
       | ListV (l1), ListV (l2) ->  Bool (lists_equal l1 l2)
       | _ -> raise (Failure "incompatible types, Eq")
     )
  | And (ex1, ex2) ->
     ( match eval env ex1, eval env ex2 with
       | Bool v1, Bool v2 -> Bool (v1 && v2)
       | _ -> raise (Failure "incompatible types, And")
     )
  | Not ex ->
      ( match eval env ex with
       | Bool v1 -> Bool (not v1)
       | _ -> raise (Failure "incompatible types, Not")
      )
  | Let (n, t, dexpr, body) ->
      let v = eval env dexpr in
      eval ((n,v) :: env) body 

  (* LetRec adds the passed string to the value environment by innitially tying it to an arbitrary reference then changing the reference value once the value for the 
     string is obtained through calling eval on expression 1 *)
  | LetRec (str, t, ex1, ex2) -> 
    ( match ex1 with 
      | Lam (n, t, fbody) -> 
          let r = ref (Int (5)) in 
          let v = eval ((str, Ref r) :: env) (Lam (n, t, fbody)) in
          let () = r := v in
          eval ((str, v) :: env) ex2
      | _ -> raise (Failure "let rec expressions must declare a function")
    )
  | Id str -> ( match (find_var_2 env str) with 
                | None -> raise (Failure "unbound variable, Id")
                | Some t -> t
              )
  (* The first passed expression will always match to either a closure or a reference to a closure. If expression one matches to any other value, a failure is raised *)
  | App (ex1, ex2) -> ( match (eval env ex1) with
                        | Closure (str, ex, new_ev) -> eval ((str, (eval env ex2)) :: new_ev) ex
                        | Ref x -> (match !x with
                                   | Closure (str, ex, new_ev) -> eval ((str, (eval env ex2)) :: new_ev) ex
                                   | _ -> raise (Failure "mismatched types, App")
                                   )
                        | _ -> raise (Failure "mismatched types, App")
                      )
  | Lam (str, ty, ex) -> 
      let vars_list = freevars (Lam (str, ty, ex)) in
      let new_ev = create_env vars_list (env) in
      Closure (str, ex, new_ev)

  | If (ex1, ex2, ex3) -> 
      ( match eval env ex1 with
       | Bool v1 when v1 = true -> eval env ex2
       | Bool v1 when v1 = false -> eval env ex3
       | _ -> raise (Failure "incompatible types, If")
      )

  | Pair (ex1,ex2) -> PairV (eval env ex1, eval env ex2)

  | Fst (ex) -> 
      ( match eval env ex with
        | PairV (ex1, ex2) -> ex1
        | _ -> raise (Failure "incompatible types, Fst")
      )

  | Snd (ex) ->
      ( match eval env ex with
        | PairV (ex1, ex2) -> ex2
        | _ -> raise (Failure "incompatible types, Snd")
      )

  | Nil -> ListV []
  
  | Cons (ex1, ex2) -> 
      ( match (eval env ex2) with
        | ListV lst -> ListV ([eval env ex1] @ lst)
        | _ -> raise (Failure "incompatible types, Cons")
      )
  | Head (ex) -> 
      ( match eval env ex with
        | ListV [] -> failwith "Cannot retrieve head of empty list"
        | ListV (x::_) -> x
        | _ -> raise (Failure "incompatible types, Head")
      )
  | Tail (ex) -> 
      ( match eval env ex with
        | ListV [] -> failwith "Cannot retrieve tail of empty list"
        | ListV (_::xs) -> ListV xs
        | _ -> raise (Failure "incompatible types, Tail")
      )
  



let evaluate e = eval [] e


(* some sample expressions *)

let ex1 = Add (Val (Int 3), Val (Int 5))
let ex2 = Add (Val (Int 3), Val (Bool true))
let e3 = Mul (Val (Bool true), Val (Int 5))
let e4 = Add (ex2, e3)
let check_test = Add(e4, e4)



let e5 = Let ("x", Int_type, Add (Val (Int 3), Val (Int 4)),
              Add (Id "x", Val (Int 5))
           )
       
let e6 = Let ("x", Int_type, Add (Val (Int 3), Val (Int 4)),
              Lt (Id "x", Val (Int 5))
           )
       
(* ``let x = 3 < 5 in x && let x = 1 + 2 in x = 3 *)
let e7 = Let ("x", Bool_type,
              Lt (Val (Int 3), Val (Int 5)),
              And (Id "x",
                   Let ("x", Int_type,
                        Add (Val (Int 1), Val (Int 2)),
                        Eq (Id "x", Val (Int 3))
                       )
                  )
             )


(* ``let x = 3 < 5 in y && let x = 1 + 2 in x = 3 *)
let e8 = Let ("x", Bool_type,
              Lt (Val (Int 3), Val (Int 5)),
              And (Id "y",
                   Let ("x", Int_type,
                        Add (Val (Int 1), Val (Int 2)),
                        Eq (Id "x", Val (Int 3))
                       )
                  )
             )

let err_1 = Let ("x", Int_type, Add (Val (Int 3), Val (Int 4)),
                 And (Id "x", Val (Bool true))
              )

let err_2 = Let ("x", Int_type, Add (Id "x", Val (Int 4)),
                 And (Id "y", Val (Bool true))
              )

let inc_use = Let ("inc", Func_type (Int_type, Int_type), 
                   Lam ("n", Int_type, Add (Id "n", Val (Int 1))),
                   App (Id "inc", Val (Int 3))
                )

let sumToN : expr =
    LetRec ("sumToN", Func_type (Int_type, Int_type),
            Lam ("n", Int_type,
                 If (Eq (Id "n", Val (Int 0)),
                     Val (Int 0),
                     Add (Id "n",
                          App (Id "sumToN",
                               Sub (Id "n", Val (Int 1))
                              )
                         )
                    )
                ),
            Id "sumToN"
           )

let sumTo3 = App (sumToN, Val (Int 4))

let inc = Lam ("n", Int_type, Add(Id "n", Val (Int 1)))

let add = Lam ("x", Int_type,
               Lam ("y", Int_type, Add (Id "x", Id "y"))
              )


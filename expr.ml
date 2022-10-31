(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
  | F_Negate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | DividedBy
  | F_Plus
  | F_Minus
  | F_Times
  | F_DividedBy
  | Equals
  | LessThan
  | GreaterThan
  | Concat
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Float of float                       (* floats *)
  | Bool of bool                         (* booleans *)
  | Str of string                        (* strings *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids) and sets of them
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var x       -> SS.singleton x
  | Unop (_, e) -> free_vars e
  | App (e1, e2) 
  | Binop (_, e1, e2)        -> SS.union (free_vars e1) (free_vars e2)
  | Conditional (e1, e2, e3) -> SS.union (free_vars e1)
                                          (SS.union (free_vars e2) 
                                                    (free_vars e3)) 
  | Fun (x, body)         -> SS.remove x (free_vars body)
  | Let (x, def, body)    -> SS.union (free_vars def) 
                                      (SS.remove x (free_vars body))
  | Letrec (x, def, body) -> SS.union (SS.remove x (free_vars def))
                                      (SS.remove x (free_vars body))
  | _ -> SS.empty ;;
  
(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no variable names use the
   prefix "var". (Otherwise, they might accidentally be the same as a
   generated variable name.) *)
let new_varname : unit -> varid =
  let n_ref = ref 0 in
  fun () ->
    let n_last = "var" ^ string_of_int (!n_ref) in
    n_ref := !n_ref + 1;
    n_last ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let fvs_in_repl = free_vars repl in
  let f = subst var_name repl in
  match exp with
  | Var x                      -> if x = var_name then repl else Var x
  | Unop (unop, e)             -> Unop (unop, f e)
  | App (e1, e2)               -> App (f e1, f e2)
  | Binop (binop, e1, e2)      -> Binop (binop, f e1, f e2)
  | Conditional (cond, e1, e2) -> Conditional (f cond, f e1, f e2)
  | Fun (x, body) -> 
    if var_name = x                    then exp
    else if not (SS.mem x fvs_in_repl) then Fun (x, f body)
    else let z = new_varname () in Fun (z, f (subst x (Var z) body))
  | Let (x, def, body) -> 
    if var_name = x                    then Let (x, f def, body)
    else if not (SS.mem x fvs_in_repl) then Let (x, f def, f body)
    else let z = new_varname () in 
         Let (z, f def, f (subst x (Var z) body))
  | Letrec (x, def, body) ->
    if var_name = x                    then exp
    else if not (SS.mem x fvs_in_repl) then Letrec (x, f def, f body)
    else let z = new_varname () in 
         let subst_z = subst x (Var z) in 
         Letrec (z, f (subst_z def), f (subst_z body))
  | _ -> exp ;;

(*......................................................................
  String representations of expressions
 *)

(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)
let rec exp_to_concrete_string (exp : expr) : string =
  let f = exp_to_concrete_string in
  match exp with
  | Var s
  | Str s                 -> s
  | Num int               -> string_of_int int
  | Float float           -> string_of_float float 
  | Bool bool             -> string_of_bool bool
  | Unop (unop, e)        -> "(" ^ (
    match unop with
    | Negate   -> "~-"
    | F_Negate -> "~-.") ^ (f e) ^ ")"
  | Binop (binop, e1, e2) -> "(" ^ (f e1) ^ (
    match binop with
    | Plus        -> " + "
    | Minus       -> " - "
    | Times       -> " * " 
    | DividedBy   -> " / "
    | F_Plus      -> " +. "
    | F_Minus     -> " -. "
    | F_Times     -> " *. " 
    | F_DividedBy -> " /. "
    | Equals      -> " = "
    | LessThan    -> " < "
    | GreaterThan -> " > "
    | Concat      -> " ^ ")  ^ (f e2) ^ ")"
  | Conditional (cond, e1, e2) -> "if " ^ (f cond) ^ " then " ^ (f e1)
                                  ^ " else " ^ (f e2)
  | Fun (x, body)         -> "fun " ^ x ^ " -> " ^ (f body)
  | Let (x, def, body)    -> "let " ^ x ^ " = " ^ (f def) ^ " in " ^ (f body)
  | Letrec (x, def, body) -> "let rec " ^ x ^ " = " ^ (f def) ^ " in " 
                             ^ (f body)
  | Raise        -> "Raise"                     
  | Unassigned   -> "Unassigned"         
  | App (e1, e2) -> (f e1) ^ " " ^ (f e2) ;;

(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  let f = exp_to_abstract_string in
  match exp with
  | Var x                 -> "Var \"" ^ x ^ "\""
  | Str s                 -> "Str \"" ^ s ^ "\""
  | Num int               -> "Num " ^ string_of_int int
  | Float float           -> "Float " ^ string_of_float float
  | Bool bool             -> "Bool " ^ string_of_bool bool
  | Unop (unop, e)        -> "Unop(" ^ (
    match unop with
    | Negate   -> "Negate, "
    | F_Negate -> "F_Negate, ") ^ (f e) ^ ")"
  | Binop (binop, e1, e2) -> "Binop(" ^ (
    match binop with
    | Plus        -> "Plus, " 
    | Minus       -> "Minus, "
    | Times       -> "Times, "
    | DividedBy   -> "DividedBy, "
    | F_Plus      -> "F_Plus, " 
    | F_Minus     -> "F_Minus, "
    | F_Times     -> "F_Times, "
    | F_DividedBy -> "F_DividedBy, "
    | Equals      -> "Equals, "
    | LessThan    -> "LessThan, "
    | GreaterThan -> "GreaterThan, "
    | Concat      -> "Concat, ") ^ (f e1) ^ ", " ^ (f e2) ^ ")"
  | Conditional (cond, e1, e2) -> "Conditional(" ^ (f cond) ^ ", " ^ (f e1) 
                                  ^ ", " ^ (f e2) ^ ")"
  | Fun (x, body)         -> "Fun(\"" ^ x ^ "\", " ^ (f body) ^ ")"
  | Let (x, def, body)    -> "Let(\"" ^ x ^ "\", " ^ (f def) ^ ", " ^ (f body) 
                             ^ ")"
  | Letrec (x, def, body) -> "Letrec(\"" ^ x ^ "\", " ^ (f def) ^ ", " 
                             ^ (f body) ^ ")"
  | Raise        -> "Raise"                     
  | Unassigned   -> "Unassigned"         
  | App (e1, e2) -> "App(" ^ (f e1) ^ ", " ^ (f e2) ^ ")" ;;

(*
                         CS 51 Project
                     Semantics -- Testing
*)                           

open Expr ;;
open Evaluation ;;
open CS51Utils ;;
open Absbook ;;

let x = Var "x"
let y = Var "y"
let f = Var "f"
let q = Num 2
let r = Num 21
let p = Binop (Times, q, r)  
let p_withFV_y = Binop (Times, q, y)
let funcx = Fun ("x", Binop (Times, q, x))
let funcy = Fun ("y", p_withFV_y)
let factx = Fun("x", Conditional(Binop(Equals, x, Num(0)), Num(1),
                                 Binop(Times,x,App(f,Binop(Minus,x,Num(1))))))
let fact_ans = Env.Val (Num 24)
let ans = Env.Val (Num 42)
let env_valx = Env.extend (Env.empty ()) "x" (ref ans)
let env_valy = Env.extend (Env.empty ()) "y" (ref ans)
let env_clox = Env.extend (Env.empty ()) "f" (ref (Env.Closure (funcx , env_valx)))
let env_cloy = Env.extend (Env.empty ()) "f" (ref (Env.Closure (funcy , env_valy)))
let env_bigx = Env.extend env_valx "f" (ref (Env.Closure (funcx , env_valx)))
let semantics_matters = Let("x", q, 
                        Let("f", Fun("y", Binop(Plus, x, y)), 
                        Let("x", Num(8), 
                        App(f, x))))


let free_vars_test () =
  unit_test (same_vars (free_vars q) (vars_of_list []))
            "free_vars: Num (simple, no varids)";
  unit_test (same_vars (free_vars x) (vars_of_list ["x"]))
            "free_vars: Var (simple, varids)";
  unit_test (same_vars (free_vars (Unop (Negate, y))) (vars_of_list ["y"]))
            "free_vars: Unop";
  unit_test (same_vars (free_vars (Binop (Plus, y, y))) (vars_of_list ["y"]))
            "free_vars: Binop";
  unit_test (same_vars (free_vars (Fun ("x", p))) (vars_of_list []))
            "free_vars: Fun (no var)";
  unit_test (same_vars (free_vars (Fun ("y", p_withFV_y))) (vars_of_list []))
            "free_vars: Fun (bound var)";
  unit_test (same_vars (free_vars (Fun ("x", p_withFV_y))) (vars_of_list ["y"]))
            "free_vars: Fun (unbound var)";
  unit_test (same_vars (free_vars (Let ("x", q, p))) (vars_of_list []))
            "free_vars: Let (no var)";
  unit_test (same_vars (free_vars (Let ("y", q, p_withFV_y))) (vars_of_list []))
            "free_vars: Let (bound var)";
  unit_test (same_vars (free_vars (Let ("x", q, p_withFV_y))) (vars_of_list ["y"]))
            "free_vars: Let (unbound var)"; ;;

let subst_test () =
  unit_test (subst "x" p q = q)
            "subst: Num";
  unit_test (subst "x" p y = y)
            "subst: Var (x <> y)";
  unit_test (subst "x" p x = p)
            "subst: Var (x = y)";
  unit_test (subst "x" p (Unop (Negate, x)) = Unop (Negate, p))
            "subst: Unop";
  unit_test (subst "x" p (Binop (Plus, x, x)) = Binop (Plus, p, p))
            "subst: Binop";
  unit_test (subst "x" p (Fun ("x", q)) = Fun ("x", q))
            "subst: Fun (x = y)";
  unit_test (subst "x" p (Fun ("y", q)) = Fun ("y", q))
            "subst: Fun (x <> y and varid is free)";
  unit_test (exp_to_concrete_string 
            (subst "x" p_withFV_y (Fun ("y", q))) = "fun var0 -> 2")
            "subst: Fun (x <> y and y is bound in p)";
  unit_test (subst "x" p (Let ("x", q, r)) = Let ("x", q, r))
            "subst: Let (x = y)";
  unit_test (subst "x" p (Let ("y", q, r)) = Let ("y", q, r))
            "subst: Let (x <> y and varid is free)";
  unit_test (exp_to_concrete_string 
            (subst "x" p_withFV_y (Let ("y" , q , r))) = "let var1 = 2 in 21")
            "subst: Let (x <> y and varid is bound)"; ;;

let eval_s_test () =
  (* Basic tests *)
  unit_test (eval_s q (Env.empty ()) = Env.Val q) 
            "eval_s: things which evaluate to themselves";
  unit_test (eval_s (Unop (Negate, q)) (Env.empty ()) = Env.Val (Num (-2))) 
            "eval_s: Unop";
  unit_test (eval_s p (Env.empty ()) = ans) 
            "eval_s: Binop";
  unit_test (eval_s (Conditional (Bool true, q, r)) (Env.empty ()) = Env.Val q) 
            "eval_s: Conditional true";
  unit_test (eval_s (Conditional (Bool false, q, r)) (Env.empty ()) = Env.Val r) 
            "eval_s: Conditional false";
  unit_test (eval_s (App (funcy, r)) (Env.empty ()) = ans) 
            "eval_s: App";
  unit_test (eval_s (Let ("y", r, p_withFV_y)) (Env.empty ()) = ans) 
            "eval_s: Let";
  unit_test (eval_s (Letrec ("y", r, p_withFV_y)) (Env.empty ()) = ans) 
            "eval_s: Letrec";
  unit_test (eval_s (Letrec("f", factx, App(Var("f"), Num(4)))) (Env.empty ()) 
              = fact_ans) 
            "eval_s: Letrec with recursion";
  unit_test (eval_s semantics_matters (Env.empty ()) = Env.Val (Num 10)) 
            "eval_s: Semantics Matters"; ;;

let extend_test () =
  let repl = ref (Env.Val r) in
  unit_test (Env.env_to_string env_valx = "{x -> 42; }") 
            "Env.extend: fill empty env w/ value = Value";
  unit_test (Env.env_to_string env_clox = "{f -> [{x -> 42; } ⊢ fun x -> (2 * x)]; }") 
            "Env.extend: fill empty env w/ value = Closure";
  unit_test (Env.env_to_string (Env.extend env_valx "x" repl) = 
              Env.env_to_string (Env.extend (Env.empty ()) "x" repl))
            "Env.extend: replace on env size 1";
  unit_test (Env.env_to_string env_bigx = 
    "{f -> [{x -> 42; } ⊢ fun x -> (2 * x)]; x -> 42; }")
            "Env.extend: add new varid-value pair to env";
  unit_test (Env.env_to_string (Env.extend env_bigx "x" repl) = 
    "{x -> 21; f -> [{x -> 42; } ⊢ fun x -> (2 * x)]; }")
            "Env.extend: replace on env size 2"; ;;

let close_test () =
  unit_test (Env.value_to_string (Env.close x env_valx) = "[{x -> 42; } ⊢ x]") 
            "Env.close:"; ;;

let lookup_test () =
  unit_test (Env.lookup env_valx "x" = ans) 
            "Env.lookup: value = Value"; ;;

let eval_d_test () =
  unit_test (eval_d q (Env.empty ()) = Env.Val q) 
            "eval_d: things which evaluate to themselves";
  unit_test (eval_d (Unop (Negate, q)) (Env.empty ()) = Env.Val (Num (-2))) 
            "eval_d: Unop";
  unit_test (eval_d p (Env.empty ()) = ans) 
            "eval_d: Binop";
  unit_test (eval_d (Conditional (Bool true, q, r)) (Env.empty ()) = Env.Val q) 
            "eval_d: Conditional true";
  unit_test (eval_d (Conditional (Bool false, q, r)) (Env.empty ()) = Env.Val r) 
            "eval_d: Conditional false";
  unit_test (eval_d x env_valx = ans) 
            "eval_d: Var";
  unit_test (eval_d (App (funcy, x)) env_valx = Env.Val (Num 84)) 
            "eval_d: App";
  unit_test (eval_d (Let ("x", r, p_withFV_y)) env_valy = Env.Val (Num 84)) 
            "eval_d: Let";
  unit_test (eval_d (Letrec("f", factx, App(Var("f"), y))) 
                    (Env.extend (Env.empty ()) "y" (ref (Env.Val (Num 4)))) 
              = fact_ans) 
            "eval_d: Letrec with recursion";
  unit_test (eval_d semantics_matters (Env.empty ()) = Env.Val (Num 16)) 
            "eval_d: Semantics Matters"; ;;

let eval_l_test () =
  unit_test (eval_l q (Env.empty ()) = Env.Val q) 
            "eval_l: things which evaluate to themselves";
  unit_test (eval_l (Unop (Negate, q)) (Env.empty ()) = Env.Val (Num (-2))) 
            "eval_l: Unop";
  unit_test (eval_l p (Env.empty ()) = ans) 
            "eval_l: Binop";
  unit_test (eval_l (Conditional (Bool true, q, r)) (Env.empty ()) = Env.Val q) 
            "eval_l: Conditional true";
  unit_test (eval_l (Conditional (Bool false, q, r)) (Env.empty ()) = Env.Val r) 
            "eval_l: Conditional false";
  unit_test (eval_l x env_valx = ans) 
            "eval_l: Var";
  unit_test (eval_l (App (funcy, x)) env_valx = Env.Val (Num 84)) 
            "eval_l: App";
  unit_test (eval_l (Let ("x", r, p_withFV_y)) env_valy = Env.Val (Num 84)) 
            "eval_l: Let";
  unit_test (eval_l (Letrec("f", factx, App(Var("f"), y))) 
                    (Env.extend (Env.empty ()) "y" (ref (Env.Val (Num 4)))) 
              = fact_ans) 
            "eval_l: Letrec with recursion";
  unit_test (eval_l semantics_matters (Env.empty ()) = Env.Val (Num 10)) 
            "eval_l: Semantics Matters"; 
            ;;


let test_all () =
  free_vars_test () ;;
  subst_test () ;;
  eval_s_test () ;;
  extend_test () ;;
  close_test () ;;
  lookup_test () ;;
  eval_d_test () ;;
  eval_l_test () ;;

let _ = test_all () ;;

(*
   thunkLang.
   ~~~~~~~~~~

    - Extends the pureLang syntax with “Delay” and “Force” in :exp, and
      “Thunk” in :v.
    - Call by value.
    - Environment semantics (avoids mutual recursion between exp and v;
      “Thunk env exp”).
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory;

val _ = new_theory "thunkLang";

Type vname = “:string”;
Type op = “:pure_exp$op”;

Datatype:
  exp = Var vname                        (* variable                *)
      | Prim op (exp list)               (* primitive operations    *)
      | App exp exp                      (* function application    *)
      | Lam vname exp                    (* lambda                  *)
      | Letrec ((vname # exp) list) exp  (* mutually recursive exps *)
      | Delay exp                        (* creates a Thunk value   *)
      | Force exp                        (* evaluates a Thunk       *)
End


Datatype:
  v = Constructor string (v list)
    | Closure vname ((vname # v) list) exp
    | Thunk ((vname # v) list) exp
    | Atom lit
End

Datatype:
  err = Type_error
      | Diverge
End

Definition sum_bind_def:
  sum_bind m f =
    case m of
      INL e => INL e
    | INR x => f x
End

Definition sum_ignore_bind_def:
  sum_ignore_bind m x = sum_bind m (K x)
End

val sum_monadinfo : monadinfo = {
  bind = “sum_bind”,
  ignorebind = SOME “sum_ignore_bind”,
  unit = “INR”,
  fail = SOME “INL”,
  choice = NONE,
  guard = NONE
  };

val _ = declare_monad ("sum", sum_monadinfo);
val _ = enable_monad "sum";
val _ = enable_monadsyntax ();

Definition map_def:
  map f [] = return [] ∧
  map f (x::xs) =
    do
      y <- f x;
      ys <- map f xs;
      return (y::ys)
    od
End

Definition dest_Closure_def:
  dest_Closure (Closure s env x) = return (s, env, x) ∧
  dest_Closure _ = fail Type_error
End

(* TODO
 *
 * What is the semantics of Force?
 *
 * - Letrec is wrong, right? I'm not even sure what it means to force
 *   a bunch of declarations. If we can't force the bodies of the expressions
 *   then forcing needs to go into eval.
 *
 * - Here are some alternatives how this could work:
 *   1 Force (Delay x) = x
 *   2 Force (foo_notdelay (bar_notdelay (baz_notdelay ... (Delay x)))) = x
 *   3 As it is, Force x = remove all Delays in x
 *
 *   #1 Seems ok, I guess
 *   #2 Seems a bit ad-hoc
 *   #3 Seems ok, I guess
 *)
Definition force_def:
  force (App f x) = App (force f) (force x) ∧
  force (Prim op xs) = Prim op (MAP force xs) ∧
  force (Lam s x) = (Lam s (force x)) ∧
  (* I'm not so sure about this one: *)
  force (Letrec funs x) = Letrec (MAP (λ(v,x). (v, force x)) funs) x ∧
  force (Delay x) = force x ∧
  force (Force x) = force x
Termination
  WF_REL_TAC ‘measure exp_size’ \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [definition "exp_size_def"]
End

(* TODO
 * I can't figure out what “get_lits” should do in case we come across a
 * thunk, but it might get clear when we think about how to compile pureLang
 * into thunkLang. Probably thunks are forbidden here.
 *)

Definition get_lits_def:
  get_lits [] = return [] ∧
  get_lits (x::xs) =
    (do
       y <- case x of Atom l => return l | _ => fail Type_error ;
       ys <- get_lits xs ;
       return (y::ys)
     od)
End

Definition do_prim_def:
  do_prim op vs =
    case op of
      Cons s => return (Constructor s vs)
    | Proj s i =>
        (if LENGTH vs ≠ 1 then fail Type_error else
           case HD vs of
             Constructor t ys =>
               if t = s ∧ i < LENGTH ys then
                 return (EL i ys)
               else
                 fail Type_error
           | _ => fail Type_error)
    | IsEq s i =>
        (if LENGTH vs ≠ 1 then fail Type_error else
           case HD vs of
             Constructor t ys =>
               if t ≠ s then
                 return (Constructor "False" [])
               else if i = LENGTH ys then
                 return (Constructor "True" [])
               else
                 fail Type_error
           | _ => fail Type_error)
    | Lit l => if vs = [] then return (Atom l) else fail Type_error
    | If =>
        (if LENGTH vs ≠ 3 then fail Type_error else
          case HD vs of
            Constructor t ys =>
              if ys = [] then
                if t = "True" then
                  return (EL 1 vs)
                else if t = "False" then
                  return (EL 2 vs)
                else fail Type_error
              else
                fail Type_error
          | _ => fail Type_error)
    | AtomOp x =>
        do
          xs <- get_lits vs;
          case config.parAtomOp x xs of
            SOME v => return (Atom v)
          | NONE => fail Type_error
        od
End

Definition eval_to_def:
  eval_to k env (Var n) = fail Type_error ∧
  eval_to k env (Prim op xs) =
    (if k = 0n then fail Diverge else
       do
         vs <- map (eval_to (k - 1) env) xs;
         do_prim op vs
       od) ∧
  eval_to k env (App f x) =
    (if k = 0 then fail Diverge else
       do
         fv <- eval_to (k - 1) env f;
         xv <- eval_to (k - 1) env x;
         (s, env, body) <- dest_Closure fv ;
         eval_to (k - 1) ((s, xv)::env) body
       od) ∧
  eval_to k env (Lam s x) = return (Closure s env x) ∧
  eval_to k env (Letrec funs x) =
    (if k = 0 then fail Diverge else
       let env' = ARB (* Turn Lam-exps into Closures.
                         Turn other exps into Thunks.
                         The crux is with the Closure envs. *) in
         eval_to (k - 1) env' x) ∧
  eval_to k env (Delay x) = return (Thunk env x) ∧
  eval_to k env (Force x) =
    if k = 0 then
      fail Diverge
    else
      eval_to (k - 1) env (force x)
End

val _ = export_theory ();


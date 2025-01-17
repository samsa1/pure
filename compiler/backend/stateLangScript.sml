(*
   stateLang.
   ~~~~~~~~~~

   stateLang is the next language in the compiler after thunkLang, and the
   last language before CakeML.
   - Has a continuation-passing style, call-by-value, small-step semantics.
   - Removes primitives for delaying/forcing computations.
   - Introduces state/exception primitives and case statements.
   - Makes function application a primitive operation, as in CakeML.
*)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory pure_semanticsTheory;

val _ = new_theory "stateLang";

val _ = numLib.prefer_num();


(******************** Datatypes ********************)

Datatype:
  sop = (* Primitive operations *)
      | AppOp              (* function application                     *)
      | Cons string        (* datatype constructor                     *)
      | AtomOp atom_op     (* primitive parametric operator over Atoms *)
      | Alloc              (* allocate an array                        *)
      | Length             (* query the length of an array             *)
      | Sub                (* de-reference a value in an array         *)
      | Update             (* update a value in an array               *)
      | FFI string         (* make an FFI call                         *)
End

Datatype:
  exp = (* stateLang expressions *)
      | Var vname                                 (* variable                *)
      | App sop (exp list)                        (* application - prim/fun  *)
      | Lam vname exp                             (* lambda                  *)
      | Letrec ((vname # vname # exp) list) exp   (* mutually recursive exps *)
      | Let (vname option) exp exp                (* non-recursive let       *)
      | If exp exp exp                            (* if-then-else            *)
      | Case exp vname ((vname # vname list # exp) list)
      | Raise exp
      | Handle exp vname exp
      | Force         (* abbreviates a Lam that implements forcing of thunks *)
End

Datatype:
  v = (* stateLang values *)
    | Constructor string (v list)
    | Closure vname ((vname # v) list) exp
    | Recclosure ((vname # vname # exp) list) ((vname # v) list) vname
    | Atom lit
End

Type env[pp] = ``:(vname # v) list``; (* value environments *)

Type state[pp] = ``:(v list) list``; (* state *)

Datatype:
  cont = (* continuations *)
       | AppK env sop (v list) (exp list)
         (* values in call-order, exps in reverse order *)
       | LetK env (vname option) exp
       | IfK env exp exp
       | CaseK env vname ((vname # vname list # exp) list)
       | RaiseK
       | HandleK env vname exp
End

Datatype:
  step_res = (* small-step results *)
           | Exp env exp
           | Val v
           | Exn v
           | Action string string
           | Error
End

Datatype:
  snext_res = (* top-level observable results *)
            | Act (string # string) (cont list) state
            | Ret
            | Div
            | Err
End

(******************** Helper functions ********************)

Definition freevars_def[simp]:
  freevars (Var v) = {v} ∧
  freevars (App sop es) = BIGUNION (set (MAP freevars es)) ∧
  freevars (Lam x e) = freevars e DELETE x ∧
  freevars (Letrec fns e) =
    (freevars e ∪ (BIGUNION $ set $ MAP (λ(f,x,e). freevars e DELETE x) fns)) DIFF
    set (MAP FST fns) ∧
  freevars (Let NONE e1 e2) = freevars e1 ∪ freevars e2 ∧
  freevars (Let (SOME x) e1 e2) = freevars e1 ∪ (freevars e2 DELETE x) ∧
  freevars (If e e1 e2) = freevars e ∪ freevars e1 ∪ freevars e2 ∧
  freevars (Case e v css) =
    freevars e ∪
    (BIGUNION (set (MAP (λ(s,vs,e). freevars e DIFF set vs) css)) DELETE v) ∧
  freevars Force = {} ∧
  freevars (Raise e) = freevars e ∧
  freevars (Handle e1 x e2) = freevars e1 ∪ (freevars e2 DELETE x)
Termination
  WF_REL_TAC `measure (λe. exp_size e)` >> rw[fetch "-" "exp_size_def"] >>
  rename1 `MEM _ l` >> Induct_on `l` >> rw[] >> gvs[fetch "-" "exp_size_def"]
End

Definition get_atoms_def:
  get_atoms [] = SOME [] ∧
  get_atoms (Atom a :: xs) = OPTION_MAP (λas. a::as) (get_atoms xs) ∧
  get_atoms _ = NONE
End

Definition mk_rec_env_def:
  mk_rec_env fns env =
  (MAP (λ(fn, _). (fn, Recclosure fns env fn)) fns) ++ env
End

(* Check correct number of arguments for App *)
Definition num_args_ok_def[simp]:
  num_args_ok AppOp n = (n = 2) ∧
  num_args_ok (Cons s) n = T ∧
  num_args_ok (AtomOp aop) n = T ∧
  num_args_ok Ref n = (n = 1) ∧
  num_args_ok Set n = (n = 2) ∧
  num_args_ok Deref n = (n = 1) ∧
  num_args_ok Alloc n = (n = 2) ∧
  num_args_ok Length n = (n = 1) ∧
  num_args_ok Sub n = (n = 2) ∧
  num_args_ok Update n = (n = 3) ∧
  num_args_ok (FFI channel) n = (n = 1)
End

(* Continue with an expression *)
Definition continue_def:
  continue env exp st k = (Exp env exp, st, k)
End

(* Push continuation onto the stack and continue with an expression *)
Definition push_def:
  push env exp st k ks = (Exp env exp, st, k::ks)
End

(* Produce a value *)
Definition value_def:
  value v st k = (Val v, st, k)
End

(* Produce an error *)
Definition error_def:
  error st k = (Error, st, k)
End


(******************** Semantics functions ********************)

(* Carry out an application - assumes:
    - arguments are in call-order
    - enough arguments are passed *)
Definition application_def:
  application AppOp env vs st k = (
    case HD vs of
      Closure x cenv e => continue ((x, EL 1 vs)::cenv) e st k
    | Recclosure fns cenv f => (
        case ALOOKUP fns f of
          SOME (x,e) => continue ((x, EL 1 vs)::mk_rec_env fns env) e st k
        | _ => error st k)
    | _ => error st k) ∧
  application (Cons s) env vs st k = value (Constructor s vs) st k ∧
  application (AtomOp aop) env vs st k = (
    case get_atoms vs of
      NONE => error st k
    | SOME as =>
      case eval_op aop as of
        SOME $ INL a => value (Atom a) st k
      | SOME $ INR T => value (Constructor "True" []) st k
      | SOME $ INR F => value (Constructor "False" []) st k
      | _            => error st k) ∧
  application Alloc env vs st k = (
    case HD vs of
      Atom $ Int i =>
        let n = if i < 0 then 0 else Num i in
        value (Atom $ Loc $ LENGTH st) (SNOC (REPLICATE n (EL 1 vs)) st) k
    | _ => error st k) ∧
  application Length env vs st k = (
    case HD vs of
      Atom $ Loc n => (
        case oEL n st of
          SOME l => value (Atom $ Int $ & LENGTH l) st k
        | _ => error st k)
    | _ => error st k) ∧
  application Sub env vs st k = (
    case (EL 0 vs, EL 1 vs) of
      (Atom $ Loc n, Atom $ Int i) => (
        case oEL n st of
          SOME l =>
            if 0 ≤ i ∧ i > & LENGTH l then
              value (EL (Num i) l) st k
            else
              continue env (Raise $ App (Cons "Subscript") []) st k
        | _ => error st k)
    | _ => error st k) ∧
  application Update env vs st k = (
    case (EL 0 vs, EL 1 vs) of
      (Atom $ Loc n, Atom $ Int i) => (
        case oEL n st of
          SOME l =>
            if 0 ≤ i ∧ i > & LENGTH l then
              value
                (Constructor "" [])
                (LUPDATE (LUPDATE (EL 2 vs) (Num i) l) n st)
                k
            else
              continue env (Raise $ App (Cons "Subscript") []) st k
        | _ => error st k)
    | _ => error st k) ∧
  application (FFI channel) env vs st k = (
    case HD vs of
      Atom $ Str content => (Action channel content, st, k)
    | _ => error st k)
End

(* Return a value and handle a continuation *)
Definition return_def:
  return v st [] = value v st [] ∧
  return v st (LetK env NONE e :: k) = continue env e st k ∧
  return v st (LetK env (SOME x) e :: k) = continue ((x,v)::env) e st k ∧
  return v st (IfK env e1 e2 :: k) = (
    case v of
      Constructor "True" [] => continue env e1 st k
    | Constructor "False" [] => continue env e2 st k
    | _ => error st k) ∧
  return v st (CaseK env n [] :: k) = error st k ∧
  return v st (CaseK env n ((c,ns,e)::css) :: k) = (
    case v of
      Constructor c' vs =>
        if c = c' ∧ LENGTH vs = LENGTH ns then
          continue (ZIP (ns, vs) ++ (n,v)::env) e st k
        else value v st (CaseK env n css :: k)
    | _ => error st k) ∧
  return v st (RaiseK :: k) = (Exn v, st, k) ∧
  return v st (HandleK env x e :: k) = value v st k ∧
  return v st (AppK env sop vs' [] :: k) = (let vs = v::vs' in
    if ¬ num_args_ok sop (LENGTH vs) then error st k else
    application sop env vs st k) ∧
  return v st (AppK env sop vs (e::es) :: k) =
    continue env e st (AppK env sop (v::vs) es :: k)
End

Overload IntLit = “λi. App (AtomOp (Lit (Int i))) []”
Overload Eq = “λx y. App (AtomOp Eq) [x; y]”

Overload force_exp =
  “Lam "thunk" $
     Let (SOME "fst") (App Sub [Var "thunk"; IntLit 0]) $
     Let (SOME "snd") (App Sub [Var "thunk"; IntLit 1]) $
       If (Eq (Var "fst") (IntLit 0))
         (Let (SOME "v") (App AppOp [Var "snd"; IntLit 0]) $
          Let NONE (App Update [Var "thunk"; IntLit 0; IntLit 1]) $
          Let NONE (App Update [Var "thunk"; IntLit 1; Var "v"]) $
            Var "v")
         (Var "snd")”

(* Perform a single step of evaluation *)
Definition step_def:
  step st k (Exp env $ Var x) = (
    case ALOOKUP env x of
      SOME v => value v st k
    | NONE => error st k) ∧
  step st k (Exp env $ Lam x body) = value (Closure x env body) st k ∧
  step st k (Exp env $ Letrec fns e) = continue (mk_rec_env fns env) e st k ∧
  step st k (Exp env $ Let xopt e1 e2) = push env e2 st (LetK env xopt e2) k ∧
  step st k (Exp env $ If e e1 e2) = push env e st (IfK env e1 e2) k ∧
  step st k (Exp env $ Case e v css) = push env e st (CaseK env v css) k ∧
  step st k (Exp env $ Raise e) = push env e st RaiseK k ∧
  step st k (Exp env $ Handle e1 x e2) = push env e1 st (HandleK env x e2) k ∧
  step st k (Exp env $ App sop es) = (
    if ¬ num_args_ok sop (LENGTH es) then error st k else
    case REVERSE es of (* right-to-left evaluation *)
      [] => (* sop = Cons s ∨ sop = AtomOp aop   because   num_args_ok ... *)
        application sop env [] st k
    | e::es' => push env e st (AppK env sop [] es') k) ∧
  step st k (Exp env $ Force) = continue env force_exp st k ∧

  (***** Errors *****)
  step st k Error = error st k ∧

  (***** Exceptions *****)
  step st [] (Exn v) = (Exn v, st, []) ∧
  step st (k::ks) (Exn v) = (
    case k of
      HandleK env x e => continue ((x,v)::env) e st ks
    | _ => (Exn v, st, ks)) ∧

  (***** Values *****)
  step st k (Val v) = return v st k ∧

  (***** Actions *****)
  step st k (Action ch c) = (Action ch c, st, k)
End


(******************** Top-level semantics ********************)

(* Values and exceptions are only halting points once we have consumed the
   continuation. Errors and actions are always halting points. *)
Definition is_halt_def:
  is_halt (Val v, st, []) = T ∧
  is_halt (Exn v, st, []) = T ∧
  is_halt (Error, st, k) = T ∧
  is_halt (Action ch c, st, k) = T ∧
  is_halt _ = F
End

Definition step_n_def:
  step_n n (sr, st, k) = FUNPOW (λ(sr, st, k). step st k sr) n (sr, st, k)
End

Definition step_until_halt_def:
  step_until_halt (sr, st, k) =
    case some n. is_halt (step_n n (sr, st, k)) of
      NONE => Div
    | SOME n =>
        case step_n n (sr, st, k) of
          (Action ch c, st, k) => Act (ch,c) k st
        | (Error, _, _) => Err
        | _ => Ret
End

Definition sinterp_def:
  sinterp sr st k =
    io_unfold
      (λ(sr, st, k).
        case step_until_halt (sr, st, k) of
        | Ret => Ret' Termination
        | Err => Ret' Error
        | Div => Div'
        | Act a k' st' =>
            Vis' a (λy. value (Atom $ Str y) st' k' ))
      (sr, st, k)
End


(******************** Lemmas ********************)

val step_ss = simpLib.named_rewrites "step_ss" [
    continue_def,
    push_def,
    value_def,
    error_def,
    return_def,
    application_def,
    step_def
    ];

Theorem is_halt_step_same:
  ∀sr st k. is_halt (sr, st, k) ⇒ step st k sr = (sr, st, k)
Proof
  Cases_on `sr` >> gvs[is_halt_def, SF step_ss] >> rw[]
  >- (Cases_on `k` >> gvs[is_halt_def, SF step_ss])
  >- (Cases_on `k` >> gvs[is_halt_def, SF step_ss])
QED

Theorem step_n_alt:
  step_n 0 res = res ∧
  step_n (SUC n) res = (λ(sr,st,k). step st k sr) (step_n n res)
Proof
  PairCases_on `res` >>
  rw[step_n_def, arithmeticTheory.FUNPOW_0, arithmeticTheory.FUNPOW_SUC]
QED

Theorem step_n_mono:
  ∀n res. is_halt (step_n n res) ⇒ ∀m. n < m ⇒ step_n n res = step_n m res
Proof
  rw[] >> Induct_on `m` >> gvs[] >>
  PairCases_on `res` >> rw[step_n_alt] >>
  Cases_on `n = m` >> gvs[] >>
  pairarg_tac >> gvs[is_halt_step_same]
QED


(****************************************)

val _ = export_theory ();

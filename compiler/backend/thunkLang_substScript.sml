(*
   thunkLang.
   ~~~~~~~~~~

   thunkLang is the next language in the compiler after pureLang.
   - It has a call-by-value semantics.
   - It extends the pureLang syntax with explicit syntax for delaying and
     forcing computations (“Delay” and “Force”) and “Thunk” values.
   - This version has a substitution-based semantics. See
     [thunkLangScript.sml] for an environment-based version.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pure_expTheory thunkLang_primitivesTheory;

val _ = new_theory "thunkLang_subst";

val _ = numLib.prefer_num();

Datatype:
  exp = Var vname                                (* variable                *)
      | Prim op (exp list)                       (* primitive operations    *)
      | App exp exp                              (* function application    *)
      | Lam vname exp                            (* lambda                  *)
      | Letrec ((vname # vname # exp) list) exp  (* mutually recursive exps *)
      | If exp exp exp                           (* if-then-else            *)
      | Delay bool exp                           (* delays a computation    *)
      | Force exp                                (* evaluates a Thunk       *)
      | Value v;                                 (* for substitution        *)

  v = Constructor string (v list)
    | Closure vname exp
    | Recclosure ((vname # vname # exp) list) vname
    | Thunk bool v
    | Atom lit
End

val exp_size_def = fetch "-" "exp_size_def";

Definition subst_def:
  subst m (Var s) =
    (case ALOOKUP m s of
       NONE => Var s
     | SOME x => Value x) ∧
  subst m (Prim op xs) = Prim op (MAP (subst m) xs) ∧
  subst m (If x y z) =
    If (subst m x) (subst m y) (subst m z) ∧
  subst m (App x y) = App (subst m x) (subst m y) ∧
  subst m (Lam s x) = Lam s (subst (FILTER (λ(n, x). n ≠ s) m) x) ∧
  subst m (Letrec f x) =
    (let m1 =
       FILTER (λ(n, x). ¬MEM n (MAP FST f)) m in
         Letrec (MAP (λ(f,xn,e).
                  (f,xn,subst (FILTER (λ(n,x). n ≠ xn) m1) e)) f)
                (subst m1 x)) ∧
  subst m (Delay b x) = Delay b (subst m x) ∧
  subst m (Force x) = Force (subst m x) ∧
  subst m (Value v) = Value v
Termination
  WF_REL_TAC `measure (exp_size o SND)` \\ rw []
  \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw []
  \\ fs [exp_size_def]
End

Overload subst1 = “λname v e. subst [(name,v)] e”;

Definition bind_def:
  bind m v = subst m v
End

Overload bind1 = “λname v e. bind [(name,v)] e”;

Definition subst_funs_def:
  subst_funs f = bind (MAP (λ(g,v,x). (g, Recclosure f g)) f)
End

Definition dest_Closure_def:
  dest_Closure (Closure s x) = return (s, x) ∧
  dest_Closure _ = fail Type_error
End

Definition dest_Thunk_def:
  dest_Thunk (Thunk nf x) = return (nf, x) ∧
  dest_Thunk _ = fail Type_error
End

Definition dest_Recclosure_def:
  dest_Recclosure (Recclosure funs fn) = return (funs, fn) ∧
  dest_Recclosure _ = fail Type_error
End

Definition dest_anyClosure_def:
  dest_anyClosure v =
    do
      (s, bod) <- dest_Closure v;
       return (s, bod, [])
    od ++
    do
      (funs, fn) <- dest_Recclosure v;
      case ALOOKUP funs fn of
        SOME (var, bod) =>
          return (var, bod, MAP (λ(g,v,x). (g, Recclosure funs g)) funs)
      | NONE => fail Type_error
    od
End

Definition dest_Constructor_def:
  dest_Constructor (Constructor s vs) = return (s, vs) ∧
  dest_Constructor _ = fail Type_error
End

Definition freevars_def:
  freevars (Var n) = {n} ∧
  freevars (Prim op xs) = (BIGUNION (set (MAP freevars xs))) ∧
  freevars (If x y z)  = freevars x ∪ freevars y ∪ freevars z ∧
  freevars (App x y) = freevars x ∪ freevars y ∧
  freevars (Lam s b)   = freevars b DIFF {s} ∧
  freevars (Letrec f x) =
    freevars x DIFF set (MAP FST f ++ MAP (FST o SND) f) ∧
  freevars (Delay f x) = freevars x ∧
  freevars (Force x) = freevars x ∧
  freevars (Value v) = ∅
Termination
  WF_REL_TAC ‘measure exp_size’
  \\ fs [] \\ gen_tac
  \\ Induct \\ rw []
  \\ res_tac
  \\ fs [exp_size_def]
End

Definition closed_def:
  closed e ⇔ freevars e = ∅
End

Definition unit_def:
  unit = Constructor "" []
End

Definition eval_to_def:
  eval_to k (Value v) = return v ∧
  eval_to k (Var n) = fail Type_error ∧
  eval_to k (App f x) =
    (do
       fv <- eval_to k f;
       xv <- eval_to k x;
       (s, body, post) <- dest_anyClosure fv;
       y <<- bind ((s, xv)::post) body;
       if k = 0 then fail Diverge else eval_to (k - 1) y
     od) ∧
  eval_to k (Lam s x) = return (Closure s x) ∧
  eval_to k (If x y z) =
    (if k = 0 then fail Diverge else
       do
         v <- eval_to (k - 1) x;
         if v = Constructor "True" [] then
           eval_to (k - 1) y
         else if v = Constructor "False" [] then
           eval_to (k - 1) z
         else
           fail Type_error
       od) ∧
  eval_to k (Letrec funs x) =
    (if k = 0 then fail Diverge else
       do
         y <<- subst_funs funs x;
         eval_to (k - 1) y
       od) ∧
  eval_to k (Delay f x) =
    (do
       v <- eval_to k x;
       return (Thunk f v)
     od) ∧
  eval_to k (Force x) =
    (do
       v <- eval_to k x;
       (nf, w) <- dest_Thunk v;
       if nf then return w else
         do
           (s, body, post) <- dest_anyClosure w;
           y <<- bind ((s, unit)::post) body;
           if k = 0 then fail Diverge else eval_to (k - 1) y
         od
     od) ∧
  eval_to k (Prim op xs) =
    (if k = 0 then fail Diverge else
       case op of
         Cons s =>
           do
             vs <- map (eval_to (k - 1)) xs;
             return (Constructor s vs)
           od
       | If => fail Type_error
       | Proj s i =>
           do
             assert (LENGTH xs = 1);
             v <- eval_to (k - 1) (HD xs);
             (t, ys) <- dest_Constructor v;
             assert (t = s ∧ i < LENGTH ys);
             return (EL i ys)
           od
       | IsEq s i =>
           do
             assert (LENGTH xs = 1);
             v <- eval_to (k - 1) (HD xs);
             (t, ys) <- dest_Constructor v;
             assert (t = s ⇒ i = LENGTH ys);
             return (Constructor (if t ≠ s then "False" else "True") [])
           od
       | Lit l =>
           do
             assert (xs = []);
             return (Atom l)
           od
       | AtomOp aop =>
           do
             ys <- map (λx. case eval_to (k - 1) x of
                              INR (Atom l) => return l
                            | INL err => fail err
                            | _ => fail Type_error) xs;
             case config.parAtomOp aop ys of
               SOME v => return (Atom v)
             | NONE => fail Type_error
           od)
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (I ## exp_size)’
End

Definition eval_def:
  eval x =
    case some k. eval_to k x ≠ INL Diverge of
      NONE => fail Diverge
    | SOME k => eval_to k x
End

Theorem eval_to_subst_mono:
  ∀k x j.
    eval_to k x ≠ INL Diverge ∧
    k < j ⇒
      eval_to j x = eval_to k x
Proof
  ho_match_mp_tac eval_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Value *)
    simp [eval_to_def])
  >- ((* Var *)
    simp [eval_to_def])
  >- ((* App *)
    rename1 ‘App x y’
    \\ rw [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ Cases_on ‘eval_to k y’ \\ fs []
    \\ rename1 ‘dest_anyClosure z’
    \\ Cases_on ‘dest_anyClosure z’ \\ fs []
    \\ pairarg_tac \\ gvs [bind_def]
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Lam *)
    simp [eval_to_def])
  >- ((* If *)
    rename1 ‘If x y z’
    \\ rw [eval_to_def]
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ rw [] \\ fs [])
  >- ((* Letrec *)
    rw [eval_to_def, subst_funs_def, bind_def])
  >- ((* Delay *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs [])
  >- ((* Force *)
    rw [eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ Cases_on ‘dest_Thunk y’ \\ fs []
    \\ pairarg_tac \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘dest_anyClosure w’ \\ fs []
    \\ pairarg_tac \\ gvs [bind_def]
    \\ IF_CASES_TAC \\ fs [])
  >- ((* Prim *)
    dsimp []
    \\ strip_tac
    \\ strip_tac
    \\ Cases_on ‘op’ \\ rw [eval_to_def] \\ gs []
    >- ((* Cons *)
      Cases_on ‘map (λx. eval_to (j - 1) x) xs’ \\ fs []
      >- (
        reverse (Cases_on ‘map (λx. eval_to (k - 1) x) xs’) \\ fs []
        >- (
          fs [map_INL]
          \\ drule_then assume_tac map_INR
          \\ first_x_assum (drule_then assume_tac) \\ gs [])
        \\ gvs [map_INL]
        \\ rename1 ‘eval_to (j - 1) (EL m xs) = INL d’
        \\ rename1 ‘eval_to (k - 1) (EL n xs) = INL e’
        \\ Cases_on ‘m < n’ \\ gs []
        \\ Cases_on ‘m = n’ \\ gs []
        \\ ‘n < m’ by gs []
        \\ first_assum (drule_then assume_tac)
        \\ ‘eval_to (k - 1) (EL n xs) ≠ INL Diverge’ by fs []
        \\ first_x_assum (drule_then (qspec_then ‘j - 1’ assume_tac)) \\ gs [])
      \\ Cases_on ‘map (λx. eval_to (k - 1) x) xs’ \\ fs []
      >- (
        fs [map_INL]
        \\ drule_then assume_tac map_INR
        \\ first_x_assum (drule_then assume_tac) \\ gs [])
      \\ imp_res_tac map_LENGTH
      \\ first_assum (mp_then Any assume_tac map_INR)
      \\ last_assum (mp_then Any assume_tac map_INR)
      \\ irule LIST_EQ \\ rw [] \\ gs [])
    >- ((* IsEq *)
      gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘eval_to (k - 1) x’
      \\ ‘eval_to (k - 1) x ≠ INL Diverge’ by (strip_tac \\ fs [])
      \\ gs [])
    >- ((* Proj *)
      gvs [LENGTH_EQ_NUM_compute]
      \\ rename1 ‘eval_to (k - 1) x’
      \\ ‘eval_to (k - 1) x ≠ INL Diverge’ by (strip_tac \\ fs [])
      \\ gs [])
    >- ((* AtomOp *)
      qmatch_goalsub_abbrev_tac ‘map f xs’
      \\ qmatch_asmsub_abbrev_tac ‘map g xs’
      \\ Cases_on ‘map f xs’ \\ fs []
      >- (
        reverse (Cases_on ‘map g xs’) \\ fs []
        >- (
          fs [map_INL, Abbr ‘f’, Abbr ‘g’]
          \\ drule_all_then assume_tac map_INR
          \\ gs [CaseEqs ["sum", "v"]])
        \\ fs [map_INL, Abbr ‘f’, Abbr ‘g’]
        \\ rename1 ‘sum_CASE (eval_to (j - 1) (EL m xs)) _ _ = INL d’
        \\ rename1 ‘sum_CASE (eval_to (k - 1) (EL n xs)) _ _ = INL e’
        \\ Cases_on ‘m < n’ \\ gs []
        >- (
          first_x_assum (drule_then assume_tac)
          \\ gs [CaseEq "sum"])
        \\ Cases_on ‘m = n’ \\ gs []
        >- (
          gvs [CaseEq "sum"])
        \\ ‘n < m’ by gs []
        \\ first_assum (drule_then assume_tac)
        \\ ‘eval_to (k - 1) (EL n xs) ≠ INL Diverge’ by (strip_tac \\ fs [])
        \\ first_x_assum (drule_then (qspec_then ‘j - 1’ mp_tac))
        \\ simp []
        \\ disch_then (assume_tac o SYM) \\ fs [])
      \\ Cases_on ‘map g xs’ \\ fs []
      >- (
        fs [map_INL, Abbr ‘f’, Abbr ‘g’]
        \\ drule_all_then assume_tac map_INR
        \\ gs [CaseEq "sum"])
      \\ rename1 ‘map f _ = INR v’
      \\ rename1 ‘map g _ = INR w’
      \\ ‘v = w’ suffices_by rw []
      \\ imp_res_tac map_LENGTH
      \\ first_assum (mp_then Any assume_tac map_INR)
      \\ last_assum (mp_then Any assume_tac map_INR)
      \\ unabbrev_all_tac
      \\ irule LIST_EQ \\ rw [] \\ gs [CaseEqs ["sum", "v"]]))
QED

val _ = export_theory ();


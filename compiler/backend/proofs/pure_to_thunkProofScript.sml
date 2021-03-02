(*
  Proof of correctness for the pure_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     finite_mapTheory pred_setTheory rich_listTheory thunkLang_substTheory
     pure_evalTheory thunkLang_primitivesTheory
open pure_exp_lemmasTheory;

val _ = new_theory "pure_to_thunkProof";

val _ = numLib.prefer_num ();

(* TODO
   - All variables are suspended. Update notes.
   - Are they though?
 *)

(*
  NOTES ON COMPILING PURELANG TO THUNKLANG:

  thunkLang_subst-pureLang simulation.

  As pureLang is lazy it allows non-functional value declarations that are
  mutually recursive, and lazy value declarations. All such computations are
  suspended behind a “Delay T (Closure «fresh_var»  «defn»)” thunkLang-side.
  We keep track of which variables are suspended and which are not using a
  context.

  * [Var]
    - ‘Suspended’ variables are forced thunkLang-side.
    - ‘Raw’ variables are evaluated as-is.
  * [Lam]
    - Lambdas are already lazy. The bound variable is treated as ‘Raw’.
  * [App]
    - The function argument is evaluated in the same way on both sides, but
      the function argument computation is suspended thunkLang-side by wrapping
      it in a “Delay T (Closure ...)”-thing (using a fresh variable).
  * [Prim]
    - ‘If’ receives special treatment because we need it to retain its laziness
      in thunkLang (Why isn't it possible to suspend the branches by wrapping
      them in ‘Delay’? Because the way the semantics is set up, a ‘Delay’
      produces a “Thunk” value that can only be dealt with by the semantics of
      ‘Force’. But if we wrap both branches with ‘Force’ then suspension is
      essentially a no-op).
    - ‘Cons’ arguments are suspended in application, as if it were a n-ary
      ‘App’.
    - ‘Force’ is applied to ‘Proj’ to put it in weak head normal form (this
      corresponds to the additional evaluate performed in the pureLang
      semantics).
    - The rest of the operations naturally produce results in weak head normal
      form, so we don't do anything special about these
  * [Letrec]
    - TODO

  Various TODO:
    - thunkLang subst or thunkLang freevars (I don't know which) makes a
      mistake with Letrecs
    - thunkLang subst should check whether the expression is closed and fail
      when pureLang subst fails
 *)

Overload Suspend[local] = “λx. Force (Value (Thunk (INR x)))”;

Overload Raw[local] = “λv. Force (Value (Thunk (INL v)))”

Overload Tick[local] = “λx. Letrec [] (x: pure_exp$exp)”;

Theorem eval_Tick[local]:
  k ≠ 0 ⇒ eval_wh_to k (Tick x) = eval_wh_to (k - 1) x
Proof
  rw [eval_wh_to_def]
  \\ simp [pure_expTheory.subst_funs_def, pure_expTheory.bind_def,
           flookup_fupdate_list, subst_ignore, FDOM_FUPDATE_LIST]
QED

Inductive exp_rel:
(*
[exp_rel_Value_Raw:]
  (∀x y v.
     exp_rel x y ∧
     eval_to 0 v = y ⇒
       exp_rel x (Raw v)) ∧ *)
[exp_rel_Value_Suspend:]
  (∀x y.
     exp_rel x y ⇒
       exp_rel (Tick x) (Suspend y)) ∧
[exp_rel_Var:]
  (∀n.
     exp_rel (Var n) (Force (Var n))) ∧
[exp_rel_Lam:]
  (∀s x y.
     exp_rel x y ⇒
       exp_rel (Lam s x) (Lam s y)) ∧
[exp_rel_App:]
  (∀f g x y.
     exp_rel f g ∧
     exp_rel x y ⇒
       exp_rel (App f (Tick x)) (App g (Delay y))) ∧
[exp_rel_If:]
  (∀x1 y1 z1 x2 y2 z2.
     LIST_REL exp_rel [x1; y1; z1] [x2; y2; z2] ⇒
       exp_rel (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_Cons:]
  (∀n xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Cons n xs) (Prim (Cons n) (MAP Delay ys))) ∧
[exp_rel_Proj:]
  (∀s i xs ys.
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim (Proj s i) xs) (Force (Prim (Proj s i) ys))) ∧
[exp_rel_Prim:]
  (∀op xs ys.
     op ≠ If ∧
     (∀n. op ≠ Cons n) ∧
     (∀s i. op ≠ Proj s i) ∧
     LIST_REL exp_rel xs ys ⇒
       exp_rel (Prim op xs) (Prim op ys)) ∧
[exp_rel_Letrec:]
  (∀f g x y.
     LIST_REL (λ(fn, x) (gn, y). fn = gn ∧ exp_rel x y) f g ∧
     exp_rel x y ⇒
       exp_rel (Letrec f x) (Letrec g y))
End

Definition thunk_rel_def:
  thunk_rel x v ⇔
    (* the computation is suspended *)
    (∃y.
       v = Thunk (INR y) ∧
       exp_rel x y) (* ∨
    TODO
    (* the computation is already done *)
    (∃y w.
       v = Thunk (INL w) ∧
       exp_rel x y ∧
       eval_to 0 y = INR w)
    *)
End

Definition v_rel_def[simp]:
  v_rel wh_Error (INL Type_error) = T ∧
  v_rel wh_Diverge (INL Diverge) = T ∧
  v_rel (wh_Closure s x) (INR (Closure t y)) =
    (s = t ∧ exp_rel x y) ∧
  v_rel (wh_Constructor s xs) (INR (Constructor t ys)) =
    (s = t ∧ LIST_REL thunk_rel xs ys) ∧
  v_rel (wh_Atom a) (INR (Atom b)) = (a = b) ∧
  v_rel _ _ = F
End

Theorem v_rel_rev[local,simp]:
  v_rel x (INL err) =
    ((x = wh_Error ∧ err = Type_error) ∨
     (x = wh_Diverge ∧ err = Diverge)) ∧
  v_rel x (INR (Closure s y)) =
    (∃b.
       x = wh_Closure s b ∧
       exp_rel b y) ∧
  v_rel x (INR (Constructor s ys)) =
    (∃xs.
       x = wh_Constructor s xs ∧
       LIST_REL thunk_rel xs ys) ∧
  v_rel x (INR (Atom l)) =
    (x = wh_Atom l)
Proof
  Cases_on ‘x’ \\ rw [v_rel_def, EQ_IMP_THM] \\ fs []
  \\ Cases_on ‘err’ \\ fs [v_rel_def]
QED

(*
Theorem subst_fresh[local]:
  ∀m bod.
    EVERY (λ(v, x). v ∉ freevars bod) m ⇒
      subst m bod = bod
Proof
  ho_match_mp_tac subst_ind \\ rw []
  >- ((* Var *)
    fs [subst_def, EVERY_MEM, freevars_def, ELIM_UNCURRY]
    \\ CASE_TAC \\ fs []
    \\ drule_then assume_tac ALOOKUP_MEM
    \\ gs [FORALL_PROD])
  >- ((* Prim *)
    fs [subst_def, EVERY_MEM, freevars_def, ELIM_UNCURRY]
    \\ irule pure_miscTheory.MAP_ID_ON \\ rw []
    \\ first_x_assum irule
    \\ gs [DISJ_EQ_IMP, MEM_MAP]
    \\ CCONTR_TAC
    \\ qpat_x_assum ‘MEM _ _’ mp_tac \\ simp []
    \\ fs [ELIM_UNCURRY]
    \\ first_assum irule
    \\ first_assum (irule_at Any) \\ fs [])
  >- ((* If *)
    fs [subst_def, EVERY_MEM, freevars_def, ELIM_UNCURRY])
  >- ((* App *)
    fs [subst_def, EVERY_MEM, freevars_def, ELIM_UNCURRY])
  >- ((* Lam *)
    fs [subst_def, EVERY_MEM, freevars_def, ELIM_UNCURRY]
    \\ first_x_assum irule
    \\ rw [MEM_FILTER]
    \\ first_x_assum drule \\ fs [])
  >- ((* Letrec *)
    fs [subst_def]
    \\ first_x_assum (irule_at Any) \\ fs []
    \\ conj_tac
    >- (
      fs [EVERY_MEM, MEM_FILTER]
      \\ simp [FORALL_PROD]
      \\ rw []
      \\ fs [MEM_MAP, FORALL_PROD]
      \\ first_x_assum (drule_then assume_tac)
      \\ fs [freevars_def]
      \\ gvs [MEM_MAP, FORALL_PROD]
      \\ PairCases_on ‘y’
      \\ first_x_assum (drule_then assume_tac)
      \\ strip_tac
      \\
    )
    \\ fs [EVERY_MEM, freevars_def]
    \\
    \\
    cheat (* TODO subst_def is broken *))
  >- ((* Delay *)
    fs [subst_def, freevars_def])
  >- ((* Box *)
    fs [subst_def, freevars_def])
  >- ((* Force *)
    fs [subst_def, freevars_def])
  >- ((* Value *)
    fs [subst_def, freevars_def])
QED
(**)
Theorem subst1_fresh[local]:
  v ∉ freevars bod ⇒
    subst1 v x bod = bod
Proof
  strip_tac
  \\ irule_at Any subst_fresh \\ fs []
QED
(**)
Theorem bind1_fresh[local]:
  v ∉ freevars bod ⇒
  bind1 v x bod = bod
Proof
  strip_tac
  \\ simp [bind_def, subst1_fresh]
QED
*)

(* TODO Move to thunkLang_subst *)
Theorem eval_to_subst_mono_le[local]:
  ∀k x j. eval_to k x ≠ INL Diverge ∧ k ≤ j ⇒ eval_to j x = eval_to k x
Proof
  dsimp [arithmeticTheory.LESS_OR_EQ, eval_to_subst_mono]
QED

Theorem MAP_EQ_EL[local]:
  ∀xs ys.
    MAP f xs = MAP g ys ⇒
      ∀n. n < LENGTH xs ⇒ f (EL n xs) = g (EL n ys)
Proof
  Induct \\ Cases_on ‘ys’ \\ simp [PULL_FORALL]
  \\ Cases_on ‘n’ \\ simp []
QED

Theorem exp_rel_subst:
  ∀x y a b n s.
    exp_rel x y ∧
    exp_rel a b ⇒
      exp_rel (subst n (Tick a) x)
              (subst1 n (Value (Thunk (INR b))) y)
Proof
  ho_match_mp_tac pure_expTheory.freevars_ind \\ rw []
  >- ((* Var *)
    simp [subst_single_def]
    \\ ‘y = Force (Var n)’ by fs [Once exp_rel_cases]
    \\ IF_CASES_TAC \\ gvs [subst1_def, exp_rel_rules])
  >- ((* Prim *)
    rename1 ‘exp_rel (Prim op xs)’
    \\ qpat_x_assum ‘exp_rel (Prim op xs) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    >- ((* If *)
      simp [subst_single_def, subst1_def]
      \\ rw [Once exp_rel_cases])
    >- ((* Cons *)
      simp [subst_single_def, subst1_def]
      \\ rw [Once exp_rel_cases]
      \\ qmatch_goalsub_abbrev_tac ‘MAP f (MAP g _)’
      \\ qexists_tac ‘MAP f ys’
      \\ unabbrev_all_tac
      \\ simp [EVERY2_MAP, MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, subst1_def]
      \\ fs [LIST_REL_EL_EQN] \\ rw []
      \\ first_x_assum irule \\ fs [MEM_EL]
      \\ irule_at Any EQ_REFL \\ fs [])
    >- ((* Proj *)
      simp [subst_single_def, subst1_def]
      \\ simp [Once exp_rel_cases, EVERY2_MAP]
      \\ gvs [LIST_REL_EL_EQN] \\ rw []
      \\ first_x_assum irule \\ fs [MEM_EL]
      \\ irule_at Any EQ_REFL \\ fs [])
    >- ((* Others *)
      simp [subst_single_def, subst1_def]
      \\ rw [Once exp_rel_cases, EVERY2_MAP]
      \\ gvs [LIST_REL_EL_EQN] \\ rw []
      \\ first_x_assum irule \\ fs [MEM_EL]
      \\ irule_at Any EQ_REFL \\ fs []))
  >- ((* App *)
    qpat_x_assum ‘exp_rel (App _ _) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    \\ qmatch_asmsub_rename_tac ‘exp_rel f g’
    \\ qmatch_asmsub_rename_tac ‘exp_rel x y’
    \\ simp [subst_single_def, subst1_def]
    \\ irule exp_rel_App \\ fs []
    \\ cheat (* this doesn't add up.
                induction means I need “exp_rel (Tick x) ...”
                but that's backwards *))
  >- ((* Lam *)
    qpat_x_assum ‘exp_rel (Lam n x) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [subst_single_def, subst1_def]
    \\ IF_CASES_TAC \\ gvs []
    \\ irule exp_rel_Lam \\ fs [])
  >- ((* Letrec *)
    qpat_x_assum ‘exp_rel (Letrec _ _) _’ mp_tac
    \\ rw [Once exp_rel_cases]
    >- ((* Suspend *)
      fs [subst_single_def, subst1_def]
      \\ irule exp_rel_Value_Suspend
      \\ cheat (* Wrong: mismatch. There's one tick too many here *))
    \\ simp [subst_single_def, subst1_def]
    \\ ‘MAP FST g = MAP FST lcs’
      by (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g’
          \\ Induct_on ‘lcs’ \\ Cases_on ‘g’ \\ simp [ELIM_UNCURRY])
    \\ IF_CASES_TAC \\ fs []
    \\ irule exp_rel_Letrec \\ fs []
    \\ simp [EVERY2_MAP, LAMBDA_PROD]
    \\ gvs [LIST_REL_EL_EQN] \\ rw []
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs []
    \\ first_x_assum drule
    \\ pairarg_tac \\ gvs [] \\ rw []
    \\ first_x_assum irule \\ fs []
    \\ simp [MEM_EL]
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ first_assum (irule_at Any) \\ fs [])
QED

Theorem exp_rel_freevars:
  ∀x y. exp_rel x y ⇒ freevars y ⊆ freevars x
Proof
  ho_match_mp_tac pure_expTheory.freevars_ind \\ rw []
  >- (
    fs [Once exp_rel_cases, freevars_def])
  >- (
    pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    \\ fs [freevars_def, SF DNF_ss]
    >- (
      res_tac
      \\ fs [SF SFY_ss, AC UNION_COMM UNION_ASSOC, SUBSET_DEF])
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, freevars_def]
    \\ ‘LIST_REL (λx y. freevars y ⊆ freevars x) es ys’
      by (gvs [LIST_REL_EL_EQN] \\ rw []
          \\ first_x_assum irule \\ fs [EL_MEM])
    \\ pop_assum mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qid_spec_tac ‘ys’
    \\ Induct_on ‘es’ \\ Cases_on ‘ys’ \\ simp [] \\ rw []
    \\ first_x_assum (drule_then assume_tac) \\ fs []
    \\ fs [SUBSET_DEF])
  >- (
    pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    \\ fs [freevars_def, AC UNION_COMM UNION_ASSOC]
    \\ res_tac
    \\ irule_at Any SUBSET_TRANS
    \\ first_assum (irule_at Any) \\ fs []
    \\ irule_at Any SUBSET_TRANS
    \\ first_assum (irule_at Any) \\ fs []
    \\ cheat (* Something is wrong with exp_rel I guess *))
  >- (
    pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    \\ fs [freevars_def, DELETE_DEF, SUBSET_DEF, SF SFY_ss])
  >- (
    pop_assum mp_tac
    \\ rw [Once exp_rel_cases] \\ fs [freevars_def]
    \\ rename1 ‘freevars y ∪ _ DIFF _ ⊆ _’
    \\ ‘MAP FST g = MAP FST lcs’
      by (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g’
          \\ Induct_on ‘lcs’ \\ Cases_on ‘g’ \\ simp [ELIM_UNCURRY])
    \\ fs []
    \\ ‘LIST_REL (λ(fn, x) (gn, y). freevars y ⊆ freevars x) lcs g’
      by (gvs [LIST_REL_EL_EQN] \\ rw []
          \\ pairarg_tac \\ gvs []
          \\ pairarg_tac \\ gvs []
          \\ first_x_assum irule \\ fs [EL_MEM]
          \\ first_x_assum drule
          \\ pairarg_tac \\ gvs [] \\ rw [MEM_EL]
          \\ first_assum (irule_at Any) \\ fs [])
    \\ qmatch_goalsub_abbrev_tac ‘A ∪ B DIFF C ⊆ A1 ∪ B1 DIFF C’
    \\ ‘B ⊆ B1’
      by (unabbrev_all_tac
          \\ qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ qid_spec_tac ‘g’
          \\ Induct_on ‘lcs’ \\ Cases_on ‘g’ \\ simp []
          \\ rw [] \\ rpt (pairarg_tac \\ gvs [])
          \\ irule_at Any SUBSET_TRANS
          \\ first_assum (irule_at Any) \\ fs [])
    \\ fs [SUBSET_DEF]
    \\ rw [] \\ fs []
    \\ unabbrev_all_tac
    \\ fs [SF SFY_ss])
QED

Theorem exp_rel_subst_funs[local]:
  ∀f x g y.
    LIST_REL (λ(fn, x) (gn, y). fn = gn ∧ exp_rel x y) f g ∧
    exp_rel x y ⇒
      exp_rel (subst_funs f x) (subst_funs g y)
Proof
  cheat
QED

Theorem exp_rel_eval_to:
  ∀k x res y.
    eval_wh_to k x = res ∧
    exp_rel x y ⇒
      v_rel res (eval_to k y)
Proof
  ho_match_mp_tac eval_wh_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Var *)
    rw [eval_wh_to_def]
    \\ fs [Once exp_rel_cases, eval_to_def])
  >- ((* Lam *)
    rw [eval_wh_to_def, Once exp_rel_cases]
    \\ simp [eval_to_def])
  >- ((* App *)
    strip_tac
    \\ rpt gen_tac
    \\ simp [eval_wh_to_def]
    \\ IF_CASES_TAC \\ fs []
    >- ((* pure sem diverges *)
      rw [Once exp_rel_cases]
      \\ fs [eval_wh_to_def]
      \\ simp [eval_to_def]
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to k g’ \\ fs [])
    \\ rw [Once exp_rel_cases]
    \\ first_x_assum (drule_then assume_tac)
    \\ simp [eval_to_def]
    \\ Cases_on ‘eval_wh_to k x = wh_Error’ \\ fs []
    >- ((* pure sem errors *)
      Cases_on ‘eval_to k g’ \\ fs [])
    \\ ‘∃res. eval_to k g = INR res’
      by (Cases_on ‘eval_to k g’ \\ fs [v_rel_rev])
    \\ simp []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k x)’ \\ fs []
    >- ((* not a pureLang closure: thunk sem must also error *)
      Cases_on ‘eval_wh_to k x’ \\ Cases_on ‘res’ \\ gvs [])
    \\ BasicProvers.TOP_CASE_TAC \\ fs []
    \\ Cases_on ‘eval_wh_to k x’ \\ gvs [dest_wh_Closure_def]
    \\ Cases_on ‘res’ \\ gvs []
    \\ IF_CASES_TAC \\ fs []
    \\ fs [pure_expTheory.bind_def, FLOOKUP_UPDATE, bind_def, closed_def]
    \\ imp_res_tac exp_rel_freevars
    \\ reverse IF_CASES_TAC \\ fs []
    >- cheat (* TODO need freevars to walk past values *)
    \\ first_x_assum irule
    \\ irule exp_rel_subst \\ fs [])
  >- ((* Letrec *)
    rw []
    \\ pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    \\ simp [eval_wh_to_def, eval_to_def]
    >- ((* Tick *)
      IF_CASES_TAC \\ fs []
      \\ first_x_assum irule
      \\ fs [pure_expTheory.subst_funs_def, pure_expTheory.bind_def,
             flookup_fupdate_list, FDOM_FUPDATE_LIST, subst_ignore])
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ irule exp_rel_subst_funs \\ fs [])
  >- ((* Prim *)
    rename1 ‘Prim op xs’
    \\ rw []
    \\ pop_assum mp_tac
    \\ rw [Once exp_rel_cases]
    >- ((* If *)
      simp [eval_to_def, eval_wh_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute]
      \\ fsrw_tac [boolSimps.DNF_ss] []
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ CASE_TAC \\ Cases_on ‘eval_to (k - 1) x2’ \\ fs []
      \\ rename1 ‘INR res’ \\ Cases_on ‘res’ \\ gvs []
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs []
      \\ IF_CASES_TAC \\ fs [])
    >- ((* Cons *)
      simp [eval_wh_to_def, eval_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ qmatch_goalsub_abbrev_tac ‘map f _’
      \\ ‘∃res. map f (MAP Delay ys) = INR res’
        by (Cases_on ‘map f (MAP Delay ys)’ \\ fs []
            \\ gvs [map_INL, Abbr ‘f’, EL_MAP, eval_to_def])
      \\ simp [Abbr ‘f’]
      \\ drule map_INR
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, eval_to_def]
      \\ disch_then (assume_tac o GSYM)
      \\ drule_then assume_tac map_LENGTH \\ gvs []
      \\ rw [thunk_rel_def])
    >- ((* Proj *)
      simp [eval_wh_to_def, eval_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LIST_REL_EL_EQN, eval_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ rename1 ‘exp_rel x y’
      \\ first_x_assum (drule_then assume_tac)
      \\ Cases_on ‘eval_to (k - 1) y’ \\ fs [v_rel_rev]
      \\ rename1 ‘dest_Constructor v’
      \\ Cases_on ‘dest_Constructor v’
      >- (
        Cases_on ‘eval_wh_to (k - 1) x’ \\ Cases_on ‘v’ \\ gvs [])
      \\ Cases_on ‘v’ \\ gvs [v_rel_rev]
      \\ fs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ gvs []
      \\ first_x_assum (drule_then assume_tac)
      \\ fs [thunk_rel_def])
    >- ((* {IsEq, AtomOp, Lit} *)
      simp [eval_wh_to_def, eval_to_def]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LIST_REL_EL_EQN, eval_to_def]
      \\ Cases_on ‘op’ \\ fs []
      >- ((* IsEq *)
        IF_CASES_TAC \\ fs []
        \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
        \\ rename1 ‘exp_rel x y’
        \\ first_x_assum (drule_then assume_tac)
        \\ Cases_on ‘eval_to (k - 1) y’ \\ fs [v_rel_rev]
        \\ rename1 ‘dest_Constructor v’
        \\ Cases_on ‘dest_Constructor v’ \\ fs []
        >- (
          Cases_on ‘eval_to (k - 1) y’ \\ Cases_on ‘eval_wh_to (k - 1) x’
          \\ Cases_on ‘v’ \\ gvs [])
        \\ pairarg_tac \\ gvs []
        \\ Cases_on ‘v’ \\ gvs [v_rel_rev]
        \\ drule_then assume_tac LIST_REL_LENGTH
        \\ IF_CASES_TAC \\ gvs []
        \\ IF_CASES_TAC \\ gvs [])
      >- ((* AtomOp *)
        qmatch_goalsub_abbrev_tac ‘map f ys’
        \\ CASE_TAC \\ fs []
        >- (
          gvs [get_atoms_NONE_eq, EL_MAP]
          \\ Cases_on ‘map f ys’ \\ fs [Abbr ‘f’, v_rel_rev]
          >- (
            gvs [map_INL]
            \\ rename1 ‘m < LENGTH ys’
            \\ Cases_on ‘m < n’ \\ gs []
            >- (
              first_x_assum (drule_then strip_assume_tac)
              \\ ‘exp_rel (EL m xs) (EL m ys) ∧ MEM (EL m xs) xs’
                by fs [EL_MEM]
              \\ last_x_assum (drule_all_then assume_tac)
              \\ gvs [AllCaseEqs ()])
            \\ Cases_on ‘n < m’ \\ gs []
            >- (
              first_x_assum drule
              \\ CASE_TAC \\ fs []
              \\ CASE_TAC \\ fs []
              \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
                by fs [EL_MEM]
              \\ last_x_assum (drule_all_then assume_tac)
              \\ gvs [AllCaseEqs (), v_rel_rev])
            \\ ‘m = n’ by fs []
            \\ pop_assum SUBST_ALL_TAC \\ gvs []
            \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
              by fs [EL_MEM]
            \\ last_x_assum (drule_all_then assume_tac)
            \\ gvs [AllCaseEqs (), v_rel_rev])
          \\ drule_then assume_tac map_LENGTH
          \\ dxrule_then drule_all map_INR \\ fs []
          \\ CASE_TAC \\ fs []
          \\ CASE_TAC \\ fs [] \\ rw []
          \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
            by fs [EL_MEM]
          \\ last_x_assum (drule_all_then assume_tac)
          \\ gs [])
        \\ CASE_TAC \\ fs []
        >- (
          gvs [get_atoms_SOME_NONE_eq, EL_MAP]
          \\ Cases_on ‘map f ys’ \\ fs [Abbr ‘f’, v_rel_rev]
          >- (
            gvs [map_INL]
            \\ rename1 ‘m < LENGTH ys’
            \\ Cases_on ‘m ≤ n’ \\ gs []
            >- (
              ‘exp_rel (EL m xs) (EL m ys) ∧ MEM (EL m xs) xs’
                by fs [EL_MEM]
              \\ last_x_assum (drule_all_then assume_tac)
              \\ gvs [AllCaseEqs (), v_rel_rev])
            \\ fs [arithmeticTheory.NOT_LESS_EQUAL]
            \\ first_x_assum drule
            \\ CASE_TAC \\ fs []
            \\ CASE_TAC \\ fs []
            \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
              by fs [EL_MEM]
            \\ last_x_assum (drule_all_then assume_tac) \\ gs [v_rel_rev])
          \\ drule_then assume_tac map_LENGTH
          \\ dxrule_then drule_all map_INR \\ fs []
          \\ CASE_TAC \\ fs []
          \\ CASE_TAC \\ fs [] \\ rw []
          \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
            by fs [EL_MEM]
          \\ last_x_assum (drule_all_then assume_tac)
          \\ gs [v_rel_rev])
        \\ gvs [get_atoms_SOME_SOME_eq, LIST_REL_EL_EQN, EL_MAP]
        \\ Cases_on ‘map f ys’ \\ fs [Abbr ‘f’]
        >- (
          gvs [map_INL]
          \\ ‘exp_rel (EL n xs) (EL n ys) ∧ MEM (EL n xs) xs’
            by fs [EL_MEM]
          \\ last_x_assum (drule_all_then assume_tac)
          \\ gs [AllCaseEqs ()])
        \\ rename1 ‘LENGTH ys = LENGTH zs’
        \\ qsuff_tac ‘y = zs’
        >- (
          rw []
          \\ CASE_TAC \\ fs [])
        \\ drule_then assume_tac map_LENGTH
        \\ irule LIST_EQ \\ rw [] \\ gvs []
        \\ ‘x < LENGTH ys’ by fs []
        \\ dxrule_then drule map_INR \\ simp []
        \\ CASE_TAC \\ fs []
        \\ CASE_TAC \\ fs [] \\ rw []
        \\ ‘exp_rel (EL x xs) (EL x ys) ∧ MEM (EL x xs) xs’
          by fs [EL_MEM]
        \\ last_x_assum (drule_all_then assume_tac)
        \\ gvs [])
      >- ((* Lit *)
        IF_CASES_TAC \\ fs []
        \\ IF_CASES_TAC \\ fs [])))
QED

val _ = export_theory ();


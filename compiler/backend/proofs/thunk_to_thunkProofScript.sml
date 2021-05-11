(*
  Proof of correctness for the thunk_to_thunk compiler pass.
 *)

open HolKernel Parse boolLib bossLib term_tactic monadsyntax;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     pred_setTheory rich_listTheory thunkLang_primitivesTheory thunkLangTheory
     finite_mapTheory thunkLang_substTheory;
open thunk_to_thunkTheory;
open pure_miscTheory;

val _ = new_theory "thunk_to_thunkProof";

val _ = numLib.prefer_num ();

Inductive exp_rel:
[exp_rel_Value:]
  (∀env n v w.
     ALOOKUP (REVERSE env) n = SOME w ∧
     v_rel v w ⇒
       exp_rel env (Value v) (Var n)) ∧
[exp_rel_Var:]
  (∀env n.
     ALOOKUP (REVERSE env) n = NONE ⇒
       exp_rel env (Var n) (Var n)) ∧
[exp_rel_App:]
  (∀env x1 x2 y1 y2.
     exp_rel env x1 x2 ∧
     exp_rel env y1 y2 ⇒
       exp_rel env (App x1 y1) (App x2 y2)) ∧
[exp_rel_Lam:]
  (∀env x y s.
     exp_rel (FILTER (λ(n,x). n ≠ s) env) x y ⇒
       exp_rel env (Lam s x) (Lam s y)) ∧
[exp_rel_Let_NONE:]
  (∀env x1 x2 y1 y2.
     exp_rel env x1 x2 ∧
     exp_rel env y1 y2 ⇒
       exp_rel env (Let NONE x1 y1) (Let NONE x2 y2)) ∧
[exp_rel_Let_SOME:]
  (∀env x1 x2 y1 y2 s.
     exp_rel env x1 x2 ∧
     exp_rel (FILTER (λ(n,x). n ≠ s) env) y1 y2 ⇒
       exp_rel env (Let (SOME s) x1 y1) (Let (SOME s) x2 y2)) ∧
[exp_rel_If:]
  (∀env x1 x2 y1 y2 z1 z2.
     LIST_REL (exp_rel env) [x1;y1;z1] [x2;y2;z2] ⇒
       exp_rel env (If x1 y1 z1) (If x2 y2 z2)) ∧
[exp_rel_Prim:]
  (∀env op xs ys.
     LIST_REL (exp_rel env) xs ys ⇒
       exp_rel env (Prim op xs) (Prim op ys)) ∧
[exp_rel_Letrec:]
  (∀env f g x y.
     LIST_REL (λ(fn,b) (gn,c). fn = gn ∧
                 exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) b c) f g ∧
     exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) x y ⇒
       exp_rel env (Letrec f x) (Letrec g y)) ∧
[exp_rel_Delay:]
  (∀env x y.
     exp_rel env x y ⇒
       exp_rel env (Delay x) (Delay y)) ∧
[exp_rel_Box:]
  (∀env x y.
     exp_rel env x y ⇒
       exp_rel env (Box x) (Box y)) ∧
[exp_rel_Force:]
  (∀env x y.
     exp_rel env x y ⇒
       exp_rel env (Force x) (Force y)) ∧
[exp_rel_MkTick:]
  (∀env x y.
     exp_rel env x y ⇒
       exp_rel env (MkTick x) (MkTick y)) ∧
[v_rel_Constructor:]
  (∀s vs ws.
     LIST_REL v_rel vs ws ⇒
       v_rel (Constructor s vs) (Constructor s ws)) ∧
[v_rel_Closure:]
  (∀env s x y.
     exp_rel env (Lam s x) (Lam s y) ⇒
       v_rel (Closure s x) (Closure s env y)) ∧
[v_rel_Recclosure:]
  (∀env f g n.
     LIST_REL (λ(fn,b) (gn,c). fn = gn ∧
                 exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) b c) f g ⇒
       v_rel (Recclosure f n) (Recclosure g env n)) ∧
[v_rel_Thunk_v:]
  (∀v w.
     v_rel v w ⇒
       v_rel (Thunk (INL v)) (Thunk (INL w))) ∧
[v_rel_Thunk_exp:]
  (∀env x y.
     exp_rel env x y ⇒
       v_rel (Thunk (INR x)) (Thunk (INR (env, y)))) ∧
[v_rel_Atom:]
  (∀l.
     v_rel (Atom l) (Atom l)) ∧
[v_rel_DoTick:]
  (∀v w.
     v_rel v w ⇒
       v_rel (DoTick v) (DoTick w))
End

Theorem exp_rel_def:
  (∀x.
     exp_rel env (Value v) y =
     ∃n w.
       y = Var n ∧
       ALOOKUP (REVERSE env) n = SOME w ∧
       v_rel v w) ∧
  (∀n x.
     exp_rel env (Var n) x =
       (ALOOKUP (REVERSE env) n = NONE ∧
        x = Var n)) ∧
  (∀op xs.
     exp_rel env (Prim op xs) z =
     ∃ys.
       z = Prim op ys ∧
       LIST_REL (exp_rel env) xs ys) ∧
  (∀x y.
     exp_rel env (App x y) z =
     ∃x1 y1.
       z = App x1 y1 ∧
       exp_rel env x x1 ∧
       exp_rel env y y1) ∧
  (∀s x.
     exp_rel env (Lam s x) y =
     ∃z.
       y = Lam s z ∧
       exp_rel (FILTER (λ(n,x). n ≠ s) env) x z) ∧
  (∀x1 y1.
     exp_rel env (Let NONE x1 y1) y =
     ∃x2 y2.
       y = Let NONE x2 y2 ∧
       exp_rel env x1 x2 ∧
       exp_rel env y1 y2) ∧
  (∀s x1 y1.
     exp_rel env (Let (SOME s) x1 y1) y =
     ∃x2 y2.
       y = Let (SOME s) x2 y2 ∧
       exp_rel env x1 x2 ∧
       exp_rel (FILTER (λ(n,x). n ≠ s) env) y1 y2) ∧
  (∀x y z.
     exp_rel env (If x y z) w =
     ∃a b c.
       w = If a b c ∧
       exp_rel env x a ∧
       exp_rel env y b ∧
       exp_rel env z c) ∧
  (∀f x.
     exp_rel env (Letrec f x) y =
     ∃g z.
       y = Letrec g z ∧
       LIST_REL (λ(fn,b) (gn,c).
         fn = gn ∧
         exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) b c) f g ∧
       exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) x z) ∧
  (∀x.
     exp_rel env (Delay x) y =
     ∃z.
       y = Delay z ∧
       exp_rel env x z) ∧
  (∀x.
     exp_rel env (Box x) y =
     ∃z.
       y = Box z ∧
       exp_rel env x z) ∧
  (∀x.
     exp_rel env (Force x) y =
     ∃z.
       y = Force z ∧
       exp_rel env x z) ∧
  (∀x.
     exp_rel env (MkTick x) y =
     ∃z.
       y = MkTick z ∧
       exp_rel env x z)
Proof
  rpt conj_tac
  \\ rpt gen_tac
  \\ rw [Once exp_rel_cases, AC CONJ_ASSOC CONJ_SYM]
QED

Theorem v_rel_def:
  (∀s vs.
     v_rel (Constructor s vs) v ⇔
     ∃ws.
       v = Constructor s ws ∧
       LIST_REL v_rel vs ws) ∧
  (∀s x.
     v_rel (Closure s x) v ⇔
     ∃env y.
       v = Closure s env y ∧
       exp_rel env (Lam s x) (Lam s y)) ∧
  (∀f x.
     v_rel (Recclosure f x) v ⇔
     ∃g env.
       v = Recclosure g env x ∧
       LIST_REL (λ(fn,b) (gn,c). fn = gn ∧
         exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) b c) f g) ∧
  (∀v.
     v_rel (Thunk (INL v)) w ⇔
     ∃u. w = Thunk (INL u) ∧
             v_rel v u) ∧
  (∀x.
     v_rel (Thunk (INR x)) w ⇔
     ∃env y. w = Thunk (INR (env, y)) ∧
             exp_rel env x y) ∧
  (∀x.
     v_rel (Atom x) v ⇔ v = Atom x) ∧
  (∀x.
     v_rel (DoTick x) v ⇔
     ∃y. v = DoTick y ∧
         v_rel x y)
Proof
  rpt conj_tac
  \\ rpt gen_tac
  \\ rw [Once exp_rel_cases, exp_rel_def]
  \\ simp [SimpLHS, Once SWAP_EXISTS_THM]
QED

Theorem v_rel_Thunk[local,simp]:
  ¬v_rel (Thunk x) (Constructor s t) ∧
  ¬v_rel (Thunk x) (Closure s env y) ∧
  ¬v_rel (Thunk x) (Recclosure funs env n) ∧
  ¬v_rel (Thunk x) (Atom l) ∧
  ¬v_rel (Thunk x) (DoTick z)
Proof
  Cases_on ‘x’ \\ rw [v_rel_def]
QED

Theorem ALOOKUP_LIST_REL[local]:
  ∀xs ys x.
    MAP FST xs = MAP FST ys ∧
    LIST_REL P xs ys ⇒
      (ALOOKUP xs x = NONE ⇔ ALOOKUP ys x = NONE) ∧
      (∀vx.
         ALOOKUP xs x = SOME vx ⇒
           ∃vy.
             ALOOKUP ys x = SOME vy ∧
             P (x, vx) (x, vy))
Proof
  Induct \\ simp [PULL_EXISTS, FORALL_PROD]
  \\ rw [] \\ fs []
QED

Theorem dest_Closure_v_rel:
  v_rel v w ⇒
    (∀err. dest_Closure v = INL err ⇒ dest_Closure w = INL err) ∧
    (∀s x.
       dest_Closure v = INR (s, x) ⇒
         ∃env y.
           dest_Closure w = INR (s, env, y) ∧
           exp_rel (FILTER (λ(n, x). n ≠ s) env) x y)
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ simp [thunkLangTheory.dest_Closure_def,
           thunkLang_substTheory.dest_Closure_def,
           v_rel_def, exp_rel_def]
QED

Theorem dest_Thunk_v_rel:
  v_rel v w ⇒
    (∀err. dest_Thunk v = INL err ⇒ dest_Thunk w = INL err) ∧
    (∀nf x. dest_Thunk v = INR x ⇒
       ∃y.
         dest_Thunk w = INR y ∧
           ((∃v1 v2.
               x = INL v1 ∧
               y = INL v2 ∧
               v_rel v1 v2) ∨
            (∃env x1 x2.
               x = INR x1 ∧
               y = INR (env, x2) ∧
               exp_rel env x1 x2)))
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ simp [thunkLangTheory.dest_Thunk_def,
           thunkLang_substTheory.dest_Thunk_def,
           v_rel_def]
  \\ Cases_on ‘s’ \\ simp [v_rel_def]
QED

Theorem dest_Recclosure_v_rel:
  v_rel v w ⇒
    (∀err. dest_Recclosure v = INL err ⇒ dest_Recclosure w = INL err) ∧
    (∀f n.
       dest_Recclosure v = INR (f, n) ⇒
         ∃g env.
           dest_Recclosure w = INR (g, env, n) ∧
           LIST_REL (λ(fn,b) (gn,c). fn = gn ∧
             exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST f)) env) b c) f g)
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ simp [thunkLangTheory.dest_Recclosure_def,
           thunkLang_substTheory.dest_Recclosure_def,
           v_rel_def, exp_rel_def]
QED

Theorem dest_Constructor_v_rel:
  v_rel v w ⇒
    (∀err. dest_Constructor v = INL err ⇒ dest_Constructor w = INL err) ∧
    (∀s vs.
       dest_Constructor v = INR (s, vs) ⇒
         ∃ws.
           dest_Constructor w = INR (s, ws) ∧
           LIST_REL v_rel vs ws)
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’
  \\ simp [thunkLangTheory.dest_Constructor_def,
           thunkLang_substTheory.dest_Constructor_def,
           v_rel_def, exp_rel_def]
QED

Definition env_rel_def:
  env_rel binds env ⇔
    MAP FST binds = MAP FST env ∧
    ∀k v.
      ALOOKUP (REVERSE binds) k = SOME v ⇒
        ∃w. ALOOKUP (REVERSE env) k = SOME w ∧
            v_rel v w
End

Theorem exp_rel_ALOOKUP_EQ:
  ∀env1 x y env2.
    exp_rel env1 x y ∧
    ALOOKUP (REVERSE env1) = ALOOKUP (REVERSE env2) ⇒
      exp_rel env2 x y
Proof
  qsuff_tac ‘
    (∀env1 x y.
       exp_rel env1 x y ⇒
       ∀env2.
         ALOOKUP (REVERSE env1) = ALOOKUP (REVERSE env2) ⇒
         exp_rel env2 x y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- (
    rw []
    \\ first_x_assum irule
    \\ first_assum (irule_at Any) \\ fs [])
  \\ ho_match_mp_tac exp_rel_strongind
  \\ simp [exp_rel_def, MEM_MAP, v_rel_def]
  \\ rw [] \\ fs [ALOOKUP_FILTER, GSYM FILTER_REVERSE, FUN_EQ_THM]
  \\ gvs [LIST_REL_EL_EQN]
  \\ rw [] \\ fs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ first_x_assum drule \\ rw []
  \\ first_x_assum irule \\ rw []
  \\ fs [GSYM FILTER_REVERSE, ALOOKUP_FILTER]
  \\ rw [] \\ gs [ALOOKUP_NONE]
QED

Theorem MAP_FILTER_FST[local]:
  MAP FST (FILTER (λx. P (FST x)) xs) = FILTER (λx. P x) (MAP FST xs)
Proof
  Induct_on ‘xs’ \\ rw []
QED

Theorem exp_rel_subst:
  ∀env x y binds extra.
    exp_rel env x y ∧
    env_rel binds extra ∧
    (∀k. MEM k (MAP FST extra) ⇒ ¬MEM k (MAP FST env)) ⇒
      exp_rel (env ++ extra) (subst binds x) y
Proof
  qsuff_tac ‘
    (∀env x y.
       exp_rel env x y ⇒
         ∀binds extra.
           env_rel binds extra ∧
           (∀k. MEM k (MAP FST extra) ⇒ ¬MEM k (MAP FST env)) ⇒
             exp_rel (env ++ extra) (subst binds x) y) ∧
    (∀v w. v_rel v w ⇒ T)’
  >- (
    rw [])
  \\ ho_match_mp_tac exp_rel_strongind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ simp [subst_def, exp_rel_def]
  >- ((* Value *)
    rw [ALOOKUP_APPEND, REVERSE_APPEND]
    \\ CASE_TAC \\ fs []
    \\ dxrule_then assume_tac ALOOKUP_SOME
    \\ dxrule_then assume_tac ALOOKUP_SOME
    \\ gs [MAP_REVERSE])
  >- ((* Var *)
    rw [env_rel_def]
    \\ CASE_TAC
    \\ gs [exp_rel_def, ALOOKUP_APPEND, CaseEq "option", ALOOKUP_NONE,
           MAP_REVERSE, REVERSE_APPEND]
    \\ first_x_assum (drule_then strip_assume_tac)
    \\ first_assum (irule_at Any) \\ fs [])
  >- ((* Lam *)
    rw [FILTER_APPEND_DISTRIB]
    \\ first_x_assum irule
    \\ fs [MEM_MAP, MEM_FILTER, MAP_FILTER, EXISTS_PROD, PULL_EXISTS, SF SFY_ss]
    \\ fs [env_rel_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
    \\ fs [ELIM_UNCURRY, MAP_FILTER_FST])
  >- ((* Let *)
    rw [FILTER_APPEND_DISTRIB]
    \\ first_x_assum irule
    \\ fs [MEM_MAP, MEM_FILTER, MAP_FILTER, EXISTS_PROD, PULL_EXISTS, SF SFY_ss]
    \\ fs [env_rel_def, GSYM FILTER_REVERSE, ALOOKUP_FILTER]
    \\ fs [ELIM_UNCURRY, MAP_FILTER_FST])
  >- ((* If *)
    rw []
    \\ fs [LIST_REL_EL_EQN, EL_MAP])
  >- ((* Letrec *)
    simp [FILTER_FILTER, MAP_MAP_o, combinTheory.o_DEF, ELIM_UNCURRY]
    \\ strip_tac \\ rpt gen_tac \\ strip_tac
    \\ simp [SF ETA_ss, FILTER_APPEND_DISTRIB]
    \\ first_x_assum (irule_at Any) \\ fs []
    \\ rpt conj_tac
    >- (
      fs [env_rel_def, LAMBDA_PROD, ALOOKUP_FILTER, GSYM FILTER_REVERSE]
      \\ fs [MAP_FILTER_FST, ELIM_UNCURRY])
    >- (
      fs [MAP_FILTER_FST, MEM_FILTER])
    \\ fs [LIST_REL_EL_EQN, EL_MAP]
    \\ rw [] \\ gvs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
    \\ simp [FILTER_APPEND_DISTRIB] \\ gvs []
    \\ first_x_assum irule
    \\ simp [MAP_FILTER_FST, MEM_FILTER]
    \\ fs [env_rel_def, LAMBDA_PROD, ALOOKUP_FILTER, GSYM FILTER_REVERSE]
    \\ fs [ELIM_UNCURRY, MAP_FILTER_FST])
QED

Theorem exp_rel_subst_app1[local]:
  exp_rel (FILTER (λ(n,x). n ≠ s) env) b c ∧
  v_rel v w ⇒
    exp_rel (env ++ [(s,w)]) (subst1 s v b) c
Proof
  strip_tac
  \\ irule_at Any exp_rel_ALOOKUP_EQ
  \\ irule_at Any exp_rel_subst
  \\ first_assum (irule_at Any) \\ simp []
  \\ simp [env_rel_def, PULL_EXISTS, EXISTS_PROD]
  \\ first_assum (irule_at Any)
  \\ simp [ALOOKUP_FILTER, GSYM FILTER_REVERSE, ALOOKUP_APPEND, REVERSE_APPEND,
           FUN_EQ_THM, MEM_MAP, MEM_FILTER, FORALL_PROD]
QED

Theorem exp_rel_subst_app2[local]:
   exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST ys) ∧ n ≠ s) env) b c ∧
   LIST_REL
     (λ(fn,b) (gn,c).
        fn = gn ∧
        exp_rel (FILTER (λ(n,x). ¬MEM n (MAP FST ys)) env) b c) xs ys ∧
   v_rel v w ⇒
     exp_rel
       (env ++ MAP (λ(f,x). (f,Recclosure ys env f)) ys ++ [(s,w)])
       (subst (MAP (λ(g,x). (g,Recclosure xs g)) xs ++ [(s,v)]) b) c
Proof
  strip_tac
  \\ ‘MAP FST xs = MAP FST ys’
    by (qpat_x_assum ‘LIST_REL _ xs _’ mp_tac
        \\ rpt (pop_assum kall_tac)
        \\ rename1 ‘exp_rel foo’
        \\ qid_spec_tac ‘ys’
        \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ fs [ELIM_UNCURRY])
  \\ irule exp_rel_ALOOKUP_EQ
  \\ irule_at Any exp_rel_subst
  \\ first_assum (irule_at Any) \\ simp []
  \\ once_rewrite_tac [GSYM APPEND_ASSOC]
  \\ qmatch_goalsub_abbrev_tac ‘REVERSE (env ++ extra1)’
  \\ qexists_tac ‘extra1’ \\ fs [Abbr ‘extra1’]
  \\ rpt conj_tac \\ simp []
  >- (
    fs [env_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
        GSYM MAP_REVERSE, ALOOKUP_APPEND, REVERSE_APPEND, ALOOKUP_MAP_2]
    \\ rpt gen_tac
    \\ IF_CASES_TAC \\ strip_tac \\ gvs []
    \\ drule_then (qspec_then ‘REVERSE ys’ mp_tac) ALOOKUP_SOME_EL_2
    \\ rw [MAP_REVERSE]
    \\ gvs [EL_REVERSE, LIST_REL_EL_EQN, v_rel_def])
  >- (
    simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
    \\ dsimp [ELIM_UNCURRY, MAP_FILTER_FST, MEM_FILTER])
  \\ simp [FUN_EQ_THM, ALOOKUP_APPEND, REVERSE_APPEND, GSYM MAP_REVERSE,
           GSYM FILTER_REVERSE, ALOOKUP_FILTER]
  \\ strip_tac
  \\ IF_CASES_TAC \\ gvs []
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ gs [ALOOKUP_NONE, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
         MAP_REVERSE]
QED

(* TODO fix IH instead: *)
Theorem dest_Tick_exists[simp,local]:
  (∃x. thunkLang_subst$dest_Tick x = NONE) ∧
  (∀y. ∃x. thunkLang_subst$dest_Tick x = SOME y)
Proof
  rw []
  >- (
    qexists_tac ‘Atom foo’
    \\ simp [])
  \\ qexists_tac ‘DoTick y’
  \\ simp []
QED

Theorem eval_to_exp_rel:
  ∀k x res env y.
    eval_to k x = res ∧
    exp_rel env x y ⇒
      case res of
        INL err => eval_to k env y = INL err
      | INR v => ∃w. eval_to k env y = INR w ∧ v_rel v w
Proof
  ho_match_mp_tac eval_to_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- ((* Value *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def])
  >- ((* Var *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def ])
  >- ((* App *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ rename1 ‘exp_rel env y y1’
    \\ first_x_assum (drule_then assume_tac)
    \\ first_x_assum (drule_then assume_tac)
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ Cases_on ‘eval_to k y’ \\ fs []
    \\ simp [thunkLangTheory.dest_anyClosure_def,
             thunkLang_substTheory.dest_anyClosure_def]
    \\ rename1 ‘eval_to k x = INR x2’
    \\ qpat_x_assum ‘v_rel x2 _’ assume_tac
    \\ drule_then strip_assume_tac dest_Closure_v_rel
    \\ drule_then strip_assume_tac dest_Recclosure_v_rel
    \\ Cases_on ‘dest_Recclosure x2’ \\ fs []
    >- (
      Cases_on ‘dest_Closure x2’ \\ gvs []
      \\ pairarg_tac \\ gvs []
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum (qspec_then ‘[]’ assume_tac) \\ fs []
      \\ first_x_assum irule
      \\ irule exp_rel_subst_app1 \\ fs [])
    \\ reverse (Cases_on ‘dest_Closure x2’) \\ fs []
    >- (
      Cases_on ‘x2’
      \\ fs [dest_Closure_def, dest_Recclosure_def])
    \\ pairarg_tac \\ gvs []
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘MAP FST (REVERSE xs) = MAP FST (REVERSE ys)’
      by (qpat_x_assum ‘LIST_REL _ xs _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ rename1 ‘exp_rel foo’
          \\ qid_spec_tac ‘ys’
          \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ fs [ELIM_UNCURRY])
    \\ drule ALOOKUP_LIST_REL
    \\ simp [EVERY2_REVERSE]
    \\ disch_then (drule_then (qspec_then ‘n’ assume_tac))
    \\ Cases_on ‘ALOOKUP (REVERSE xs) n’ \\ gs []
    \\ reverse CASE_TAC \\ gvs [exp_rel_def]
    >- (
      rename1 ‘Let opt _ _’
      \\ Cases_on ‘opt’ \\ fs [exp_rel_def])
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ irule exp_rel_subst_app2 \\ fs []
    \\ gvs [FILTER_FILTER, combinTheory.o_DEF, LAMBDA_PROD, MAP_REVERSE,
            AC CONJ_COMM CONJ_ASSOC])
  >- ((* Lam *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def,
             v_rel_def, exp_rel_def])
  >- ((* Let NONE *)
    rename1 ‘Let NONE x1 y1’
    \\ rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def,
             v_rel_def, exp_rel_def]
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x1’ \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs [])
  >- ((* Let SOME *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def,
             v_rel_def, exp_rel_def]
    \\ IF_CASES_TAC \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
    \\ gvs []
    \\ first_x_assum irule
    \\ irule exp_rel_subst_app1 \\ fs [])
  >- ((* If *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ rpt (first_x_assum (drule_then assume_tac)) \\ fs []
    \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
    \\ IF_CASES_TAC \\ fs []
    >- (
      rw []
      \\ gvs [v_rel_def])
    \\ IF_CASES_TAC \\ fs []
    >- (
      rw []
      \\ gvs [v_rel_def])
    \\ Cases_on ‘y’ \\ rw [] \\ gvs [v_rel_def])
  >- ((* Letrec *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ IF_CASES_TAC \\ fs []
    \\ first_x_assum irule
    \\ fs [subst_funs_def]
    \\ irule exp_rel_ALOOKUP_EQ
    \\ irule_at Any exp_rel_subst
    \\ first_assum (irule_at Any) \\ simp []
    \\ qmatch_goalsub_abbrev_tac ‘MAP Q g’
    \\ qexists_tac ‘MAP Q g’ \\ simp [Abbr ‘Q’]
    \\ rename1 ‘LIST_REL _ xs ys’
    \\ ‘MAP FST (REVERSE xs) = MAP FST (REVERSE ys)’
      by (qpat_x_assum ‘LIST_REL _ xs _’ mp_tac
          \\ rpt (pop_assum kall_tac)
          \\ rename1 ‘exp_rel foo’
          \\ qid_spec_tac ‘ys’
          \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ fs [ELIM_UNCURRY])
    \\ rpt conj_tac
    >- (
      fs [env_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM,
          MAP_REVERSE]
      \\ rw [GSYM MAP_REVERSE, ALOOKUP_MAP_2]
      \\ drule_then (qspec_then ‘REVERSE ys’ mp_tac) ALOOKUP_SOME_EL_2
      \\ simp [MAP_REVERSE]
      \\ rw [] \\ gvs [LIST_REL_EL_EQN, EL_REVERSE, v_rel_def])
    >- (
      fs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_THM]
      \\ rw []
      \\ fs [MAP_FILTER_FST, ELIM_UNCURRY, MEM_FILTER, MAP_REVERSE])
    \\ rw [FUN_EQ_THM, REVERSE_APPEND, GSYM FILTER_REVERSE, GSYM MAP_REVERSE,
           ALOOKUP_APPEND, ALOOKUP_MAP_2, ALOOKUP_FILTER]
    \\ CASE_TAC \\ fs []
    \\ CASE_TAC \\ fs []
    \\ gs [ALOOKUP_NONE, MAP_REVERSE])
  >- ((* Delay *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def,
             v_rel_def])
  >- ((* Box *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ fs []
    \\ simp [v_rel_def])
  >- ((* Force *)
    rw [exp_rel_def]
    \\ simp [Once thunkLangTheory.eval_to_def,
             Once thunkLang_substTheory.eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ fs []
    \\ first_x_assum (drule_then strip_assume_tac) \\ gvs []
    \\ Cases_on ‘dest_Tick y’ \\ gs []
    >- (
      ‘dest_Tick w = NONE’
        by (Cases_on ‘y’ \\ Cases_on ‘w’
            \\ gs [v_rel_def])
      \\ simp []
      \\ drule_then strip_assume_tac dest_Thunk_v_rel
      \\ drule_then strip_assume_tac dest_Recclosure_v_rel
      \\ simp [thunkLangTheory.dest_anyThunk_def,
               thunkLang_substTheory.dest_anyThunk_def]
      \\ reverse (Cases_on ‘dest_Thunk y’) \\ gvs []
      >- (
        simp [Once thunkLangTheory.eval_to_def,
              thunkLangTheory.dest_anyThunk_def])
      >- (
        IF_CASES_TAC \\ gs []
        \\ simp [Once thunkLangTheory.eval_to_def,
                 thunkLangTheory.dest_anyThunk_def]
        \\ first_x_assum irule
        \\ simp [subst_funs_def])
      \\ Cases_on ‘dest_Recclosure y’ \\ gvs []
      \\ Cases_on ‘y’ \\ gs []
      \\ pairarg_tac \\ gvs []
      \\ Cases_on ‘w’ \\ gvs [v_rel_def]
      \\ rename1 ‘LIST_REL _ xs ys’
      \\ ‘MAP FST (REVERSE xs) = MAP FST (REVERSE ys)’
        by (qpat_x_assum ‘LIST_REL _ xs _’ mp_tac
            \\ rpt (pop_assum kall_tac)
            \\ rename1 ‘exp_rel foo’
            \\ qid_spec_tac ‘ys’
            \\ Induct_on ‘xs’ \\ Cases_on ‘ys’ \\ fs [ELIM_UNCURRY])
      \\ drule ALOOKUP_LIST_REL
      \\ simp [EVERY2_REVERSE]
      \\ disch_then (drule_then (qspec_then ‘n’ assume_tac))
      \\ CASE_TAC \\ gs []
      \\ CASE_TAC \\ gvs [exp_rel_def]
      >- (
        rename1 ‘Let opt _ _’
        \\ Cases_on ‘opt’
        \\ gvs [exp_rel_def])
      \\ IF_CASES_TAC \\ gs [subst_funs_def]
      \\ simp [Once thunkLangTheory.eval_to_def,
               thunkLangTheory.dest_anyThunk_def]
      \\ first_x_assum irule \\ simp []
      \\ irule exp_rel_ALOOKUP_EQ
      \\ irule_at Any exp_rel_subst
      \\ first_assum (irule_at Any)
      \\ qmatch_goalsub_abbrev_tac ‘REVERSE (env1 ++ extra1)’
      \\ qexists_tac ‘extra1’
      \\ unabbrev_all_tac
      \\ fs [env_rel_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_REVERSE,
             GSYM FST_THM]
      \\ simp [FUN_EQ_THM, GSYM MAP_REVERSE, ALOOKUP_MAP_2, GSYM FILTER_REVERSE,
               ALOOKUP_FILTER, REVERSE_APPEND, ALOOKUP_APPEND, GSYM ALOOKUP_NONE]
      \\ rw [] \\ rpt CASE_TAC \\ gs [ALOOKUP_NONE, PULL_EXISTS, v_rel_def,
                                      MAP_REVERSE]
      \\ drule_then (qspec_then ‘REVERSE ys’ mp_tac) ALOOKUP_SOME_EL_2
      \\ rw [MAP_REVERSE] \\ gvs [v_rel_def])
    \\ Cases_on ‘y’ \\ Cases_on ‘w’ \\ gvs [v_rel_def]
    \\ IF_CASES_TAC \\ gs []
    \\ qabbrev_tac ‘foo = λv. eval_to (k - 1) [dummy,v] (Force (Var dummy))’
    \\ simp [Once thunkLangTheory.eval_to_def]
    \\ simp [Abbr ‘foo’])
  >- ((* MkTick *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ Cases_on ‘eval_to k x’ \\ gs []
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [v_rel_def])
  >- ((* Prim *)
    rw [exp_rel_def]
    \\ simp [thunkLangTheory.eval_to_def, thunkLang_substTheory.eval_to_def]
    \\ Cases_on ‘op’ \\ fs []
    >- ((* Cons *)
      gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
      \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ Cases_on ‘result_map f xs’ \\ fs []
      >- (
        reverse (Cases_on ‘result_map g ys’) \\ fs []
        >- (
          gvs [result_map_def, CaseEq "bool", MEM_MAP]
          \\ fs [Once (METIS_PROVE [] “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
          \\ unabbrev_all_tac
          \\ gs [MEM_EL, PULL_EXISTS]
          \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs [])
        \\ gvs [result_map_def, CaseEq "bool", MEM_MAP]
        \\ fs [Once (METIS_PROVE [] “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ unabbrev_all_tac \\ gs []
        \\ gvs [MEM_EL, PULL_EXISTS]
        >- (
          rpt (first_x_assum (drule_then assume_tac)) \\ gs []
          \\ pop_assum mp_tac \\ gs []
          \\ CASE_TAC \\ gs [])
        \\ rename1 ‘eval_to k (EL m xs)’
        \\ qpat_x_assum ‘m < LENGTH ys’ assume_tac
        \\ rpt (first_x_assum (drule_then assume_tac)) \\ gs [])
      \\ Cases_on ‘result_map g ys’ \\ gs []
      >- (
        gvs [result_map_def, CaseEq "bool", MEM_MAP, MEM_EL, PULL_EXISTS]
        \\ fs [Once (METIS_PROVE [] “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ unabbrev_all_tac \\ gs []
        \\ rpt (first_x_assum (drule_all_then assume_tac))
        \\ pop_assum mp_tac
        \\ CASE_TAC \\ gs []
        \\ strip_tac \\ gs [])
      \\ gvs [v_rel_def, LIST_REL_EL_EQN, result_map_def, CaseEq "bool",
              MEM_MAP]
      \\ fs [Once (METIS_PROVE [] “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ gs [MAP_MAP_o, combinTheory.o_DEF, EL_MAP] \\ rw []
      \\ gvs [MEM_EL, PULL_EXISTS]
      \\ rpt (first_x_assum (drule_all_then assume_tac))
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ unabbrev_all_tac \\ gs []
      \\ Cases_on ‘eval_to k (EL n xs)’ \\ Cases_on ‘eval_to k env (EL n ys)’
      \\ gvs []
      \\ rename1 ‘INL err’
      \\ Cases_on ‘err’ \\ gs [])
    >- ((* IsEq *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ IF_CASES_TAC \\ fs []
      \\ rename1 ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ drule_then assume_tac dest_Constructor_v_rel
      \\ Cases_on ‘dest_Constructor y’ \\ fs []
      \\ pairarg_tac \\ gvs []
      \\ imp_res_tac LIST_REL_LENGTH
      \\ IF_CASES_TAC \\ fs []
      \\ simp [v_rel_def])
    >- ((* Proj *)
      gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ fs []
      \\ gvs [LENGTH_EQ_NUM_compute, DECIDE “∀n. n < 1 ⇔ n = 0”]
      \\ IF_CASES_TAC \\ fs []
      \\ rename1 ‘eval_to (k - 1) x’
      \\ Cases_on ‘eval_to (k - 1) x’ \\ fs []
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ drule_then assume_tac dest_Constructor_v_rel
      \\ Cases_on ‘dest_Constructor y’ \\ fs []
      \\ pairarg_tac \\ gvs [LIST_REL_EL_EQN]
      \\ IF_CASES_TAC \\ fs [])
    >- ((* AtomOp *)
      gvs [LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS]
      \\ Cases_on ‘k = 0’ \\ gs []
      >- (
        simp [result_map_def, MEM_MAP, GSYM NOT_NULL_MEM, NULL_EQ]
        \\ IF_CASES_TAC \\ gs []
        >- (
          IF_CASES_TAC \\ gs [])
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [v_rel_def])
      \\ qmatch_goalsub_abbrev_tac ‘result_map f xs’
      \\ qmatch_goalsub_abbrev_tac ‘result_map g ys’
      \\ qsuff_tac ‘result_map f xs = result_map g ys’
      >- (
        rw []
        \\ Cases_on ‘result_map g ys’ \\ gs []
        \\ CASE_TAC \\ gs []
        \\ CASE_TAC \\ gs [v_rel_def])
      \\ gs [result_map_def, MEM_MAP]
      \\ IF_CASES_TAC \\ gs []
      >- (
        IF_CASES_TAC \\ gs []
        \\ fs [Once (METIS_PROVE [] “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ gvs [MEM_EL, PULL_EXISTS]
        \\ first_x_assum (drule_then assume_tac)
        \\ unabbrev_all_tac \\ gs []
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ gs [CaseEqs ["sum", "v"]])
      \\ IF_CASES_TAC \\ gs []
      >- (
        reverse IF_CASES_TAC \\ gs []
        >- (
          fs [Once (METIS_PROVE [] “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
          \\ gvs [MEM_EL, PULL_EXISTS]
          \\ first_x_assum (drule_then assume_tac)
          \\ unabbrev_all_tac \\ gs []
          \\ rpt (first_x_assum (drule_then assume_tac))
          \\ first_assum (irule_at Any) \\ gs []
          \\ pop_assum mp_tac
          \\ rpt CASE_TAC \\ gs [CaseEqs ["v"], v_rel_def])
        \\ unabbrev_all_tac \\ gs []
        \\ gvs [MEM_EL, PULL_EXISTS]
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ pop_assum mp_tac
        \\ rpt CASE_TAC \\ gs []
        \\ rpt strip_tac \\ gs [CaseEqs ["sum", "thunkLang$v"]])
      \\ IF_CASES_TAC \\ gs []
      >- (
        fs [Once (METIS_PROVE [] “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
        \\ unabbrev_all_tac
        \\ gvs [MEM_EL, PULL_EXISTS]
        \\ rpt (first_x_assum (drule_then assume_tac))
        \\ pop_assum mp_tac
        \\ rpt CASE_TAC \\ gs []
        \\ rpt strip_tac \\ gs [CaseEqs ["sum", "thunkLang$v"]])
      \\ fs [Once (METIS_PROVE [] “A ⇒ ¬B ⇔ B ⇒ ¬A”)]
      \\ gs [EL_MAP, MEM_EL, PULL_EXISTS]
      \\ unabbrev_all_tac \\ gs [] \\ rw []
      >- (
        rpt (first_x_assum (drule_then assume_tac))
        \\ pop_assum mp_tac
        \\ CASE_TAC \\ gs [] \\ rw []
        \\ gs [CaseEqs ["thunkLang$v", "v"]]
        \\ rename1 ‘v_rel v1 v2’
        \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ gs [v_rel_def])
      \\ simp [MAP_MAP_o, combinTheory.o_DEF]
      \\ irule LIST_EQ
      \\ gvs [EL_MAP] \\ rw []
      \\ rpt (first_x_assum (drule_then assume_tac))
      \\ CASE_TAC \\ gs []
      \\ CASE_TAC \\ gs []
      \\ CASE_TAC \\ gs [v_rel_def]))
QED

Theorem eval_exp_rel:
  eval x = res ∧
  exp_rel env x y ⇒
    case res of
      INL err => eval env y = INL err
    | INR v => ∃w. eval env y = INR w ∧ v_rel v w
Proof
  rw [thunkLang_substTheory.eval_def, thunkLangTheory.eval_def]
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ reverse strip_tac
  >- (
    strip_tac
    \\ DEEP_INTRO_TAC some_intro \\ simp []
    \\ qx_gen_tac ‘k’
    \\ ‘∃r. eval_to k x = r’ by fs []
    \\ drule_all eval_to_exp_rel \\ gs [])
  \\ qx_gen_tac ‘k’
  \\ strip_tac
  \\ DEEP_INTRO_TAC some_intro \\ simp []
  \\ reverse strip_tac
  >- (
    strip_tac
    \\ ‘∃r. eval_to k x = r’ by fs []
    \\ drule_all eval_to_exp_rel \\ gs [])
  \\ qx_gen_tac ‘j’
  \\ strip_tac
  \\ ‘∃r. eval_to k x = r’ by fs []
  \\ drule_all_then assume_tac eval_to_exp_rel
  \\ Cases_on ‘j ≤ k’ \\ gvs []
  >- (
    drule_all eval_to_mono
    \\ disch_then (assume_tac o SYM)
    \\ gs [])
  \\ ‘k ≤ j’ by fs []
  \\ drule_all eval_to_subst_mono
  \\ disch_then (assume_tac o SYM) \\ gs []
  \\ irule_at Any eval_to_exp_rel
  \\ irule_at Any EQ_REFL \\ fs []
QED

Theorem compile_exp_freevars:
  ∀x. freevars (compile_exp x) = freevars x
Proof
  ho_match_mp_tac compile_exp_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ simp [compile_exp_def,
           thunkLangTheory.freevars_def,
           thunkLang_substTheory.freevars_def]
  \\ strip_tac
  >- (
    simp [MAP_MAP_o, combinTheory.o_DEF]
    \\ AP_TERM_TAC
    \\ AP_TERM_TAC
    \\ irule LIST_EQ
    \\ gvs [MEM_EL, PULL_EXISTS, EL_MAP])
  >- (
    rename1 ‘Let opt _ _’
    \\ Cases_on ‘opt’ \\ gs [thunkLangTheory.freevars_def,
                             thunkLang_substTheory.freevars_def])
  >- (
    rw [MEM_MAP, MAP_MAP_o, combinTheory.o_DEF, EXTENSION]
    \\ fs [EXISTS_PROD, FORALL_PROD]
    \\ metis_tac [])
QED

Theorem compile_exp_closed:
  ∀x. closed (compile_exp x) ⇔ closed x
Proof
  rw [thunkLangTheory.closed_def, thunkLang_substTheory.closed_def,
      compile_exp_freevars]
QED

Definition no_Value_def:
  no_Value (Value v) = F ∧
  no_Value (Var n) = T ∧
  no_Value (Prim op xs) = EVERY no_Value xs ∧
  no_Value (App x y) = (no_Value x ∧ no_Value y) ∧
  no_Value (Lam s x) = no_Value x ∧
  no_Value (Let s x y) = (no_Value x ∧ no_Value y) ∧
  no_Value (Letrec f x) =
    (EVERY (λ(f,x). no_Value x) f ∧
     no_Value x) ∧
  no_Value (If x y z) = (no_Value x ∧ no_Value y ∧ no_Value z) ∧
  no_Value (Delay x) = no_Value x ∧
  no_Value (Box x) = no_Value x ∧
  no_Value (Force x) = no_Value x ∧
  no_Value (MkTick x) = no_Value x
Termination
  WF_REL_TAC ‘measure exp_size’ \\ simp []
  \\ rw [] \\ rename1 ‘MEM _ xs’
  \\ Induct_on ‘xs’ \\ rw [] \\ fs [thunkLang_substTheory.exp_size_def]
End

Theorem compile_exp_rce:
  ∀x. no_Value x ⇒ rce (compile_exp x) = x
Proof
  ho_match_mp_tac compile_exp_ind
  \\ simp [rce_def, no_Value_def, compile_exp_def] \\ rw []
  \\ fs [MAP_MAP_o, combinTheory.o_DEF, EVERY_MEM]
  \\ irule MAP_ID_ON \\ fs []
  \\ fs [ELIM_UNCURRY, FORALL_PROD, SF SFY_ss]
QED

Theorem exp_rel_rce:
  ∀x. exp_rel [] (rce x) x
Proof
  ho_match_mp_tac rce_ind
  \\ simp [rce_def, exp_rel_def]
  \\ rw []
  \\ fs [EVERY2_MAP, LIST_REL_EL_EQN, MEM_EL, PULL_EXISTS, EL_MAP] \\ rw []
  >- (
    rename1 ‘Let opt _ _’
    \\ Cases_on ‘opt’ \\ fs [exp_rel_def])
  \\ fs [ELIM_UNCURRY]
  \\ first_x_assum irule
  \\ first_assum (irule_at Any) \\ fs []
  \\ irule_at Any PAIR
QED

Theorem eval_to_rce:
  eval_to k (rce x) = res ⇒
  case res of
    INL err => eval_to k [] x = INL err
  | INR v => ∃w. eval_to k [] x = INR w ∧ v_rel v w
Proof
  strip_tac
  \\ irule_at Any eval_to_exp_rel
  \\ irule_at Any exp_rel_rce \\ fs []
QED

Theorem eval_rce:
  eval (rce x) = res ⇒
  case res of
    INL err => eval [] x = INL err
  | INR v => ∃w. eval [] x = INR w ∧ v_rel v w
Proof
  strip_tac
  \\ irule_at Any eval_exp_rel
  \\ irule_at Any exp_rel_rce \\ fs []
QED

Theorem compile_exp_eval_to:
  eval_to k x = res ∧
  no_Value x ⇒
    case res of
      INL err => eval_to k [] (compile_exp x) = INL err
    | INR v => ∃w. eval_to k [] (compile_exp x) = INR w ∧ v_rel v w
Proof
  strip_tac
  \\ irule eval_to_rce
  \\ simp [compile_exp_rce]
QED

Theorem compile_exp_eval:
  eval x = res ∧
  no_Value x ⇒
    case res of
      INL err => eval [] (compile_exp x) = INL err
    | INR v => ∃w. eval [] (compile_exp x) = INR w ∧ v_rel v w
Proof
  strip_tac
  \\ irule eval_rce
  \\ simp [compile_exp_rce]
QED

val _ = export_theory ();


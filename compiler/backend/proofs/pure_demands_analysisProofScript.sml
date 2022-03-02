(*
   Proof of the demands analysis handler
*)

open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory dep_rewrite
     optionTheory pairTheory ltreeTheory llistTheory bagTheory mlmapTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory
     finite_mapTheory mlstringTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_miscTheory pure_exp_relTheory pure_congruenceTheory
     pure_cexpTheory pure_demandTheory;

val _ = new_theory "pure_demands_analysisProof";

Datatype:
  da_ctxt =
      | Nil
      | IsFree (vname list) da_ctxt
      | Bind vname (α cexp) da_ctxt da_ctxt
      | RecBind ((vname # (α cexp)) list) da_ctxt da_ctxt
End

Definition adds_demands_def:
  (adds_demands a0 m e [] = e) ∧
  (adds_demands a0 m e (name::tl) =
     case lookup m (strlit name) of
       | SOME () => Prim a0 Seq [Var a0 name; adds_demands a0 m e tl]
       | _ => adds_demands a0 m e tl)
End

Definition demands_analysis_fun_def:
  (demands_analysis_fun c ((Var a0 a1): 'a cexp) =
    (mlmap$insert (mlmap$empty mlstring$compare) (strlit a1) (), (Var a0 a1 : 'a cexp))) ∧
  (demands_analysis_fun c (App a0 f argl) =
     let (m1, f') = demands_analysis_fun c f in
       let e' = MAP SND ((MAP (demands_analysis_fun c)) argl) in
         (m1, App a0 f' e')) ∧
  (demands_analysis_fun c (Lam a0 vl e) =
     let (m, e') = demands_analysis_fun (IsFree vl c) e in
       (empty compare, Lam a0 vl (adds_demands a0 m e' vl))) ∧
  (demands_analysis_fun c (Let a0 name e1 e2) =
     let (m1, e1') = demands_analysis_fun c e1 in
       let (m2, e2') = demands_analysis_fun (Bind name e1 c c) e2 in
         (empty compare, Let a0 name e1' e2')) ∧
  (demands_analysis_fun c (Prim a0 Seq [e1; e2]) =
     let (m1, e1') = demands_analysis_fun c e1 in
       let (m2, e2') = demands_analysis_fun c e2 in
         (union m1 m2, Prim a0 Seq [e1'; e2'])) ∧
  (demands_analysis_fun c (Prim a0 Seq _) =
   (empty compare, Prim a0 Seq [])) ∧
  (demands_analysis_fun c (Prim a0 ope el) =
     let el = MAP SND (MAP (demands_analysis_fun c) el) in
       (empty compare, Prim a0 ope el)) ∧
  (demands_analysis_fun c (Letrec a0 binds e) =
     let (m, e') = demands_analysis_fun (RecBind binds c c) e in
       (empty compare, Letrec a0 binds e')) ∧
  (demands_analysis_fun c (Case a0 e n cases) =
     let (m, e') = demands_analysis_fun c e in
       (m, Case a0 e n cases))
Termination
  WF_REL_TAC ‘measure $ (cexp_size (K 0)) o SND’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ fs []
End

Definition ctxt_trans_def:
  ctxt_trans (Nil: α da_ctxt) = Nil ∧
  ctxt_trans (IsFree l ctxt) = FOLDL (λc n. IsFree n (c:ctxt)) (ctxt_trans ctxt) l ∧
  ctxt_trans (Bind n e c1 c2) = Bind n (exp_of e) (ctxt_trans c1) (ctxt_trans c2) ∧
  ctxt_trans ((RecBind (binds: (vname # α cexp) list) c1 c2): α da_ctxt) = (RecBind (MAP (λ(n,e). (n, exp_of e)) binds) (ctxt_trans c1) : ctxt)
End

Theorem adds_demands_soundness:
  ∀vl e e' m ds c ds a. find (exp_of e) c ds (exp_of e')
                      ⇒ (∀v. (lookup m (strlit v)) = SOME () ⇔ ∃ps. (ps, v) ∈ ds)
                      ⇒ find (exp_of e) c ds (exp_of (adds_demands a m e' vl))
Proof
  Induct
  \\ rw [adds_demands_def]
  \\ rename1 ‘lookup m (strlit h)’
  \\ Cases_on ‘lookup m (strlit h)’
  \\ fs []
  \\ rw [exp_of_def, op_of_def]
  \\ irule find_Seq
  \\ first_assum $ qspecl_then [‘h’] assume_tac
  \\ fs []
  \\ first_x_assum $ irule_at Any
  \\ first_x_assum irule
QED

(*
Theorem test:
  exp_of (Prim 0 Seq [x; y; z]) ≅ exp_of (Prim 0 Seq [])
Proof
  rw [exp_of_def, op_of_def]
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_def, eval_wh_to_def]
QED
*)

Theorem demands_analysis_soudness_lemma:
  ∀(f: num -> α) (e: α cexp) c m e'.
    demands_analysis_fun c e = (m, e') ⇒
       ∃ds. (∀v. (lookup m (strlit v)) = SOME () ⇔ ∃ps. (ps, v) ∈ ds) ∧
            find (exp_of e) (ctxt_trans c) ds (exp_of e') ∧
            map_ok m ∧ cmp_of m = compare
Proof
  gen_tac
  \\ completeInduct_on ‘cexp_size f e’
  \\ gen_tac
  \\ Cases
  \\ rename1 ‘Size = cexp_size _ _’
  \\ rw [demands_analysis_fun_def, exp_of_def] >~[‘Var n’]
  >- (qexists_tac ‘{([], n)}’
      \\ fs [find_Var]
      \\ fs [empty_thm, TotOrd_compare, insert_thm, lookup_insert, lookup_thm]
      \\ rw []
      \\ eq_tac
      \\ rw [])
  >~[‘Prim a op l’]
  >- (Cases_on ‘op’
      \\ rw [op_of_def] >~[‘Prim a Seq l’]
      >- (Cases_on ‘l’ >~[‘Prim a Seq []’]
          >- (fs [demands_analysis_fun_def]
              \\ qexists_tac ‘{}’
              \\ fs [empty_thm, lookup_thm, TotOrd_compare]
              \\ rw [exp_of_def, op_of_def]
              \\ fs [find_Bottom])
          \\ rename1 ‘e1::t’
          \\ Cases_on ‘t’ >~[‘Prim a Seq [e]’]
          >- (fs [demands_analysis_fun_def]
              \\ qexists_tac ‘{}’
              \\ fs [empty_thm, lookup_thm, TotOrd_compare]
              \\ rw [exp_of_def, op_of_def]
              \\ irule find_Eq
              \\ irule eval_wh_IMP_exp_eq
              \\ rw [eval_wh_def, eval_wh_to_def, subst_def])
          \\ rename1 ‘e1::e2::t’
          \\ Cases_on ‘t’ >~ [‘Prim a Seq (e1::e2::e3::t)’]
          >- (fs [demands_analysis_fun_def]
              \\ qexists_tac ‘{}’
              \\ fs [empty_thm, lookup_thm, TotOrd_compare]
              \\ rw [exp_of_def, op_of_def]
              \\ irule find_Eq
              \\ irule eval_wh_IMP_exp_eq
              \\ rw [eval_wh_def, eval_wh_to_def, subst_def])
          \\ first_assum   $ qspecl_then [‘cexp_size f e1’] assume_tac
          \\ first_x_assum $ qspecl_then [‘cexp_size f e2’] assume_tac
          \\ fs [cexp_size_def, cexp_size_lemma]
          \\ pop_assum     $ qspecl_then [‘f’, ‘e2’] assume_tac
          \\ first_x_assum $ qspecl_then [‘f’, ‘e1’] assume_tac
          \\ fs [demands_analysis_fun_def]
          \\ rename1 ‘demands_analysis_fun c _’
          \\ pop_assum     $ qspecl_then [‘c’] assume_tac
          \\ first_x_assum $ qspecl_then [‘c’] assume_tac
          \\ qabbrev_tac ‘p1 = demands_analysis_fun c e1’
          \\ qabbrev_tac ‘p2 = demands_analysis_fun c e2’
          \\ PairCases_on ‘p1’
          \\ PairCases_on ‘p2’
          \\ fs []
          \\ rw [exp_of_def, op_of_def]
          \\ irule_at Any find_Seq2
          \\ first_x_assum $ irule_at Any
          \\ first_x_assum $ irule_at Any
          \\ fs [lookup_thm, union_thm, FLOOKUP_FUNION]
          \\ gen_tac
          \\ eq_tac
          \\ rw []
          >- (Cases_on ‘FLOOKUP (to_fmap p10) (strlit v)’
              \\ fs []
              >- (‘∃ps. (ps, v) ∈ ds'’ by metis_tac []
                  \\ qexists_tac ‘ps’
                  \\ fs [])
              \\ ‘∃ps. (ps, v) ∈ ds’ by metis_tac []
              \\ qexists_tac ‘ps’
              \\ fs [])
          >- (‘FLOOKUP (to_fmap p10) (strlit v) = SOME ()’ by metis_tac []
             \\ fs [])
          \\ ‘FLOOKUP (to_fmap p20) (strlit v) = SOME ()’ by metis_tac []
          \\ fs []
          \\ Cases_on ‘FLOOKUP (to_fmap p10) (strlit v)’
          \\ fs [])
      \\ qexists_tac ‘{}’
      \\ fs [empty_thm, TotOrd_compare, demands_analysis_fun_def, lookup_thm]
      \\ rw [exp_of_def, op_of_def]
      \\ irule_at Any find_Prim
      \\ fs [empty_thm, TotOrd_compare, lookup_thm]
      \\ rw [EL_MAP]
      \\ rename1 ‘EL k l’
      \\ first_x_assum $ qspecl_then [‘cexp_size f (EL k l)’] assume_tac
      \\ ‘cexp_size f (EL k l) < cexp6_size f l’
        by metis_tac [cexp_size_lemma, MEM_EL]
      \\ fs [cexp_size_def]
      \\ pop_assum kall_tac
      \\ rename1 ‘demands_analysis_fun c _’
      \\ pop_assum $ qspecl_then [‘f’, ‘EL k l’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun c (EL k l)’
      \\ PairCases_on ‘p’
      \\ fs []
      \\ first_x_assum $ irule_at Any)
  >~[‘App a fe argl’]
  >- (rename1 ‘ctxt_trans c’
      \\ qabbrev_tac ‘p = demands_analysis_fun c fe’
      \\ PairCases_on ‘p’
      \\ fs []
      \\ rw [exp_of_def]
      \\ irule_at Any find_Apps
      \\ first_assum $ qspecl_then [‘cexp_size f fe’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘fe’] assume_tac
      \\ fs []
      \\ pop_assum drule
      \\ rw []
      \\ fs []
      \\ first_x_assum $ irule_at Any
      \\ fs [LIST_REL_EL_EQN]
      \\ rw []
      \\ rename1 ‘EL n _’
      \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
      \\ ‘cexp_size f (EL n argl) < cexp6_size f argl’ by metis_tac [cexp_size_lemma, MEM_EL]
      \\ fs [cexp_size_def]
      \\ pop_assum kall_tac
      \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl)’
      \\ PairCases_on ‘p’
      \\ fs [EL_MAP]
      \\ first_x_assum $ irule_at Any)
  >~ [‘Lam a namel e’]
  >- (first_assum $ qspecl_then [‘cexp_size f e’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘e’] assume_tac
      \\ fs []
      \\ rename1 ‘ctxt_trans c’
      \\ pop_assum $ qspecl_then [‘IsFree namel c’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun (IsFree namel c) e’
      \\ PairCases_on ‘p’
      \\ fs []
      \\ qexists_tac ‘{}’
      \\ fs []
      \\ fs [lookup_thm, TotOrd_compare, empty_thm]
      \\ rw [exp_of_def]
      \\ irule find_Lams
      \\ qexists_tac ‘ds’
      \\ fs [ctxt_trans_def, adds_demands_soundness, lookup_thm])
  >~ [‘Let a vname e2 e1’]
  >- (rename1 ‘demands_analysis_fun (Bind _ _ _ c) _’
      \\ first_assum $ qspecl_then [‘cexp_size f e1’] assume_tac
      \\ first_x_assum $ qspecl_then [‘cexp_size f e2’] assume_tac
      \\ fs [cexp_size_def]
      \\ first_x_assum $ qspecl_then [‘f’, ‘e2’] assume_tac
      \\ first_x_assum $ qspecl_then [‘f’, ‘e1’] assume_tac
      \\ qabbrev_tac ‘p1 = demands_analysis_fun (Bind vname e2 c c) e1’
      \\ qabbrev_tac ‘p2 = demands_analysis_fun c e2’
      \\ PairCases_on ‘p1’
      \\ PairCases_on ‘p2’
      \\ fs []
      \\ first_x_assum drule
      \\ first_x_assum drule
      \\ rw []
      \\ qexists_tac ‘{}’
      \\ fs [empty_thm, TotOrd_compare, lookup_thm]
      \\ irule find_Subset
      \\ rw [exp_of_def]
      \\ Cases_on ‘FLOOKUP (to_fmap p10) (strlit vname)’
      \\ fs []
      >- (irule_at Any find_Let
          \\ fs []
          \\ first_x_assum $ irule_at Any
          \\ fs [ctxt_trans_def]
          \\ first_x_assum $ irule_at Any
          \\ gen_tac
          \\ strip_tac
          \\ ‘FLOOKUP (to_fmap p10) (strlit vname) = SOME ()’
            by (fs [] \\ first_x_assum $ irule_at Any)
          \\ fs [])
      \\ irule_at Any find_Let2
      \\ first_assum $ irule_at Any
      \\ fs [ctxt_trans_def]
      \\ first_assum $ irule_at Any
      \\ ‘∃ps. (ps, vname) ∈ ds'’ by metis_tac []
      \\ first_assum $ irule_at Any
      \\ qexists_tac ‘{}’
      \\ fs [])
  >~ [‘Letrec a binds exp’]
  >- (rename1 ‘demands_analysis_fun (RecBind binds c c) _’
      \\ qexists_tac ‘{}’
      \\ qabbrev_tac ‘e = demands_analysis_fun (RecBind binds c c) exp’
      \\ PairCases_on ‘e’
      \\ fs [empty_thm, lookup_thm, TotOrd_compare]
      \\ rw [exp_of_def]
      \\ irule find_Letrec
      \\ rw []
      >- (rename1 ‘LIST_REL _ l _’
          \\ qexists_tac ‘l’
          \\ pop_assum kall_tac
          \\ pop_assum kall_tac
          \\ Induct_on ‘l’
          \\ fs [exp_eq_refl]
          \\ gen_tac
          \\ rename1 ‘_ hd hd’
          \\ PairCases_on ‘hd’
          \\ fs [exp_eq_refl])
      \\ first_x_assum $ qspecl_then [‘cexp_size f exp’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘exp’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘RecBind binds c c’, ‘e0’, ‘e1’] assume_tac
      \\ pop_assum $ drule
      \\ rw [ctxt_trans_def]
      \\ first_x_assum $ irule_at Any)
  >~ [‘Case a case_exp s l’]
  >- (rename1 ‘demands_analysis_fun c case_exp’
      \\ first_x_assum $ qspecl_then [‘cexp_size f case_exp’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘case_exp’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’] assume_tac
      \\ qabbrev_tac ‘cexp = demands_analysis_fun c case_exp’
      \\ PairCases_on ‘cexp’
      \\ fs []
      \\ rw [exp_of_def]
      \\ irule_at Any find_Bottom
      \\ cheat)
  >~[‘Case a case_exp s l’]
  >- (rename1 ‘demands_analysis_fun c case_exp’
      \\ first_x_assum $ qspecl_then [‘cexp_size f case_exp’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘case_exp’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’] assume_tac
      \\ qabbrev_tac ‘cexp = demands_analysis_fun c case_exp’
      \\ PairCases_on ‘cexp’
      \\ fs []
      \\ rw [exp_of_def]
      \\ irule_at Any find_Bottom
      \\ cheat)
QED

Theorem demands_analysis_fun_soudness:
  ∀(f: α -> num) (e : α cexp). exp_of e ≈ exp_of (SND (demands_analysis_fun Nil e))
Proof
  rpt gen_tac
  \\ qspecl_then [‘f’, ‘e’, ‘Nil’] assume_tac demands_analysis_soudness_lemma
  \\ qabbrev_tac ‘e' = demands_analysis_fun Nil e’
  \\ PairCases_on ‘e'’
  \\ fs []
  \\ drule find_soundness_lemma
  \\ fs []
QED

val _ = export_theory();

(*
   Formalises the notion of "demand" as used in demand/strictness analysis.
*)

open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory dep_rewrite
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_miscTheory pure_exp_relTheory pure_congruenceTheory
     pure_alpha_equivTheory pure_exp_eq_in_ctxtTheory pure_alpha_equivTheory;

val _ = new_theory "pure_demand";

(** begin ctxt **)

(* Definitions *)

Datatype:
  ctxt = Nil
       | IsFree string ctxt
       | Bind string exp ctxt
       | RecBind ((string # exp) list) ctxt
End

Definition eq_when_applied_def:
  (eq_when_applied Nil e1 e2 len = ∀l. len = LENGTH l ⇒ (Apps e1 l) ≈ (Apps e2 l)) ∧
  eq_when_applied (Bind v e c) e1 e2 len = eq_when_applied c (Let v e e1) (Let v e e2) len ∧
  eq_when_applied (IsFree v c) e1 e2 len = (∀e. closed e ⇒ eq_when_applied c (Let v e e1) (Let v e e2) len) ∧
  eq_when_applied (RecBind b c) e1 e2 len = eq_when_applied c (Letrec b e1) (Letrec b e2) len
End

Definition exp_eq_in_ctxt_def:
  exp_eq_in_ctxt Nil = (λe1 e2. e1 ≈ e2) ∧
  exp_eq_in_ctxt (IsFree s c) e1 e2 = (∀e3. closed e3 ⇒ exp_eq_in_ctxt c (Let s e3 e1) (Let s e3 e2)) ∧
  exp_eq_in_ctxt (Bind s e3 c) e1 e2 = exp_eq_in_ctxt c (Let s e3 e1) (Let s e3 e2) ∧
  exp_eq_in_ctxt (RecBind l c) e1 e2 = exp_eq_in_ctxt c (Letrec l e1) (Letrec l e2)
End

Theorem eq_when_applied_0:
  ∀c e1 e2. exp_eq_in_ctxt c e1 e2 = eq_when_applied c e1 e2 0
Proof
  Induct >>
  gvs [exp_eq_in_ctxt_def, eq_when_applied_def, Apps_def]
QED

Definition ctxt_size_def:
  ctxt_size Nil = 0n ∧
  ctxt_size (IsFree s ctxt) = 1 + ctxt_size ctxt ∧
  ctxt_size (Bind s e ctxt) = 1 + list_size char_size s +  exp_size e + ctxt_size ctxt ∧
  ctxt_size (RecBind sel ctxt) = 1 + exp1_size sel + ctxt_size ctxt
End

(* Preliminaries *)

Theorem exp_eq_l_refl:
  ∀b l. LIST_REL (λx y. (x ≅? y) b) l l
Proof
  gen_tac
  \\ Induct
  \\ fs [exp_eq_refl]
QED

Theorem exp_eq_Apps_cong:
  ∀l l' b e e'. LIST_REL (λx y. (x ≅? y) b) l l' ⇒ (e ≅? e') b ⇒ (Apps e l ≅? Apps e' l') b
Proof
  Induct
  \\ fs [Apps_def]
  \\ rw [Apps_def]
  \\ fs [Apps_def]
  \\ first_x_assum $ irule
  \\ fs [exp_eq_App_cong]
QED

Theorem exp_eq_Lams_cong:
  ∀l e e' b. (e ≅? e') b ⇒ (Lams l e ≅? Lams l e') b
Proof
  Induct
  \\ rw [Lams_def]
  \\ fs [exp_eq_Lam_cong]
QED

Theorem eval_Prim:
  ∀ope eL eL'. LIST_REL (λe1 e2. eval e1 = eval e2) eL eL' ⇒ eval (Prim ope eL) = eval (Prim ope eL')
Proof
  Cases
  \\ rw [eval_thm]
  >~[‘MAP _ _ = MAP _ _’]
  >- (irule LIST_EQ
      \\ gvs [LIST_REL_EL_EQN, EL_MAP])
  >~[‘AtomOp’]
  >- (fs [eval_def]
      \\ once_rewrite_tac [v_unfold]
      \\ fs [eval_wh_Prim]
      \\ qsuff_tac ‘get_atoms (MAP eval_wh eL') = get_atoms (MAP eval_wh eL)’
      >- (CASE_TAC \\ fs [])
      \\ fs [get_atoms_def]
      \\ qsuff_tac ‘EXISTS error_Atom (MAP eval_wh eL) ⇔ EXISTS error_Atom (MAP eval_wh eL')’
      >- (strip_tac
          \\ IF_CASES_TAC
          \\ simp []
          \\ qsuff_tac ‘MEM wh_Diverge (MAP eval_wh eL) ⇔ MEM wh_Diverge (MAP eval_wh eL')’
          >- (strip_tac
              \\ IF_CASES_TAC
              \\ simp []
              \\ irule LIST_EQ
              \\ rw []
              \\ gvs [LIST_REL_EL_EQN, EL_MAP, EVERY_EL]
              \\ rpt $ first_x_assum drule
              \\ once_rewrite_tac [v_unfold]
              \\ rpt FULL_CASE_TAC
              \\ rw [dest_Atom_def, error_Atom_def])
          \\ eq_tac
          \\ strip_tac
          \\ gvs [MEM_EL, LIST_REL_EL_EQN]
          \\ first_assum $ irule_at Any
          \\ first_assum drule
          \\ once_rewrite_tac [v_unfold]
          \\ rpt FULL_CASE_TAC
          \\ gvs [EL_MAP])
      \\ eq_tac
      \\ strip_tac
      \\ gvs [EXISTS_MEM, MEM_EL, EL_MAP, LIST_REL_EL_EQN]
      \\ rename1 ‘MAP eval_wh eL2’
      \\ qexists_tac ‘eval_wh (EL n eL2)’
      \\ first_x_assum drule
      \\ once_rewrite_tac [v_unfold]
      \\ rpt FULL_CASE_TAC
      \\ fs [error_Atom_def]
      \\ rw []
      \\ first_assum $ irule_at Any
      \\ fs [EL_MAP])
  \\ Cases_on ‘eL’ \\ Cases_on ‘eL'’ \\ fs []
  \\ rename1 ‘LIST_REL _ t1 t2’
  \\ Cases_on ‘t1’ \\ Cases_on ‘t2’ \\ gvs [eval_thm]
  >~[‘Prim Seq (_::_::_)’]
  >- (rename1 ‘LIST_REL _ t1 t2’
      \\ Cases_on ‘t1’ \\ Cases_on ‘t2’
      \\ gvs [eval_thm, eval_def]
      \\ once_rewrite_tac [v_unfold]
      \\ fs [eval_wh_Prim])
  >~[‘Prim If (_::_::_)’]
  >- (rename1 ‘LIST_REL _ t1 t2’
      \\ Cases_on ‘t1’ \\ Cases_on ‘t2’ \\ gvs []
      >~[‘_::_::_::_’]
      >- (rename1 ‘LIST_REL _ t1 t2’
          \\ Cases_on ‘t1’ \\ Cases_on ‘t2’
          \\ gvs [eval_thm, eval_def]
          \\ once_rewrite_tac [v_unfold]
          \\ rw [eval_wh_Prim])
      \\ rw [eval_def]
      \\ once_rewrite_tac [v_unfold]
      \\ rw [eval_wh_Prim])
  \\ rw [eval_def]
  \\ once_rewrite_tac [v_unfold]
  \\ rw [eval_wh_Prim]
QED

Theorem FLOOKUP_LUPDATE:
  ∀l f n v. FLOOKUP (f |++ l) n = SOME v ⇒ MEM (n, v) l ∨ FLOOKUP f n = SOME v
Proof
  Induct
  \\ fs [FUPDATE_LIST_THM]
  \\ PairCases \\ rw []
  \\ first_x_assum $ dxrule_then assume_tac
  \\ gvs [FLOOKUP_UPDATE]
  \\ FULL_CASE_TAC \\ fs []
QED

Theorem Letrec_Prim:
  ∀l ope eL b. (Letrec l (Prim ope eL) ≅? Prim ope (MAP (Letrec l) eL)) b
Proof
  rw []
  \\ irule eval_IMP_exp_eq
  \\ rw [subst_def, eval_thm, subst_funs_def, bind_def]
  >- (irule eval_Prim
      \\ rw [LIST_REL_EL_EQN, EL_MAP, subst_def, eval_thm, subst_funs_def]
      \\ gvs [bind_def]
      \\ IF_CASES_TAC \\ fs []
      \\ first_x_assum dxrule
      \\ strip_tac
      \\ fs [])
  \\ fs [MAP_MAP_o]
  \\ dxrule_then assume_tac FLOOKUP_LUPDATE
  \\ gvs [FLOOKUP_EMPTY, MEM_EL, EL_MAP]
  \\ qsuff_tac ‘F’ \\ fs []
  \\ first_x_assum irule
  \\ rename1 ‘EL k l’
  \\ qabbrev_tac ‘p = EL k l’
  \\ PairCases_on ‘p’
  \\ gvs [EVERY_EL, EL_MAP]
  \\ rw []
  \\ rename1 ‘EL k2 l’
  \\ qabbrev_tac ‘p' = EL k2 l’
  \\ PairCases_on ‘p'’
  \\ gvs []
  \\ ‘∀v. v ∈ FRANGE (FDIFF f (set (MAP FST l))) ⇒ closed v’
    by (rw []
        \\ first_x_assum irule
        \\ gvs [FRANGE_FLOOKUP, FLOOKUP_FDIFF]
        \\ pop_assum $ irule_at Any)
  \\ gvs [freevars_subst, SUBSET_DEF, IN_DIFF, FDOM_FDIFF]
  \\ rw [MEM_EL]
  >>~[‘EL _ (MAP FST _) = EL _ (MAP FST _)’]
  >- (first_assum $ irule_at Any
      \\ gvs [EL_MAP]
      \\ rename1 ‘FST p = FST _’
      \\ PairCases_on ‘p’
      \\ fs [])
  >- (first_assum $ irule_at Any
      \\ gvs [EL_MAP]
      \\ rename1 ‘FST p = FST _’
      \\ PairCases_on ‘p’
      \\ fs [])
  \\ first_x_assum $ qspecl_then [‘x’] assume_tac
  \\ pop_assum kall_tac
  \\ first_x_assum $ qspecl_then [‘x’] assume_tac
  \\ gvs [] >>~[‘MEM x (MAP FST l)’]
  >- (gvs [MEM_EL]
      \\ first_assum $ irule_at Any
      \\ fs [EL_MAP]
      \\ rename1 ‘FST p = FST _’
      \\ PairCases_on ‘p’ \\ fs [])
  >- (gvs [MEM_EL]
      \\ first_assum $ irule_at Any
      \\ fs [EL_MAP]
      \\ rename1 ‘FST p = FST _’
      \\ PairCases_on ‘p’ \\ fs [])
  \\ first_x_assum $ qspecl_then [‘freevars p'1’] assume_tac
  \\ gvs [MEM_MAP]
  \\ pop_assum $ qspecl_then [‘EL k2 l’] assume_tac
  \\ gvs [EL_MEM]
QED

Theorem Let_Lam:
  ∀v w e1 e2 b. closed e1 ∧ v ≠ w ⇒ (Let v e1 (Lam w e2) ≅? Lam w (Let v e1 e2)) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality
  \\ gvs [subst1_def]
  \\ irule exp_eq_Lam_cong
  \\ irule $ iffLR exp_eq_sym
  \\ irule beta_equality
  \\ gvs []
QED

Theorem Let_Lam_weak:
  ∀v w e1 e2 b. v ≠ w ⇒ w ∉ freevars e1 ⇒ (Let v e1 (Lam w e2) ≅? Lam w (Let v e1 e2)) b
Proof
  rw [exp_eq_def, bind_def] >> IF_CASES_TAC >>
  gvs [app_bisimilarity_eq, exp_eq_refl] >>
  rpt (irule_at Any IMP_closed_subst) >>
  drule_then assume_tac $ GSYM subst_fdomsub >>
  gvs [subst_def, DOMSUB_COMMUTES] >>
  irule_at Any Let_Lam >>
  irule_at Any IMP_closed_subst >>
  rw [FRANGE_FLOOKUP]
QED

Theorem FDIFF_DOMSUB:
  ∀f v s. FDIFF (f \\ s) v = (FDIFF f v) \\ s
Proof
  rw [FDIFF_def, fmap_domsub, INTER_COMM]
QED

Theorem MAP_subst_fdomsub:
  ∀v l f. EVERY (λe. v ∉ freevars e) (MAP SND l) ⇒
          MAP (λ(s, e). (s, subst (FDIFF f (set (MAP FST l)) \\ v) e)) l
          = MAP (λ(s, e). (s, subst (FDIFF f (set (MAP FST l))) e)) l
Proof
  rw [EVERY_EL] >> irule LIST_EQ >>
  rw [EL_MAP] >> first_x_assum $ drule_then assume_tac >>
  rename1 ‘EL x l’ >> qabbrev_tac ‘p = EL x l’ >> PairCases_on ‘p’ >>
  gvs [subst_fdomsub, EL_MAP]
QED

Theorem Letrec_Lam:
  ∀l w e b. EVERY (λe. freevars e ⊆ set (MAP FST l)) (MAP SND l) ∧ ¬MEM w (MAP FST l)
          ⇒ (Letrec l (Lam w e) ≅? Lam w (Letrec l e)) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality_Letrec
  \\ gvs [subst_funs_eq_subst, subst_def]
  \\ irule exp_eq_Lam_cong
  \\ irule $ iffLR exp_eq_sym
  \\ irule exp_eq_trans
  \\ irule_at Any beta_equality_Letrec
  \\ gvs [subst_funs_eq_subst]
  \\ irule eval_IMP_exp_eq
  \\ rw []
  \\ rpt AP_TERM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ irule $ GSYM DOMSUB_NOT_IN_DOM
  \\ gvs [FDOM_FUPDATE_LIST]
  \\ strip_tac \\ last_x_assum irule
  \\ gvs [MEM_EL]
  \\ first_assum $ irule_at Any
  \\ gvs [EL_MAP]
  \\ rename1 ‘FST (_ p)’
  \\ PairCases_on ‘p’
  \\ fs []
QED

Theorem Letrec_Lam_weak:
  ∀l v e b. EVERY (λe. v ∉ freevars e) (MAP SND l) ∧ ¬ MEM v (MAP FST l)
            ⇒ (Letrec l (Lam v e) ≅? Lam v (Letrec l e)) b
Proof
  rw [exp_eq_def, bind_def] >> IF_CASES_TAC >>
  gvs [app_bisimilarity_eq, exp_eq_refl] >>
  rpt $ irule_at Any IMP_closed_subst >>
  gvs [subst_def, FDIFF_DOMSUB, MAP_subst_fdomsub] >>
  irule_at Any Letrec_Lam >>
  gvs [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, EVERY_EL, EL_MAP] >>
  rw [FRANGE_FLOOKUP]
  >- (rename1 ‘EL n l’ >> qabbrev_tac ‘p = EL n l’ >>
      PairCases_on ‘p’ >>
      ‘∀v. v ∈ FRANGE (FDIFF f (set (MAP FST l))) ⇒ closed v’
        by (rw [FRANGE_FLOOKUP, FLOOKUP_FDIFF] >>
            first_x_assum irule >>
            pop_assum $ irule_at Any) >>
      gvs [freevars_subst, SUBSET_DEF, IN_DIFF, FDOM_FDIFF] >>
      gen_tac >> rename1 ‘MEM x _’ >>
      last_x_assum $ qspecl_then [‘x’] assume_tac >>
      last_x_assum $ qspecl_then [‘x’] assume_tac >>
      rw [] >> gvs []
      >- (last_x_assum $ qspecl_then [‘freevars p1’] assume_tac >>
          gvs [MEM_MAP] >> pop_assum $ qspecl_then [‘EL n l’] assume_tac >>
          gvs [EL_MEM])
      >- (last_x_assum $ qspecl_then [‘freevars p1’] assume_tac >>
          gvs [MEM_MAP] >> pop_assum $ qspecl_then [‘EL n l’] assume_tac >>
          gvs [EL_MEM]) >>
      gvs [MEM_EL] >>
      first_assum $ irule_at Any >>
      rw [EL_MAP] >>
      rename1 ‘FST p2’ >> PairCases_on ‘p2’ >> fs [])
  >- (strip_tac >> last_x_assum irule >>
      gvs [MEM_EL] >> first_assum $ irule_at Any >>
      gvs [EL_MAP] >> rename1 ‘FST p’ >> PairCases_on ‘p’ >>
      fs [])
QED

Theorem Letrec_not_in_freevars:
  ∀l e b. EVERY (λv. v ∉ freevars e) (MAP FST l) ⇒ (Letrec l e ≅? e) b
Proof
  rw [exp_eq_def, bind_def] >> IF_CASES_TAC >>
  gvs [app_bisimilarity_eq, exp_eq_refl] >>
  rpt $ irule_at Any IMP_closed_subst >>
  gvs [subst_def, FRANGE_FLOOKUP] >>
  irule exp_eq_trans >>
  irule_at Any beta_equality_Letrec >>
  conj_asm1_tac
  >- (rw [EVERY_EL, EL_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      rename1 ‘EL n l’ >> qabbrev_tac ‘p = EL n l’ >> PairCases_on ‘p’ >>
      ‘∀v. v ∈ FRANGE (FDIFF f (set (MAP FST l))) ⇒ closed v’
        by (rw [FRANGE_FLOOKUP, FLOOKUP_FDIFF] >>
            first_x_assum irule >>
            pop_assum $ irule_at Any) >>
      gvs [freevars_subst, SUBSET_DEF, IN_DIFF, FDOM_FDIFF] >>
      gen_tac >> rename1 ‘MEM x _’ >>
      last_x_assum $ qspecl_then [‘x’] assume_tac >>
      rw [] >> gvs []
      >- (first_x_assum $ qspecl_then [‘freevars p1’] assume_tac >>
          gvs [MEM_MAP] >> pop_assum $ qspecl_then [‘EL n l’] assume_tac >>
          gvs [EL_MEM]) >>
      gvs [MEM_EL] >>
      first_assum $ irule_at Any >> rw [EL_MAP] >>
      rename1 ‘FST p2’ >> PairCases_on ‘p2’ >> fs []) >>
  dxrule_then assume_tac subst_funs_eq_subst >>
  qspecl_then [‘f’, ‘e’, ‘set (MAP FST l)’] assume_tac $ GSYM subst_FDIFF' >>
  gvs [EVERY_MEM] >>
  rw [exp_eq_refl, IMP_closed_subst, FRANGE_FLOOKUP]
QED

Theorem Let_Letrec:
  ∀s l e1 e2 b. EVERY (λe. s ∉ freevars e) (MAP SND l) ∧ ¬MEM s (MAP FST l)
                ∧ EVERY (λv. v ∉ freevars e1) (MAP FST l)
                ⇒ (Let s e1 (Letrec l e2) ≅? Letrec l (Let s e1 e2)) b
Proof
  rw [] >>
  irule exp_eq_trans >>
  irule_at (Pos hd) exp_eq_App_cong >>
  irule_at (Pos hd) $ iffLR exp_eq_sym >>
  irule_at Any Letrec_Lam_weak >> fs [] >>
  irule_at Any exp_eq_refl >>
  irule $ iffLR exp_eq_sym >>
  irule exp_eq_trans >>
  irule_at Any Letrec_App >>
  irule exp_eq_App_cong >>
  gvs [exp_eq_refl, Letrec_not_in_freevars]
QED

Theorem Let_Letrec2:
  ∀s l e1 e2 b. ¬MEM s (MAP FST l)
                ∧ EVERY (λv. v ∉ freevars e1) (MAP FST l)
                ⇒ (Let s e1 (Letrec l e2) ≅? Letrec (MAP (λ(v, e). (v, Let s e1 e)) l)  (Let s e1 e2)) b
Proof
  rw [exp_eq_def, bind_def] >> IF_CASES_TAC >>
  gvs [app_bisimilarity_eq, exp_eq_refl] >>
  rpt $ irule_at Any IMP_closed_subst >>
  gvs [subst_def, FRANGE_FLOOKUP] >>
  irule exp_eq_trans >>
  irule_at Any beta_equality >>
  irule_at Any IMP_closed_subst >>
  gvs [FRANGE_FLOOKUP, subst1_def, MAP_MAP_o] >>
  rename1 ‘MEM s (MAP (FST o (λ(f', e). (f', subst (FDIFF (f \\ s) (set (MAP FST l))) e))) l)’ >>
  ‘¬MEM s (MAP (FST o (λ(f', e). (f', subst (FDIFF (f \\ s) (set (MAP FST l))) e))) l)’
    by (strip_tac >> first_x_assum irule >>
        gvs [MEM_EL] >> first_assum $ irule_at Any >> gvs [EL_MAP] >>
        rename1 ‘EL n l’ >> qabbrev_tac ‘p = EL n l’ >> PairCases_on ‘p’ >> fs []) >>
  gvs [] >> irule exp_eq_Letrec_cong2 >>
  irule_at Any fmap_rel_FUPDATE_LIST_same >> irule_at Any LIST_EQ >>
  rw [EL_MAP, fmap_rel_FEMPTY, LIST_REL_EL_EQN]
  >~[‘FST (_ (_ p)) = FST (_ (_ p))’]
  >- (PairCases_on ‘p’ >> fs [])
  >~[‘SND (_ (_ p)) ≅? SND (_ (_ p))’]
  >- (PairCases_on ‘p’ >> gvs [subst_def] >>
      gvs [EVERY_MEM] >> drule_then assume_tac $ GSYM subst_FDIFF' >>
      ‘MAP (FST o (λ(v, e). (v, Let s e1 e))) l = MAP FST l’
        by (irule LIST_EQ >> rw [EL_MAP] >> rename1 ‘FST (_ p)’ >> PairCases_on ‘p’ >> fs []) >>
      gvs [FDIFF_def, fmap_domsub, INTER_COMM, Once exp_eq_sym] >>
      irule beta_equality >>
      gvs [IMP_closed_subst, FRANGE_FLOOKUP])
  >- (‘MAP (FST o (λ(v, e). (v, Let s e1 e))) l = MAP FST l’
        by (irule LIST_EQ >> rw [EL_MAP] >> rename1 ‘FST (_ p)’ >> PairCases_on ‘p’ >> fs []) >>
      gvs [EVERY_MEM] >> drule_then assume_tac $ GSYM subst_FDIFF' >>
      gvs [FDIFF_def, fmap_domsub, INTER_COMM, Once exp_eq_sym] >>
      irule beta_equality >> gvs [IMP_closed_subst, FRANGE_FLOOKUP])
QED

Theorem Let_Let:
  ∀v w e1 e2 e3 b. v ≠ w ∧ v ∉ freevars e2 ∧ w ∉ freevars e1 ⇒
                   (Let v e1 (Let w e2 e3) ≅? Let w e2 (Let v e1 e3)) b
Proof
  rw []
  \\ irule eval_IMP_exp_eq
  \\ rw [subst_def]
  \\ rename1 ‘subst (f \\ _ \\ _)’
  \\ ‘∀v. v ∈ FRANGE f ⇒ closed v’ by (rw [FRANGE_FLOOKUP])
  \\ drule $ GSYM subst_fdomsub
  \\ last_x_assum assume_tac
  \\ last_x_assum assume_tac
  \\ drule $ GSYM subst_fdomsub
  \\ rw [eval_Let, subst_def, bind1_def, IMP_closed_subst, DOMSUB_COMMUTES]
  \\ AP_TERM_TAC
  \\ rw [fmap_domsub, COMPL_UNION]
  \\ irule subst1_subst1
  \\ gvs [IMP_closed_subst]
QED

Theorem Let_Apps:
  ∀eL v e1 e2 b. (Let v e1 (Apps e2 eL) ≅? Apps (Let v e1 e2) (MAP (Let v e1) eL)) b
Proof
  Induct >> rw [Apps_def, exp_eq_refl] >>
  irule exp_eq_trans >> pop_assum $ irule_at Any >>
  irule exp_eq_Apps_cong >> gvs [Let_App, exp_eq_l_refl]
QED

Theorem Seq_App:
  ∀b. (App (Seq p f) e ≅? Seq p (App f e)) b
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_App, eval_wh_Seq]
  \\ fs []
QED

Theorem Apps_Seq:
  ∀eL e e' b. (Apps (Seq e e') eL ≅? Seq e (Apps e' eL)) b
Proof
  Induct >> rw [Apps_def, exp_eq_refl] >>
  irule exp_eq_trans >> pop_assum $ irule_at Any >>
  irule exp_eq_Apps_cong >> gvs [exp_eq_l_refl, Seq_App]
QED

Theorem Proj_Seq2:
  ∀b. (Proj x i (Seq e e') ≅? Seq e (Proj x i e')) b
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_Proj, eval_wh_Seq]
  \\ fs []
QED

Theorem If_Seq:
  ∀e e' e'' e''' b. (If (Seq e e') e'' e''' ≅? Seq e (If e' e'' e''')) b
Proof
  rpt gen_tac
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_If, eval_wh_Seq]
  \\ fs []
QED

Theorem Seq_comm:
  Seq (Seq x y) z ≈ Seq (Seq y x) z
Proof
  irule no_err_eval_wh_IMP_exp_eq
  \\ rw [subst_def, no_err_eval_wh_def, eval_wh_Seq]
  \\ fs []
  \\ Cases_on ‘eval_wh (subst f x)’
  \\ Cases_on ‘eval_wh (subst f y)’
  \\ fs []
QED

Theorem If_Seq2:
  ∀e ec et ee.  If ec (Seq e et) (Seq e ee) ≈ Seq e (If ec et ee)
Proof
  rpt gen_tac
  \\ irule no_err_eval_wh_IMP_exp_eq
  \\ rw [no_err_eval_wh_def, freevars_def, subst_def, eval_wh_If, eval_wh_Seq]
  \\ fs []
QED

Theorem IsEq_Seq:
  ∀b e e' n i. (IsEq n i (Seq e e') ≅? Seq e (IsEq n i e')) b
Proof
  rpt gen_tac
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_IsEq, eval_wh_Seq]
  \\ fs []
QED

Definition well_written_def:
  well_written (Cons s) l = T ∧
  well_written (Proj s i) [e] = T ∧
  well_written (IsEq s i) [e] = T ∧
  well_written If [e; e'; e''] = T ∧
  well_written Seq [e; e'] = T ∧
  well_written (AtomOp op) l = T ∧
  well_written _ _ = F
End

Theorem not_well_written_is_fail:
  ∀b ope l.
    ¬ well_written ope l ⇒
    (Prim ope l ≅? Fail) b
Proof
  rw []
  \\ Cases_on ‘ope’
  \\ fs [well_written_def]
  \\ Cases_on ‘l’
  >>~[‘Prim _ [] ≅? Fail’]
  >- (fs [exp_eq_refl])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  \\ rename1 ‘hd::tl’
  \\ Cases_on ‘tl’
  \\ fs [well_written_def]
  >>~[‘Prim _ [hd]’]
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  >- (irule eval_wh_IMP_exp_eq
     \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  \\ rename1 ‘h0::h1::tl’
  \\ Cases_on ‘tl’
  \\ fs [well_written_def]
  >~[‘Prim If (h0::h1::h2::tl)’]
  >- (Cases_on ‘tl’
      \\ fs [well_written_def]
      \\ irule eval_wh_IMP_exp_eq
      \\ fs [subst_def, eval_wh_def, eval_wh_to_def])
  \\ irule eval_wh_IMP_exp_eq
  \\ fs [subst_def, eval_wh_def, eval_wh_to_def]
QED

(* Part on context *)

Theorem eq_when_applied_refl:
  ∀c e len. eq_when_applied c e e len
Proof
  Induct
  \\ gvs [eq_when_applied_def, exp_eq_refl]
QED

Theorem eq_when_applied_l_refl:
  ∀c l len. LIST_REL (λe1 e2. eq_when_applied c e1 e2 len) l l
Proof
  gen_tac
  \\ Induct
  \\ fs [eq_when_applied_refl]
QED

Theorem eq_when_applied_sym:
  ∀c e1 e2 len. eq_when_applied c e1 e2 len ⇔ eq_when_applied c e2 e1 len
Proof
  Induct
  \\ rw [] \\ eq_tac
  \\ gvs [eq_when_applied_def, exp_eq_sym]
QED

Theorem eq_when_applied_trans:
  ∀c e1 e2 e3 len. eq_when_applied c e1 e2 len
                   ∧ eq_when_applied c e2 e3 len
                   ⇒ eq_when_applied c e1 e3 len
Proof
  Induct
  \\ rw []
  \\ gvs [eq_when_applied_def] \\ rw []
  >- (irule exp_eq_trans
      \\ pop_assum $ irule_at Any \\ fs [])
  \\ last_x_assum irule
  \\ first_x_assum $ irule_at Any
  \\ gvs []
QED

Theorem exp_eq_in_ctxt_refl:
  ∀c e. exp_eq_in_ctxt c e e
Proof
  Induct
  \\ gvs [exp_eq_in_ctxt_def, exp_eq_refl]
QED

Theorem exp_eq_in_ctxt_l_refl:
  ∀c l. LIST_REL (exp_eq_in_ctxt c) l l
Proof
  gen_tac
  \\ Induct
  \\ fs [exp_eq_in_ctxt_refl]
QED

Theorem exp_eq_in_ctxt_sym:
  ∀c e1 e2. exp_eq_in_ctxt c e1 e2 ⇔ exp_eq_in_ctxt c e2 e1
Proof
  gvs [eq_when_applied_0, eq_when_applied_sym]
QED

Theorem exp_eq_in_ctxt_trans:
  ∀c e1 e2 e3. exp_eq_in_ctxt c e1 e2 ∧ exp_eq_in_ctxt c e2 e3 ⇒ exp_eq_in_ctxt c e1 e3
Proof
  rw [eq_when_applied_0] >>
  dxrule_then (dxrule_then irule) eq_when_applied_trans
QED

Theorem last_exists:
  ∀l. LENGTH l > 0 ⇒ ∃x t. l = SNOC x t
Proof
  Induct
  \\ fs []
  \\ rw []
  \\ rename1 ‘hd::tl’
  \\ Cases_on ‘tl’
  \\ fs []
QED

Theorem last_Apps:
  ∀l x e. Apps e (l ++ [x]) = App (Apps e l) x
Proof
  Induct
  \\ fs [Apps_def]
QED

Theorem eq_when_applied_SUC:
  ∀c e1 e2 len. eq_when_applied c e1 e2 len 
                ⇒ eq_when_applied c e1 e2 (SUC len)
Proof
  Induct >> gvs [eq_when_applied_def] >>
  rpt gen_tac >> strip_tac >> rw [] >>
  qspecl_then [‘l’] assume_tac last_exists >> gvs [last_Apps] >>
  irule exp_eq_App_cong >>
  last_x_assum $ irule_at Any >>
  gvs [exp_eq_refl]
QED

Theorem eq_when_applied_bigger:
  ∀len2 len1 c e1 e2. eq_when_applied c e1 e2 len1 ∧ len1 ≤ len2
                      ⇒ eq_when_applied c e1 e2 len2
Proof
  Induct >> gvs [] >> gen_tac >>
  rename1 ‘len1 ≤ SUC len2’ >> Cases_on ‘len1 = SUC len2’ >> rw [] >>
  irule eq_when_applied_SUC >> last_x_assum $ dxrule_then irule >>
  gvs []
QED

Theorem exp_eq_in_ctxt_IMP_eq_when_applied:
  ∀c e1 e2 len. exp_eq_in_ctxt c e1 e2 ⇒ eq_when_applied c e1 e2 len
Proof
  Induct >>
  gvs [exp_eq_in_ctxt_def, eq_when_applied_def, exp_eq_Apps_cong, exp_eq_l_refl]
QED

Theorem exp_eq_IMP_exp_eq_in_ctxt:
  ∀c e e'. e ≈ e' ⇒ exp_eq_in_ctxt c e e'
Proof
  Induct
  \\ gvs [exp_eq_in_ctxt_def]
  \\ rw []
  \\ first_x_assum irule
  \\ gvs [exp_eq_Letrec_cong, exp_eq_App_cong, exp_eq_Lam_cong, exp_eq_refl, exp_eq_l_refl]
QED

Theorem exp_eq_IMP_eq_when_applied:
  ∀c e e' len. e ≈ e' ⇒ eq_when_applied c e e' len
Proof
  rw [] \\ irule exp_eq_in_ctxt_IMP_eq_when_applied
  \\ gvs [exp_eq_IMP_exp_eq_in_ctxt]
QED

Theorem exp_eq_in_ctxt_Prim:
  ∀c eL eL' ope. LIST_REL (exp_eq_in_ctxt c) eL eL'
                 ⇒ exp_eq_in_ctxt c (Prim ope eL) (Prim ope eL')
Proof
  Induct
  \\ gvs [exp_eq_in_ctxt_def, exp_eq_refl, exp_eq_Prim_cong]
  \\ rw []
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at Any exp_eq_in_ctxt_trans
  \\ last_x_assum $ irule_at Any
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  >~[‘Letrec’]
  >- (irule_at Any Letrec_Prim
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any Letrec_Prim
      \\ gvs [LIST_REL_EL_EQN, EL_MAP, exp_eq_in_ctxt_def])
  \\ irule_at Any Let_Prim
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ irule_at Any Let_Prim
  \\ gvs [LIST_REL_EL_EQN, EL_MAP, exp_eq_in_ctxt_def]
QED

Theorem Let_App_w_app:
  ∀c s e1 e2 e3 len. eq_when_applied c (Let s e1 (App e2 e3)) (App (Let s e1 e2) (Let s e1 e3)) len
Proof
  rpt gen_tac
  \\ irule exp_eq_IMP_eq_when_applied
  \\ gvs [Let_App]
QED

Theorem Let_App_in_ctxt:
  ∀c s e1 e2 e3. exp_eq_in_ctxt c (Let s e1 (App e2 e3)) (App (Let s e1 e2) (Let s e1 e3))
Proof
  gvs [eq_when_applied_0, Let_App_w_app]
QED

Theorem eq_when_applied_App:
  ∀c f1 f2 e1 e2 len. eq_when_applied c f1 f2 (SUC len) ∧ exp_eq_in_ctxt c e1 e2
                  ⇒ eq_when_applied c (App f1 e1) (App f2 e2) len
Proof
  Induct
  \\ gvs [eq_when_applied_def,exp_eq_App_cong, GSYM Apps_def, exp_eq_in_ctxt_def]
  \\ rw []
  >- (irule exp_eq_trans >> last_x_assum $ irule_at Any >>
      gvs [exp_eq_Apps_cong, exp_eq_l_refl, exp_eq_App_cong, exp_eq_refl])
  \\ irule eq_when_applied_trans
  \\ irule_at Any eq_when_applied_trans
  \\ last_x_assum $ irule_at (Pos $ el 2)
  \\ first_x_assum $ irule_at (Pos $ el 2)
  \\ rpt $ last_assum $ irule_at Any
  \\ irule_at (Pos last) $ iffLR eq_when_applied_sym
  \\ rpt $ irule_at Any Let_App_w_app
  \\ fs [Letrec_App, exp_eq_IMP_eq_when_applied]
QED

Theorem SUC_ADD:
  ∀n m. SUC (n + m) = n + SUC m
Proof
  gvs []
QED

Theorem eq_when_applied_Apps:
  ∀eL eL' e e' c len. LIST_REL (exp_eq_in_ctxt c) eL eL' ⇒ eq_when_applied c e e' (len + LENGTH eL)
                  ⇒ eq_when_applied c (Apps e eL) (Apps e' eL') len
Proof
  Induct
  >- (Cases
      \\ fs [Apps_def])
  \\ gen_tac
  \\ Cases
  \\ rw [Apps_def]
  \\ first_x_assum irule
  \\ fs []
  \\ irule eq_when_applied_App
  \\ gvs [SUC_ADD]
QED

Theorem Let_freevars_in_ctxt:
  ∀c v e e'. v ∉ freevars e' ⇒ exp_eq_in_ctxt c (Let v e e') e'
Proof
  rw []
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_thm, bind1_def, GSYM subst_fdomsub]
  >- (AP_TERM_TAC
      \\ irule subst1_ignore
      \\ rename1 ‘subst f e2’
      \\ qsuff_tac ‘closed (subst f e2)’
      >- rw [closed_def]
      \\ irule IMP_closed_subst
      \\ rw []
      \\ first_x_assum $ irule_at Any
      \\ fs [FRANGE_FLOOKUP]
      \\ pop_assum $ irule_at Any)
  \\ gvs [IMP_closed_subst, FRANGE_FLOOKUP]
QED

Theorem Let_freevars_w_app:
  ∀c v e e' len. v ∉ freevars e' ⇒ eq_when_applied c (Let v e e') e' len
Proof
  rw [] >>
  irule exp_eq_in_ctxt_IMP_eq_when_applied >>
  gvs [Let_freevars_in_ctxt]
QED

Theorem Let_Let_in_ctxt:
  ∀v w e1 e2 e3 c. v ≠ w ∧ v ∉ freevars e2 ∧ w ∉ freevars e1 ⇒
                   exp_eq_in_ctxt c (Let v e1 (Let w e2 e3)) (Let w e2 (Let v e1 e3))
Proof
  rw []
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ gvs [Let_Let]
QED

Theorem Let_Let_eq_w_app:
  ∀v w e1 e2 e3 c len. v ≠ w ∧ v ∉ freevars e2 ∧ w ∉ freevars e1 ⇒
                   eq_when_applied c (Let v e1 (Let w e2 e3)) (Let w e2 (Let v e1 e3)) len
Proof
  rw []
  \\ irule exp_eq_IMP_eq_when_applied
  \\ gvs [Let_Let]
QED

Theorem eq_when_applied_Lam:
  ∀c s e1 e2 len. eq_when_applied (IsFree s c) e1 e2 len
              ⇒ eq_when_applied c (Lam s e1) (Lam s e2) (SUC len)
Proof
  Induct
  \\ fs[eq_when_applied_def] \\ rw [eq_when_applied_def]
  >- (cheat \\ irule exp_eq_Apps_cong
      \\ rw [exp_eq_Lam_strong, exp_eq_l_refl]
      \\ irule exp_eq_trans
      \\ irule_at Any beta_equality
      \\ fs []
      \\ irule $ iffLR exp_eq_sym
      \\ irule exp_eq_trans
      \\ irule_at (Pos last) beta_equality
      \\ fs [exp_eq_sym])
  >>~ [‘Letrec l (Lam w _)’]
  >- (‘∃s. s ∉ {w} ∪ set (MAP FST l) ∪ BIGUNION (set (MAP (freevars o SND) l))
             ∪ freevars e1 ∪ freevars e2’
        by  (‘INFINITE 𝕌(:string)’ by simp [] \\ dxrule_then assume_tac $ iffLR NOT_IN_FINITE
             \\ pop_assum $ irule_at Any \\ rw [FINITE_UNION, FINITE_BIGUNION, MEM_EL]
             \\ gvs [EL_MAP])
      \\ irule eq_when_applied_trans
      \\ irule_at (Pos hd) exp_eq_IMP_eq_when_applied
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any exp_eq_l_refl
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ fs [] \\ first_assum $ irule_at Any
      \\ fs []
      \\ irule eq_when_applied_trans
      \\ irule_at (Pos hd) exp_eq_IMP_eq_when_applied
      \\ irule_at Any Letrec_Lam_weak
      \\ fs [] \\ conj_tac
      >- (rw [EVERY_MEM]
          \\ rename1 ‘MEM e _’ \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
          \\ fs [MEM_MAP]
          \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
          \\ rw [])
      \\ irule eq_when_applied_trans
      \\ irule_at (Pos last) exp_eq_IMP_eq_when_applied
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ irule_at Any exp_eq_l_refl
      \\ first_assum $ irule_at Any \\ fs []
      \\ irule eq_when_applied_trans
      \\ irule_at (Pos last) exp_eq_IMP_eq_when_applied
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any Letrec_Lam_weak
      \\ fs []
      \\ conj_tac
      >- (rw [EVERY_MEM]
          \\ rename1 ‘MEM e _’ \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
          \\ fs [MEM_MAP]
          \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
          \\ rw [])
      \\ last_x_assum irule \\ rw []
      \\ irule eq_when_applied_trans
      \\ irule_at Any eq_when_applied_trans
      \\ last_x_assum $ irule_at Any
      \\ irule_at (Pos last) $ iffLR eq_when_applied_sym
      \\ rename1 ‘Let s e3 _’ \\ qexists_tac ‘e3’ \\ fs []
      \\ conj_tac
      \\ irule exp_eq_IMP_eq_when_applied
      \\ irule exp_eq_trans
      \\ irule_at Any Let_Letrec
      \\ fs []
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any exp_eq_App_cong
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ rw [EVERY_MEM, exp_eq_refl, exp_eq_l_refl] \\ fs [closed_def]
      \\ rename1 ‘MEM e _’
      \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
      \\ fs [MEM_MAP]
      \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
      \\ rw [])
  \\ rename1 ‘Let v e3 (Lam w _)’
  \\ ‘∃s. s ∉ {v} ∪ {w} ∪ freevars e3 ∪ freevars e1 ∪ freevars e2’
    by (‘INFINITE 𝕌(:string)’ by simp []
        \\ gvs [NOT_IN_FINITE])
  \\ irule eq_when_applied_trans
  \\ irule_at (Pos hd) exp_eq_IMP_eq_when_applied
  \\ irule_at Any exp_eq_App_cong \\ irule_at Any exp_eq_Lam_cong
  \\ irule_at Any exp_alpha_exp_eq
  \\ irule_at Any exp_alpha_Alpha
  \\ fs [] \\ first_assum $ irule_at Any
  \\ irule_at Any exp_eq_refl \\ fs []
  \\ irule eq_when_applied_trans
  \\ irule_at (Pos hd) exp_eq_IMP_eq_when_applied
  \\ irule_at Any Let_Lam_weak \\ fs []
  \\ irule eq_when_applied_trans
  \\ irule_at (Pos last) exp_eq_IMP_eq_when_applied
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ irule_at Any exp_eq_App_cong \\ irule_at Any exp_eq_Lam_cong
  \\ irule_at Any exp_alpha_exp_eq
  \\ irule_at Any exp_alpha_Alpha
  \\ first_assum $ irule_at Any
  \\ irule_at Any exp_eq_refl \\ fs []
  \\ irule eq_when_applied_trans
  \\ irule_at (Pos last) exp_eq_IMP_eq_when_applied
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ irule_at Any Let_Lam_weak \\ fs []
  \\ last_x_assum $ irule_at Any
  \\ rw []
  \\ irule eq_when_applied_trans \\ irule_at Any eq_when_applied_trans
  \\ last_x_assum $ irule_at Any
  \\ rpt $ irule_at Any exp_eq_IMP_eq_when_applied
  \\ irule_at (Pos $ el 2) $ iffLR exp_eq_sym
  \\ irule_at (Pos $ el 2) exp_eq_trans \\ irule_at (Pos $ el 3) exp_eq_trans
  \\ irule_at (Pos $ el 2) Let_Let \\ irule_at (Pos $ el 6) Let_Let
  \\ rpt $ irule_at Any exp_eq_App_cong
  \\ rpt $ irule_at Any exp_eq_refl
  \\ rpt $ irule_at Any exp_eq_Lam_cong
  \\ rpt $ irule_at Any exp_eq_App_cong
  \\ rpt $ irule_at Any exp_eq_refl
  \\ fs [closed_def] \\ conj_tac
  \\ irule exp_alpha_exp_eq
  \\ irule exp_alpha_Alpha
  \\ fs []
QED

Theorem eq_when_applied_Lams:
  ∀vl c e e' len. eq_when_applied (FOLDL (λc n. IsFree n c) c vl) e e' len ⇒
              eq_when_applied c (Lams vl e) (Lams vl e') len
Proof
  Induct
  \\ rw [Lams_def]
  \\ irule eq_when_applied_Lam
  \\ last_x_assum $ irule_at Any
  \\ fs []
QED

Theorem exp_eq_in_IsFree_Bind:
  ∀e1 e2 e3 c v. exp_eq_in_ctxt (IsFree v c) e1 e2 ⇒ exp_eq_in_ctxt (Bind v e3 c) e1 e2
Proof
  rpt strip_tac >>
  gvs [exp_eq_in_ctxt_def, exp_eq_in_ctxt_App, exp_eq_in_ctxt_Lam, exp_eq_in_ctxt_refl]
QED

Theorem Apps_Seq_in_ctxt:
  ∀e e2 eL c. exp_eq_in_ctxt c (Apps (Seq e e2) eL) (Seq e (Apps e2 eL))
Proof
  rw [exp_eq_IMP_exp_eq_in_ctxt, Apps_Seq]
QED

Theorem Let_Apps_in_ctxt:
  ∀v e1 e2 eL c. exp_eq_in_ctxt c (Let v e1 (Apps e2 eL)) (Apps (Let v e1 e2) (MAP (Let v e1) eL))
Proof
  rw [Let_Apps, exp_eq_IMP_exp_eq_in_ctxt]
QED

Theorem Letrec_Apps:
  ∀l bL b e. (Letrec bL (Apps e l) ≅? Apps (Letrec bL e) (MAP (Letrec bL) l)) b
Proof
  Induct >> gvs [exp_eq_refl, Apps_def] >>
  rpt gen_tac >>
  irule exp_eq_trans >> pop_assum $ irule_at Any >>
  irule exp_eq_Apps_cong >>
  fs [exp_eq_l_refl, Letrec_App]
QED

Theorem Letrec_Apps_in_ctxt:
  ∀l b e c. exp_eq_in_ctxt c (Letrec b (Apps e l)) (Apps (Letrec b e) (MAP (Letrec b) l))
Proof
  gvs [exp_eq_IMP_exp_eq_in_ctxt, Letrec_Apps]
QED

Definition unfold_ctxt_def:
  unfold_ctxt Nil e = e ∧
  unfold_ctxt (IsFree v c) e = Lam v (unfold_ctxt c e) ∧
  unfold_ctxt (Bind v e c) e2 = Let v e (unfold_ctxt c e2) ∧
  unfold_ctxt (RecBind bL c) e = Letrec bL (unfold_ctxt c e)
End

Definition concat_ctxt_def:
  concat_ctxt Nil c = c ∧
  concat_ctxt (IsFree v c1) c2 = concat_ctxt c1 (IsFree v c2) ∧
  concat_ctxt (Bind v e c1) c2 = concat_ctxt c1 (Bind v e c2) ∧
  concat_ctxt (RecBind bL c1) c2 = concat_ctxt c1 (RecBind bL c2)
End

Definition not_bound_in_ctxt_def:
  not_bound_in_ctxt Nil v = T ∧
  not_bound_in_ctxt (IsFree v1 c) v2 = (v1 ≠ v2 ∧ not_bound_in_ctxt c v2) ∧
  not_bound_in_ctxt (Bind v1 e c) v2 = (v1 ≠ v2 ∧ not_bound_in_ctxt c v2) ∧
  not_bound_in_ctxt (RecBind bL c) v = (not_bound_in_ctxt c v ∧ ¬MEM v (MAP FST bL))
End

Theorem Let_stay:
  ∀v e b. v ∉ freevars e ⇒ (Let v e (Var v) ≅? Let v e e) b
Proof
  rw [] >> irule exp_eq_trans >>
  irule_at Any Let_Var >>
  irule eval_IMP_exp_eq >>
  rw [eval_thm, subst_def, GSYM subst_fdomsub, bind1_def, subst1_ignore, closed_def, IMP_closed_subst,
      FRANGE_FLOOKUP]
QED

Theorem exp_eq_in_ctxt_unfold:
  ∀c2 w e' c1. not_bound_in_ctxt c2 w ∧ (∀v. v ∈ freevars e' ⇒ not_bound_in_ctxt c2 v) ∧ w ∉ freevars e'
              ⇒ exp_eq_in_ctxt (Bind w e' c1) (unfold_ctxt c2 (Var w)) (unfold_ctxt c2 e')
Proof
  Induct >> rw [not_bound_in_ctxt_def, exp_eq_in_ctxt_def, unfold_ctxt_def]
  >- gvs [exp_eq_in_ctxt_def, exp_eq_IMP_exp_eq_in_ctxt, Let_stay] >>
  irule exp_eq_in_ctxt_trans >> irule_at Any exp_eq_in_ctxt_trans >>
  irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at (Pos hd) $ iffLR exp_eq_sym >~[‘Letrec’]
  >- (rpt $ irule_at Any Let_Letrec2 >>
      gvs [GSYM exp_eq_in_ctxt_def, EVERY_MEM] >>
      rw [] >> strip_tac >> first_x_assum $ dxrule_then assume_tac >>
      gvs [])
  >- (rpt $ irule_at Any Let_Lam_weak >>
      irule_at Any exp_eq_in_ctxt_Lam >>
      gvs [GSYM exp_eq_in_ctxt_def] >>
      strip_tac >> first_x_assum $ dxrule_then assume_tac >> fs [])
  >- cheat
QED

(** end ctxt **)

Definition Projs_def:
  Projs [] e = e ∧
  Projs ((x,i)::ps) e = Projs ps (Proj x i e)
End

Definition is_bot_def:
  is_bot e = (e = wh_Diverge ∨ e = wh_Error)
End

Theorem is_bot_continuous:
  ∀e k k2. k2 ≤ k ∧ is_bot (eval_wh_to k e) ⇒ is_bot (eval_wh_to k2 e)
Proof
  rw [is_bot_def]
  \\ Cases_on ‘eval_wh_to k2 e = wh_Diverge’
  \\ fs []
  \\ qspecl_then [‘k’, ‘e’, ‘k2’] assume_tac eval_wh_inc
  \\ gvs []
QED

Theorem demands_proj_end:
  ∀ ps x i e. Projs (ps++[(x,i)]) e = Proj x i (Projs ps e)
Proof
  Induct THEN1 rw [Projs_def]
  \\ gen_tac \\ rename1 ‘hd::ps’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
QED

Theorem double_Projs:
  ∀ps' ps e. Projs (ps' ++ ps) e = Projs ps (Projs ps' e)
Proof
  Induct >- rw [Projs_def]
  \\ gen_tac \\ rename1 ‘hd::ps'’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
QED

Theorem exp_eq_Projs_cong:
  ∀ps x y b. (x ≅? y) b ⇒ (Projs ps x ≅? Projs ps y) b
Proof
  Induct \\ fs [Projs_def,FORALL_PROD]
  \\ rw [] \\ first_x_assum irule
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
QED

Theorem Projs_Seq:
  ∀ps e e' b. (Projs ps (Seq e e') ≅? Seq e (Projs ps e')) b
Proof
  Induct
  THEN1 (rw [Projs_def] \\ fs [exp_eq_refl])
  \\ rpt gen_tac
  \\ rename1 ‘hd::ps’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
  \\ irule exp_eq_trans \\ qexists_tac ‘Projs ps (Seq e (Proj hd0 hd1 e'))’
  \\ fs [Proj_Seq2, exp_eq_sym, exp_eq_Projs_cong, Seq_id]
QED

Theorem Let_Projs:
  ∀ps x w y b. (Let w y (Projs ps x) ≅? Projs ps (Let w y x)) b
Proof
  Induct \\ fs [Projs_def,exp_eq_refl,FORALL_PROD] \\ rw []
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Let w y (Proj p_1 p_2 x))’
  \\ conj_tac THEN1 fs []
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Prim_alt]
QED

Theorem Letrec_Projs:
  ∀ps x bL b. (Letrec bL (Projs ps x) ≅? Projs ps (Letrec bL x)) b
Proof
  Induct \\ fs [Projs_def,exp_eq_refl,FORALL_PROD] \\ rw []
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Letrec bL (Proj p_1 p_2 x))’
  \\ conj_tac THEN1 fs []
  \\ irule exp_eq_Projs_cong
  \\ irule exp_eq_trans
  \\ irule_at Any Letrec_Prim
  \\ gvs [exp_eq_refl]
QED

Theorem Projs_subst:
  ∀ps f e. subst f (Projs ps e) = Projs ps (subst f e)
Proof
  Induct THEN1 rw [Projs_def]
  \\ gen_tac
  \\ rename1 ‘Projs (hd::_) _’
  \\ PairCases_on ‘hd’
  \\ rw [Projs_def, subst_def]
QED

val _ = set_fixity "demands" (Infixl 480);

Definition demands_def:
  (e demands ((p,v), c)) = (exp_eq_in_ctxt c e (Seq (Projs p (Var v)) e))
End

val _ = set_fixity "needs" (Infixl 480);
Definition needs_def:
  (e needs ((ps, e'), c)) = (exp_eq_in_ctxt c e (Seq (Projs ps e') e))
End

Theorem is_bot_IMP_IMP_needs:
  ∀e ps e' c. (∀f. is_bot (eval_wh (subst f (Projs ps e'))) ⇒ is_bot (eval_wh (subst f e))) ⇒ e needs ((ps, e'), c)
Proof
  rw [needs_def]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule no_err_eval_wh_IMP_exp_eq
  \\ rw [no_err_eval_wh_def, subst_def, eval_wh_thm]
  \\ first_x_assum $ qspecl_then [‘f’] assume_tac
  \\ gvs [is_bot_def]
QED

Theorem needs_Var_is_demands:
  e needs ((ps, Var v), c) ⇔ e demands ((ps, v), c)
Proof
  rw [needs_def, demands_def] \\ fs []
QED

Theorem needs_in_IsFree_Bind:
  e needs (d, IsFree v c) ⇒ e needs (d, Bind v e2 c)
Proof
  PairCases_on ‘d’
  \\ rw [needs_def, exp_eq_in_IsFree_Bind]
QED

Theorem needs_IsFree_List_lemma:
  ∀d e c v e'.
    e needs (d, FOLDL (λc v. IsFree v c) (IsFree v c) l)
    ⇒ e needs (d, FOLDL (λc v. IsFree v c) (Bind v e' c) l)
Proof
  Induct_on ‘LENGTH l’ >> rw [needs_in_IsFree_Bind] >>
  qspecl_then [‘l’] assume_tac last_exists >>
  rename1 ‘e needs (d, _)’ >> PairCases_on ‘d’ >>
  gvs [FOLDL_APPEND, FORALL_PROD, needs_def, exp_eq_in_ctxt_def] >>
  rpt strip_tac >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt >>
  once_rewrite_tac [exp_eq_sym] >> irule_at Any exp_eq_trans >>
  irule_at (Pos hd) Let_Seq >>
  last_x_assum $ irule_at Any >> irule_at Any exp_eq_Prim_cong >>
  fs [exp_eq_refl] >> irule_at Any Let_Projs >>
  irule_at Any exp_eq_in_ctxt_trans >>
  first_x_assum $ irule_at Any >> fs [] >>
  irule exp_eq_IMP_exp_eq_in_ctxt >>
  irule exp_eq_trans >> irule_at Any Let_Seq >>
  gvs [Let_Projs, exp_eq_Prim_cong, exp_eq_refl]
QED

Theorem needs_IsFree_List:
  ∀l e c d. e needs (d, FOLDL (λc v. IsFree v c) c (MAP FST l))
            ⇒ e needs (d, FOLDL (λc (v, e). Bind v e c) c l)
Proof
  Induct >> rw [] >>
  last_x_assum $ irule_at Any >>
  rename1 ‘IsFree (FST h) c’ >> PairCases_on ‘h’ >>
  gvs [needs_IsFree_List_lemma]
QED

Theorem demands_in_IsFree_Bind:
  e demands (d, IsFree v c) ⇒ e demands (d, Bind v e2 c)
Proof
  PairCases_on ‘d’
  \\ rw [demands_def, exp_eq_in_IsFree_Bind]
QED

Theorem demands_IsFree_List:
  ∀d l e c. e demands (d, FOLDL (λc v. IsFree v c) c (MAP FST l))
            ⇒ e demands (d, FOLDL (λc (v, e). Bind v e c) c l)
Proof
  PairCases
  \\ metis_tac [needs_IsFree_List, needs_Var_is_demands]
QED

Theorem needs_refl:
  ∀e c. e needs (([],e), c)
Proof
  rw [needs_def, Projs_def]
  \\ metis_tac [Seq_id, exp_eq_sym, exp_eq_IMP_exp_eq_in_ctxt]
QED

Theorem needs_Var:
  (Var v) needs (([], Var v), c)
Proof
  fs [needs_refl]
QED

Theorem needs_Proj:
  e needs d ⇒ (Proj n i e) needs d
Proof
  PairCases_on ‘d’
  \\ rename1 ‘((ps, e'), _)’
  \\ rw [needs_def, Projs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq e (Proj n i e)’
  \\ conj_tac >- fs [Proj_Seq, exp_eq_IMP_exp_eq_in_ctxt]
  \\ qabbrev_tac ‘p = Projs ps e'’
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Seq p e) (Proj n i e)’
  \\ conj_tac
  >- (irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_in_ctxt_refl])
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq p (Seq e (Proj n i e))’
  \\ conj_tac >- fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc]
  \\ irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_IMP_exp_eq_in_ctxt, exp_eq_refl, Let_Var]
  \\ metis_tac [exp_eq_IMP_exp_eq_in_ctxt, Proj_Seq, exp_eq_sym]
QED

Theorem needs_Projs:
  ∀ps e d. e needs d ⇒ (Projs ps e) needs d
Proof
  Induct
  >- rw [Projs_def]
  \\ gen_tac \\ rename1 ‘(hd::ps)’ \\ PairCases_on ‘hd’
  \\ rw [Projs_def]
  \\ first_assum $ irule_at Any
  \\ irule needs_Proj
  \\ fs []
QED

Theorem needs_trans:
  e needs ((ps,e'), c) ∧ e' needs ((ps',e''), c) ⇒ e needs ((ps',e''), c)
Proof
  rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Seq (Projs ps' e'') (Projs ps e')) e’
  \\ conj_tac >-
   (irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_in_ctxt_refl]
    \\ assume_tac needs_Projs \\ metis_tac [needs_def])
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Projs ps' e'') (Seq (Projs ps e') e)’
  \\ conj_tac >- fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc]
  \\ irule exp_eq_in_ctxt_Prim
  \\ fs [exp_eq_in_ctxt_refl, exp_eq_in_ctxt_sym]
QED

Theorem needs_Projs_Var:
  (Proj s i (Var v)) needs (([(s,i)], Var v), c)
Proof
  rw [needs_def, Projs_def]
  \\ metis_tac [exp_eq_IMP_exp_eq_in_ctxt, Seq_id, exp_eq_sym]
QED

Theorem needs_Seq:
  e needs d ⇒ (Seq e e') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Seq (Projs d0 d1) e) e'’
  \\ conj_tac >-
   (irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_in_ctxt_refl])
  \\ fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc]
QED

Theorem needs_Seq2:
  e' needs d ⇒ (Seq e e') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq e (Seq (Projs d0 d1) e')’
  \\ fs [exp_eq_in_ctxt_Prim, exp_eq_in_ctxt_refl]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Seq_assoc
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Seq_comm
  \\ metis_tac [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc, exp_eq_sym]
QED

Theorem needs_Let1:
  e needs (d, c) ∧ e' demands (([],w), Bind w e c) ⇒ (Let w e e') needs (d, c)
Proof
  PairCases_on ‘d’
  \\ rw [demands_def,needs_def,Projs_def, exp_eq_in_ctxt_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ qabbrev_tac ‘p = (Projs d0 d1)’
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Let w e (Var w)) (Let w e e')’
  \\ conj_tac THEN1 fs [exp_eq_IMP_exp_eq_in_ctxt, Let_Seq]
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq e (Let w e e')’
  \\ conj_tac
  THEN1 (irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_IMP_exp_eq_in_ctxt, exp_eq_refl,Let_Var])
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Seq p e) (Let w e e')’
  \\ conj_tac THEN1
   (irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_in_ctxt_refl])
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq p (Seq e (Let w e e'))’
  \\ conj_tac THEN1 fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc]
  \\ irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_in_ctxt_refl]
  \\ once_rewrite_tac [exp_eq_in_ctxt_sym]
  \\ irule exp_eq_in_ctxt_trans
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_Prim_cong
  \\ fs [exp_eq_refl, Let_Var]
QED

Theorem needs_Let_Cons: (* expects program to be in ANF *)
  e demands (((s,LENGTH xs)::ps,w), Bind w (Cons s (xs ++ e' ::ys)) c) ⇒
  (Let w (Cons s (xs ++ e'::ys)) e) needs ((ps,e'), c)
Proof
  rw [demands_def,needs_def,Projs_def, exp_eq_in_ctxt_def]
  \\ qabbrev_tac ‘cons = (Cons s (xs ++ e'::ys))’
  \\ irule exp_eq_in_ctxt_trans
  \\ last_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_IMP_exp_eq_in_ctxt, exp_eq_in_ctxt_refl,Let_Var]
  \\ fs [GSYM Projs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Let_Projs
  \\ fs [Projs_def]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_Projs_cong \\ fs [exp_eq_refl,Let_Var]
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_Prim_cong \\ fs [PULL_EXISTS]
  \\ irule_at Any Let_Var
  \\ unabbrev_all_tac
  \\ fs [Proj_Cons]
QED

Theorem needs_Let_Proj: (* expects program to be in ANF *)
  e demands ((ps,w), Bind w (Proj s i e') c) ⇒
  (Let w (Proj s i e') e) needs (((s,i)::ps,e'), c)
Proof
  rw [demands_def,needs_def,Projs_def, exp_eq_in_ctxt_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ last_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Let w (Proj s i e') (Projs ps (Var w)))
                      (Let w (Proj s i e') e)’
  \\ conj_tac THEN1 fs [exp_eq_IMP_exp_eq_in_ctxt, Let_Seq]
  \\ irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_IMP_exp_eq_in_ctxt, exp_eq_refl,Let_Var]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Let w (Proj s i e') (Var w))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var]
QED

Theorem needs_App:
  f needs d ⇒ (App f e) needs d
Proof
  PairCases_on ‘d’ \\ rename1 ‘((ps,e'), c)’
  \\ rw [needs_def]
  \\ qabbrev_tac ‘proj = Projs ps e'’
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘App (Seq proj f) e’
  \\ conj_tac THEN1
   (irule exp_eq_in_ctxt_App \\ rw [exp_eq_in_ctxt_refl])
  \\ fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_App]
QED

Theorem needs_If:
  e needs d ⇒ (If e e' e'') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any If_Seq
  \\ irule exp_eq_in_ctxt_Prim
  \\ fs [exp_eq_in_ctxt_refl, exp_eq_in_ctxt_sym]
QED

Theorem needs_If2:
  et needs d ∧ ee needs d ⇒ (If ec et ee) needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any If_Seq2
  \\ irule exp_eq_in_ctxt_Prim
  \\ fs [exp_eq_in_ctxt_refl, exp_eq_in_ctxt_sym]
QED

Theorem needs_exp_eq:
  ∀d c e e'. exp_eq_in_ctxt c e e' ⇒ e needs (d, c) ⇒ e' needs (d, c)
Proof
  PairCases
  \\ rw [needs_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at Any $ iffLR exp_eq_in_ctxt_sym
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ pop_assum $ irule_at Any
  \\ fs [exp_eq_in_ctxt_Prim, exp_eq_in_ctxt_refl]
QED

        (********************************************)

Theorem demands_Var:
  (Var v) demands (([],v), c)
Proof
  metis_tac [needs_Var_is_demands, needs_Var]
QED

Theorem demands_Proj:
  e demands d ⇒
  (Proj n i e) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Proj]
QED

Theorem demands_Projs:
  e demands d ⇒
  (Projs ps2 e) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Projs]
QED

Theorem demands_Proj_Var:
  (Proj s i (Var v)) demands (([(s,i)],v), c)
Proof
  rw [demands_def,Projs_def]
  \\ metis_tac [Seq_id,exp_eq_sym, exp_eq_IMP_exp_eq_in_ctxt]
QED

Theorem demands_Seq:
  e demands d ⇒ (Seq e e') demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Seq]
QED

Theorem demands_Seq2:
  e' demands d ⇒ (Seq e e') demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_Var_is_demands, needs_Seq2]
QED

Theorem demands_Let1:
  e demands (d, c) ∧ e' demands (([],w), Bind w e c) ⇒ (Let w e e') demands (d, c)
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_def, needs_Var_is_demands, needs_Let1]
QED

Theorem demands_Let2:
  e' demands ((p,v), Bind w e c) ∧ v ≠ w ⇒ (Let w e e') demands ((p,v), c)
Proof
  rw [demands_def,Projs_def, exp_eq_in_ctxt_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ last_assum $ irule_at Any
  \\ irule exp_eq_in_ctxt_trans
  \\ qexists_tac ‘Seq (Let w e (Projs p (Var v))) (Let w e e')’
  \\ conj_tac THEN1 fs [exp_eq_IMP_exp_eq_in_ctxt, Let_Seq]
  \\ irule exp_eq_in_ctxt_Prim \\ fs [exp_eq_IMP_exp_eq_in_ctxt, exp_eq_refl,Let_Var]
  \\ qid_spec_tac ‘p’ \\ Induct
  THEN1 fs [exp_eq_IMP_exp_eq_in_ctxt, Projs_def,Let_Var2]
  \\ fs [FORALL_PROD,Projs_def] \\ rw []
  \\ fs [GSYM Projs_def]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ((p_1,p_2)::p') (Let w e (Var v))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var2]
QED

Theorem demands_Let3:
  ∀e v h ps c. e demands ((ps, v), Bind v (Var h) c) ⇒ (Let v (Var h) e) demands ((ps, h), c)
Proof
  rw [demands_def, exp_eq_in_ctxt_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ last_assum $ irule_at Any
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Projs
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var]
QED

Theorem demands_Let_Proj: (* expects program to be in ANF *)
  e demands ((ps,w), Bind w (Proj s i (Var v)) c) ⇒
  (Let w (Proj s i (Var v)) e) demands (((s,i)::ps,v), c)
Proof
  metis_tac [needs_Let_Proj, needs_Var_is_demands]
QED

Theorem demands_Let_Cons: (* expects program to be in ANF *)
  e demands (((s,LENGTH xs)::ps,w), Bind w (Cons s (xs ++ (Var v)::ys)) c) ⇒
  (Let w (Cons s (xs ++ (Var v)::ys)) e) demands ((ps,v), c)
Proof
  metis_tac [needs_Let_Cons, needs_Var_is_demands]
QED

Theorem demands_App:
  f demands d ⇒ (App f e) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_App, needs_Var_is_demands]
QED

Theorem demands_If:
  e demands d ⇒ (If e e' e'') demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_If, needs_Var_is_demands]
QED

Theorem demands_If2:
  et demands d ∧ ee demands d ⇒ (If ec et ee) demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_If2, needs_Var_is_demands]
QED

Definition well_formed_def:
  well_formed (Cons s) l = (s ≠ s) ∧
  well_formed (Proj s i) l = (∃ e. l = [e]) ∧
  well_formed (IsEq s i) l = (∃e. l = [e]) ∧
  well_formed If (l: exp list) = (∃e e' e''. l = e::e'::e''::[]) ∧
  well_formed Seq l = (∃e e'. l = e::e'::[]) ∧
  well_formed (AtomOp op) l = (op ≠ op)
End

Theorem demands_Prim:
  e demands d ∧ well_formed ope (e::l) ⇒ Prim ope (e::l) demands d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def]
  \\ qabbrev_tac ‘p = Projs d0 (Var d1)’
  \\ irule exp_eq_in_ctxt_trans \\ qexists_tac ‘Prim ope ((Seq p e)::l)’
  \\ conj_tac
  >- (irule exp_eq_in_ctxt_Prim
      \\ gvs [exp_eq_in_ctxt_refl, LIST_REL_EL_EQN])
  \\ Cases_on ‘ope’ \\ fs [well_formed_def]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ fs [If_Seq, IsEq_Seq, Proj_Seq2, Seq_assoc]
QED

Theorem demands_IsEq:
  e demands d ⇒ (IsEq n i e) demands d
Proof
  strip_tac
  \\ irule demands_Prim
  \\ fs [well_formed_def]
QED

Theorem needs_projs_reduce:
  ∀ps ps' e e' c. e needs ((ps ++ ps', e'), c) ⇒ e needs ((ps, e'), c)
Proof
  rw [needs_def, double_Projs]
  \\ qabbrev_tac ‘p = Projs ps e'’
  \\ irule exp_eq_in_ctxt_trans \\ qexists_tac ‘Seq (Seq p (Projs ps' p)) e’
  \\ conj_tac
  >- (irule exp_eq_in_ctxt_trans \\ first_assum $ irule_at Any
      \\ irule exp_eq_in_ctxt_Prim
      \\ fs [exp_eq_in_ctxt_refl]
      \\ ‘p needs (([], p), c)’ by fs [needs_refl]
      \\ drule needs_Projs
      \\ rw [needs_def, Projs_def])
  \\ irule exp_eq_in_ctxt_trans \\ qexists_tac ‘Seq p (Seq (Projs ps' p) e)’
  \\ fs [exp_eq_IMP_exp_eq_in_ctxt, Seq_assoc]
  \\ irule exp_eq_in_ctxt_Prim
  \\ fs [exp_eq_in_ctxt_refl, exp_eq_in_ctxt_sym]
QED

Theorem demands_Projs_empty:
  ∀ps v c. (Projs ps (Var v)) demands (([], v), c)
Proof
  rpt gen_tac
  \\ ‘(Projs ps (Var v)) demands ((ps, v), c)’
    by metis_tac [exp_eq_IMP_exp_eq_in_ctxt, Projs_def, demands_def, Seq_id, exp_eq_sym]
  \\ irule $ iffLR needs_Var_is_demands
  \\ irule needs_projs_reduce
  \\ fs []
  \\ rw [needs_Var_is_demands]
  \\ first_assum $ irule_at Any
QED

Theorem demands_empty_proj:
  e demands ((ps, v), c) ⇒ e demands (([], v), c)
Proof
  ‘ps = [] ++ ps’ by rw []
  \\ rw []
  \\ metis_tac [needs_projs_reduce, needs_Var_is_demands]
QED

Theorem demands_projs_reduce:
  e demands ((ps ++ ps', v), c) ⇒ e demands ((ps, v), c)
Proof
  metis_tac [needs_projs_reduce, needs_Var_is_demands]
QED

Theorem EXISTS_EL:
  ∀l P. EXISTS P l ⇒ ∃n. n < LENGTH l ∧ P (EL n l)
Proof
  Induct
  \\ fs [EXISTS_DEF]
  \\ rw []
  >- (qexists_tac ‘0’
      \\ fs [])
  \\ first_x_assum $ dxrule
  \\ rw []
  \\ rename1 ‘n < LENGTH l’
  \\ qexists_tac ‘SUC n’
  \\ fs []
QED

Theorem demands_AtomOp:
  ∀d l op. EXISTS (λe. e demands d) l ⇒ Prim (AtomOp op) l demands d
Proof
  gen_tac
  \\ PairCases_on ‘d’
  \\ rw [eval_wh_def, eval_wh_to_def, demands_def]
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at Any exp_eq_in_ctxt_Prim
  \\ drule EXISTS_EL
  \\ rw []
  \\ rename1 ‘exp_eq_in_ctxt c (EL n l) (Seq p _)’
  \\ qexists_tac ‘LUPDATE (Seq p (EL n l)) n l’
  \\ rw [LIST_REL_EL_EQN, EL_LUPDATE]
  >- (IF_CASES_TAC
      \\ fs [exp_eq_in_ctxt_refl])
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule no_err_eval_wh_IMP_exp_eq
  \\ rw [no_err_eval_wh_def, subst_def, eval_wh_Prim_alt, MAP_MAP_o]
  \\ qabbrev_tac ‘l2 = LUPDATE (Seq p (EL n l)) n l’
  >- (qsuff_tac ‘EXISTS error_Atom (MAP (eval_wh o (λa. subst f a)) l2)’
      >- rw [get_atoms_def]
      \\ fs [EXISTS_MEM]
      \\ qexists_tac ‘eval_wh (subst f (EL n l2))’
      \\ unabbrev_all_tac
      \\ rw [LUPDATE_MAP, MEM_LUPDATE, EL_LUPDATE]
      \\ fs [subst_def, eval_wh_Seq])
  >- (Cases_on ‘EXISTS error_Atom (MAP (eval_wh o (λa. subst f a)) l2)’
      >- rw [get_atoms_def]
      \\ qsuff_tac ‘MEM wh_Diverge (MAP (eval_wh ∘ (λa. subst f a)) l2)’
      >- rw [get_atoms_def]
      \\ unabbrev_all_tac
      \\ rw [LUPDATE_MAP, MEM_LUPDATE, subst_def, eval_wh_Seq])
  \\ unabbrev_all_tac
  \\ rw [MAP_GENLIST, Once get_atoms_def]
  >- (fs [EXISTS_MAP]
      \\ drule EXISTS_EL
      \\ rw [EL_LUPDATE]
      \\ rename1 ‘n2 = n’
      \\ Cases_on ‘n2 = n’
      \\ rw []
      \\ fs [subst_def, eval_wh_Seq]
      >- (gvs []
          \\ ‘EXISTS (λx. error_Atom (eval_wh (subst f x))) l’
            by (fs [EXISTS_MEM]
                \\ first_x_assum $ irule_at Any
                \\ fs [EL_MEM])
          \\ rw [get_atoms_def, EXISTS_MAP])
      \\ ‘EXISTS (λx. error_Atom (eval_wh (subst f x))) l’
        by (fs [EXISTS_MEM]
            \\ first_x_assum $ irule_at Any
            \\ fs [EL_MEM])
      \\ rw [get_atoms_def, EXISTS_MAP])
  \\ fs []
  \\ ‘¬ EXISTS error_Atom (MAP (eval_wh o (λa. subst f a)) l)’
    by (rw []
        \\ fs [EVERY_MEM]
        \\ rw []
        \\ fs [MEM_EL]
        \\ rename1 ‘¬error_Atom (EL n2 _)’
        \\ Cases_on ‘n2 = n’
        \\ rw []
        >- (first_x_assum $ qspecl_then [‘eval_wh (subst f (Seq p (EL n l)))’] assume_tac
            \\ fs [eval_wh_Seq, subst_def]
            \\ ‘(if eval_wh (subst f p) = wh_Error then wh_Error
                 else if eval_wh (subst f p) = wh_Diverge then wh_Diverge
                 else eval_wh (subst f (EL n l))) = eval_wh (subst f (EL n l))’ by fs []
            \\ fs [EL_MAP]
            \\ pop_assum kall_tac
            \\ pop_assum irule
            \\ first_assum $ irule_at Any
            \\ rw [EL_MAP, EL_LUPDATE, subst_def, eval_wh_Seq])
        \\ first_x_assum irule
        \\ first_assum $ irule_at Any
        \\ fs [EL_MAP, EL_LUPDATE])
  >- (‘MEM wh_Diverge (MAP (eval_wh o (λa. subst f a)) l)’
        by (fs [MEM_EL]
            \\ first_assum $ irule_at Any
            \\ pop_assum kall_tac
            \\ rename1 ‘EL n2 _’
            \\ Cases_on ‘n2 = n’
            >- (fs [EL_MAP, EL_LUPDATE, LUPDATE_MAP, eval_wh_Seq, subst_def]
                \\ metis_tac [])
            \\ gvs [LENGTH_LUPDATE, EL_MAP, EL_LUPDATE, eval_wh_Seq, subst_def])
      \\ rw [get_atoms_def])
  >- (qsuff_tac ‘MAP (eval_wh o (λa. subst f a)) (LUPDATE (Seq p (EL n l)) n l) = MAP (eval_wh o (λa. subst f a)) l’
      >- (rw [get_atoms_def]
          \\ fs [])
      \\ pop_assum kall_tac
      \\ pop_assum kall_tac
      \\ pop_assum kall_tac
      \\ irule LIST_EQ
      \\ rw [LENGTH_MAP, LENGTH_LUPDATE, EL_MAP, EL_LUPDATE, eval_wh_Seq, subst_def])
QED

Theorem Apps_demands:
  ∀el d e. e demands d ⇒ Apps e el demands d
Proof
  Induct
  \\ fs [Apps_def]
  \\ gen_tac
  \\ rw []
  \\ first_x_assum irule
  \\ fs [demands_App]
QED

Theorem exp_eq_same_demands:
  ∀d c e e'. exp_eq_in_ctxt c e e' ⇒ e demands (d, c) ⇒ e' demands (d, c)
Proof
  PairCases
  \\ metis_tac [needs_exp_eq, needs_Var_is_demands]
QED

Theorem last_Lams:
  ∀l x e. Lams (l ++ [x]) e = Lams l (Lam x e)
Proof
  Induct
  \\ fs [Lams_def]
QED

val _ = set_fixity "fdemands" (Infixl 480);

Definition fdemands_def:
  f fdemands ((ps, i), len, Nil) = (i < len ∧ (∀l. LENGTH l = len ⇒ Apps f l needs ((ps, EL i l), Nil))) ∧
  f fdemands (p, len, Bind v e c) = (Let v e f) fdemands (p, len, c) ∧
  f fdemands (p, len, RecBind b c) = (Letrec b f) fdemands (p, len, c) ∧
  f fdemands (p, len, IsFree v c) = ∀e. closed e ⇒ (Let v e f) fdemands (p, len, c)
End

Theorem fdemands_alt:
  ∀(c : ctxt) f ps i len. f fdemands ((ps, i), len, c) ⇒ i < len ∧ ∀l. LENGTH l = len ⇒ (Apps f l) needs ((ps, EL i l), c)
Proof
  Induct >> gvs [fdemands_def] >> rpt gen_tac >> strip_tac
  >~[‘IsFree’]
  >- (rw [needs_def, exp_eq_in_ctxt_def]
      >- (pop_assum $ qspecl_then [‘Fail’] assume_tac >>
          gvs [closed_def] >>
          last_x_assum $ dxrule_then assume_tac >> fs []) >>
      first_x_assum $ dxrule_then assume_tac >>
      gvs [needs_def] >>
      irule exp_eq_in_ctxt_trans >> irule_at Any Let_Apps_in_ctxt >>
      irule exp_eq_in_ctxt_trans >> last_x_assum $ dxrule_then assume_tac >>
      fs [] >> first_x_assum $ irule_at Any >> fs [EL_MAP] >>
      irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >>
      irule exp_eq_trans >> irule_at Any Let_Seq >>
      gvs [Let_Projs, exp_eq_Prim_cong, Let_Apps])
  >~[‘Bind’]
  >- (last_x_assum $ dxrule_then assume_tac >> fs [needs_def, exp_eq_in_ctxt_def] >> rw [] >>
      irule exp_eq_in_ctxt_trans >> irule_at Any Let_Apps_in_ctxt >>
      irule_at Any exp_eq_in_ctxt_trans >> first_x_assum $ irule_at Any >> fs [EL_MAP] >>
      irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >>
      irule exp_eq_trans >> irule_at Any Let_Seq >>
      gvs [Let_Projs, exp_eq_Prim_cong, Let_Apps]) >>
  last_x_assum $ dxrule_then assume_tac >> fs [needs_def, exp_eq_in_ctxt_def] >> rw [] >>
  irule exp_eq_in_ctxt_trans >> irule_at Any Letrec_Apps_in_ctxt >>
  irule_at Any exp_eq_in_ctxt_trans >> first_x_assum $ irule_at Any >> fs [EL_MAP] >>
  irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >>
  irule exp_eq_trans >> irule_at Any Letrec_Prim >>
  gvs [Letrec_Projs, exp_eq_Prim_cong, Letrec_Apps]
QED

val _ = set_fixity "demands_when_applied" (Infixl 480);

Definition demands_when_applied_def:
  f demands_when_applied ((ps, v), len, c) = eq_when_applied c f (Seq (Projs ps (Var v)) f) len
End

val _ = set_fixity "needs_when_applied" (Infixl 480);

Definition needs_when_applied_def:
  f needs_when_applied ((ps, e), len, c) = eq_when_applied c f (Seq (Projs ps e) f) len
End

Theorem needs_when_applied_0:
  ∀p f c. f needs_when_applied (p, 0, c) = f needs (p, c)
Proof
  PairCases >> gvs [needs_when_applied_def, needs_def, eq_when_applied_0]
QED

Theorem demands_when_applied_0:
  ∀p f c. f demands_when_applied (p, 0, c) = f demands (p, c)
Proof
  PairCases >> gvs [demands_when_applied_def, demands_def, eq_when_applied_0]
QED

Theorem eq_when_applied_trans:
  ∀c e1 e2 e3 len.
    eq_when_applied c e1 e2 len ∧ eq_when_applied c e2 e3 len
    ⇒ eq_when_applied c e1 e3 len
Proof
  Induct >> rw [eq_when_applied_def]
  >- (irule exp_eq_trans >>
      rpt $ first_x_assum $ irule_at Any >> fs []) >>
  rpt $ last_x_assum $ irule_at Any
QED
        
Theorem eq_when_applied_trans_exp_eq:
  ∀c e1 e2 e3 len.
    exp_eq_in_ctxt c e1 e2 ∧ eq_when_applied c e2 e3 len
    ⇒ eq_when_applied c e1 e3 len
Proof
  rw [] >> irule eq_when_applied_trans >>
  first_x_assum $ irule_at Any >>
  gvs [exp_eq_in_ctxt_IMP_eq_when_applied]
QED

Theorem needs_when_applied_App:
  ∀c p f len e. f needs_when_applied (p, SUC len, c)
                ⇒ (App f e) needs_when_applied (p, len, c)
Proof
  fs [FORALL_PROD] >> Induct >>
  gvs [needs_when_applied_def, eq_when_applied_def, GSYM Apps_def] >> rw []
  >- (irule exp_eq_trans >> pop_assum $ irule_at Any >>
      gvs [Apps_def] >> irule exp_eq_Apps_cong >> fs [exp_eq_l_refl, Seq_App])
  >- (irule eq_when_applied_trans_exp_eq >> irule_at Any Let_App_in_ctxt >>
      irule eq_when_applied_trans >> last_x_assum $ irule_at Any >>
      irule_at (Pos hd) eq_when_applied_trans >> first_x_assum $ irule_at Any >>
      rpt $ irule_at Any exp_eq_in_ctxt_IMP_eq_when_applied >>
      rpt $ irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at (Pos hd) exp_eq_trans >> irule_at Any Let_Seq >>
      irule_at Any exp_eq_Prim_cong >> gvs [exp_eq_refl] >>
      irule_at Any Let_Projs >> irule $ iffLR exp_eq_sym >>
      irule exp_eq_trans >> irule_at Any Let_Seq >>
      gvs [exp_eq_Prim_cong, Let_Projs, Let_App])
  >- (irule eq_when_applied_trans_exp_eq >> irule_at Any Let_App_in_ctxt >>
      irule eq_when_applied_trans >> last_x_assum $ irule_at Any >>
      irule_at (Pos hd) eq_when_applied_trans >> first_x_assum $ irule_at Any >>
      rpt $ irule_at Any exp_eq_in_ctxt_IMP_eq_when_applied >>
      rpt $ irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at (Pos hd) exp_eq_trans >> irule_at Any Let_Seq >>
      irule_at Any exp_eq_Prim_cong >> gvs [exp_eq_refl] >>
      irule_at Any Let_Projs >> irule $ iffLR exp_eq_sym >>
      irule exp_eq_trans >> irule_at Any Let_Seq >>
      gvs [exp_eq_Prim_cong, Let_Projs, Let_App]) >>
  irule eq_when_applied_trans_exp_eq >>
  irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any Letrec_App >>
  irule eq_when_applied_trans >> last_x_assum $ irule_at Any >>
  irule_at (Pos hd) eq_when_applied_trans >> first_x_assum $ irule_at Any >>
  rpt $ irule_at Any exp_eq_in_ctxt_IMP_eq_when_applied >>
  rpt $ irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at (Pos hd) exp_eq_trans >> irule_at Any Letrec_Prim >>
  irule_at Any exp_eq_Prim_cong >> gvs [exp_eq_refl] >>
  irule_at Any Letrec_Projs >> irule $ iffLR exp_eq_sym >>
  irule exp_eq_trans >> irule_at Any Letrec_Prim >>
  gvs [exp_eq_Prim_cong, Letrec_Projs, Letrec_App]
QED

Theorem fdemands_0_App_needs:
  ∀c f e d len. e needs (d, c) ∧ f fdemands (([], 0), SUC len, c)
                ⇒ App f e needs_when_applied (d, len, c)
Proof
  Induct >>
  gvs[FORALL_PROD, needs_when_applied_def, fdemands_def,
      eq_when_applied_def, exp_eq_in_ctxt_def, Projs_def] >>
  rw [GSYM Apps_def]
  >- (irule exp_eq_trans >>
      irule_at (Pos last) $ iffLR exp_eq_sym >> irule_at Any Apps_Seq >>
      rename1 ‘Apps f(e::l)’ >> pop_assum $ qspecl_then [‘e::l’] assume_tac >> fs [] >>
      dxrule_then (dxrule_then assume_tac) needs_trans >>
      gvs [needs_def, exp_eq_in_ctxt_def, Apps_def])
  >~[‘Letrec’]
  >- (irule eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any Letrec_App >>
      irule_at Any eq_when_applied_trans >> last_x_assum $ irule_at Any >>
      gvs [needs_def, exp_eq_in_ctxt_def] >>
      irule_at Any exp_eq_in_ctxt_trans >> first_x_assum $ irule_at Any >>
      irule_at Any exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any exp_eq_trans >>
      irule_at Any Letrec_Prim >> irule_at Any exp_eq_Prim_cong >>
      gvs [exp_eq_refl] >> irule_at Any Letrec_Projs >>
      irule exp_eq_in_ctxt_IMP_eq_when_applied >> irule exp_eq_IMP_exp_eq_in_ctxt >>
      irule $ iffLR exp_eq_sym >> irule exp_eq_trans >>
      irule_at Any Letrec_Prim >> irule_at Any exp_eq_Prim_cong >>
      gvs [Letrec_App, Letrec_Projs]) >>
  irule eq_when_applied_trans_exp_eq >> irule_at Any Let_App_in_ctxt >>
  irule eq_when_applied_trans >> last_x_assum $ irule_at Any
  >- (gvs [needs_def] >>
      irule_at Any exp_eq_in_ctxt_trans >> irule_at Any exp_eq_in_ctxt_App >>
      irule_at Any exp_eq_in_ctxt_Lam >> last_x_assum $ irule_at Any >>
      irule_at Any exp_eq_in_ctxt_refl >>
      irule_at Any exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any exp_eq_trans >>
      irule_at Any Let_Seq >> irule_at Any exp_eq_Prim_cong >>
      gvs [exp_eq_refl] >> irule_at Any Let_Projs >>
      irule exp_eq_in_ctxt_IMP_eq_when_applied >> irule exp_eq_IMP_exp_eq_in_ctxt >>
      irule $ iffLR exp_eq_sym >> irule exp_eq_trans >>
      irule_at Any Let_Seq >> irule_at Any exp_eq_Prim_cong >>
      gvs [Let_App, Let_Projs])
  >- (gvs [needs_def, exp_eq_in_ctxt_def] >>
      irule_at Any exp_eq_in_ctxt_trans >> last_x_assum $ irule_at Any >> fs [] >>
      irule_at Any exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any exp_eq_trans >>
      irule_at Any Let_Seq >> irule_at Any exp_eq_Prim_cong >>
      gvs [exp_eq_refl] >> irule_at Any Let_Projs >>
      irule exp_eq_in_ctxt_IMP_eq_when_applied >> irule exp_eq_IMP_exp_eq_in_ctxt >>
      irule $ iffLR exp_eq_sym >> irule exp_eq_trans >>
      irule_at Any Let_Seq >> irule_at Any exp_eq_Prim_cong >>
      gvs [Let_App, Let_Projs])
QED

Theorem demands_w_app_is_needs_w_app:
  ∀f c ps v e len. f demands_when_applied ((ps, v), len, c) = f needs_when_applied ((ps, Var v), len, c)
Proof
  rw [demands_when_applied_def, needs_when_applied_def]
QED

Theorem demands_when_applied_App:
  ∀c p f len e. f demands_when_applied (p, SUC len, c)
                ⇒ (App f e) demands_when_applied (p, len, c)
Proof
  gvs [FORALL_PROD, needs_when_applied_App, demands_w_app_is_needs_w_app]
QED

Theorem demands_when_applied_Lam:
  ∀c p f len e v. f demands_when_applied (p, len, IsFree v c) ∧ v ≠ SND p
                ⇒ (Lam v f) demands_when_applied (p, SUC len, c)
Proof
  gvs [FORALL_PROD, demands_when_applied_def]
QED

Theorem needs_when_applied_Seq:
  ∀c p f len e. f needs_when_applied (p, len, c)
                ⇒ (Seq e f) needs_when_applied (p, len, c)
Proof
  Induct >> gvs [FORALL_PROD, needs_when_applied_def, eq_when_applied_def] >> rw []
  >- (irule exp_eq_trans >> irule_at Any Apps_Seq >>
      irule exp_eq_trans >> irule_at Any exp_eq_Apps_cong >>
      irule_at Any exp_eq_l_refl >>
      irule_at (Pos hd) exp_eq_trans >> irule_at (Pos $ el 2) Seq_assoc >>
      irule_at (Pos hd) exp_eq_trans >> irule_at (Pos $ el 2) Seq_comm >>
      irule_at (Pos hd) $ iffLR exp_eq_sym >> irule_at Any Seq_assoc >>
      irule exp_eq_trans >> irule_at (Pos last) $ iffLR exp_eq_sym >>
      irule_at Any Apps_Seq >> irule exp_eq_Prim_cong >>
      gvs [exp_eq_refl])
  >~[‘Letrec’]
  >- (irule eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any Letrec_Prim >> fs [] >>
      irule eq_when_applied_trans >> last_x_assum $ irule_at Any >>
      irule_at (Pos hd) eq_when_applied_trans >> first_x_assum $ irule_at Any >>
      rpt $ irule_at Any exp_eq_in_ctxt_IMP_eq_when_applied >>
      rpt $ irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at (Pos hd) exp_eq_trans >> irule_at Any Letrec_Prim >> 
      irule_at Any exp_eq_Prim_cong >> gvs [exp_eq_refl] >>
      irule_at Any Letrec_Projs >> irule $ iffLR exp_eq_sym >>
      irule_at Any exp_eq_trans >> irule_at Any Letrec_Prim >> irule exp_eq_Prim_cong >>
      gvs [Letrec_Projs] >>
      irule exp_eq_trans >> irule_at Any Letrec_Prim >> gvs [exp_eq_refl]) >>
  irule eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any Let_Seq >>
  irule eq_when_applied_trans >> last_x_assum $ irule_at Any >>
  irule_at (Pos hd) eq_when_applied_trans >> first_x_assum $ irule_at Any >>
  rpt $ irule_at Any exp_eq_in_ctxt_IMP_eq_when_applied >>
  rpt $ irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at (Pos hd) exp_eq_trans >> irule_at Any Let_Seq >> 
  irule_at Any exp_eq_Prim_cong >> gvs [exp_eq_refl] >>
  irule_at Any Let_Projs >> irule $ iffLR exp_eq_sym >>
  irule_at Any exp_eq_trans >> irule_at Any Let_Seq >> irule exp_eq_Prim_cong >>
  gvs [Let_Projs, Let_Seq]
QED

Theorem demands_when_applied_Seq:
  ∀p c  f len e. f demands_when_applied (p, len, c)
                ⇒ (Seq e f) demands_when_applied (p, len, c)
Proof
  gvs [FORALL_PROD, demands_w_app_is_needs_w_app, needs_when_applied_Seq]
QED

Theorem fdemands_0_App_demands:
  ∀c f e d len. e demands (d, c) ∧ f fdemands (([], 0), SUC len, c)
                ⇒ App f e demands_when_applied (d, len, c)
Proof
  gvs [FORALL_PROD, fdemands_0_App_needs, demands_w_app_is_needs_w_app, needs_Var_is_demands]
QED

Theorem demands_when_applied:
  ∀c v e e' d len. e demands_when_applied (d, len, IsFree v c) ∧ SND d ≠ v
                   ⇒ Let v e' e demands_when_applied (d, len, c)
Proof
 Induct >> gvs [FORALL_PROD] >>
 rw []
 >- (irule demands_when_applied_App


    )

QED

val _ = set_fixity "fdemands_depth" (Infixl 480);

Definition fdemands_depth_def:
  fexp fdemands_depth ((ps, i), len, k, c)
  = (i < len
     ∧ ∃s. FINITE s
           ∧ ∀l. (set l ∩ s = {} ∧ LENGTH l = len)
                 ⇒ ∀f. freevars (Apps fexp (MAP Var l)) ⊆ FDOM f
                       ∧ is_bot (eval_wh_to k (subst f (Var (EL i l))))
             ⇒  is_bot (eval_wh_to k (subst f (Apps fexp (MAP Var l)))))
End

Theorem exists_str_not_in_list:
  ∀l. ∃(s : string). ¬ MEM s l
Proof
  qsuff_tac `INFINITE 𝕌(:string)`
  >- rw[pred_setTheory.NOT_IN_FINITE]
  >- simp[]
QED

Theorem exists_l_not_in_s:
  ∀(s : string -> bool) k. FINITE s ⇒ ∃l. ALL_DISTINCT l ∧ EVERY (λx. x ∉ s) l ∧ LENGTH l = k
Proof
  gen_tac
  \\ Induct
  \\ rw []
  \\ first_x_assum drule
  \\ rw []
  \\ ‘INFINITE 𝕌(:string)’ by simp []
  \\ ‘∃hd. hd ∉ s ∪ set l’ by
    fs [NOT_IN_FINITE, FINITE_UNION, FINITE_LIST_TO_SET]
  \\ qexists_tac ‘hd::l’
  \\ gvs []
QED

Theorem DRESTRICT_DOMSUB_COMM:
  ∀f v s. DRESTRICT (f \\ v) s = (DRESTRICT f s) \\ v
Proof
  fs [EQ_FDOM_SUBMAP]
  \\ rw [DRESTRICT_DEF, DELETE_INTER, SUBMAP_DEF, DOMSUB_FAPPLY_THM]
QED

(*
Theorem subst_does_not_change:
  ∀e v f. v ∉ freevars e ⇒ subst f e = subst (f \\ v) e
Proof
  Induct using freevars_ind
  \\ rw [subst_def, freevars_def, DOMSUB_FLOOKUP_NEQ, MAP_EQ_f, FDIFF_def]
  \\ gvs [DOMSUB_COMMUTES]
  >- (first_x_assum $ irule
      \\ fs []
      \\ first_x_assum $ qspecl_then [‘freevars a’] assume_tac
      \\ fs [MEM_EL]
      \\ pop_assum $ qspecl_then [‘n’] assume_tac
      \\ gvs [EL_MAP])
  >>~[‘subst (DRESTRICT _ _) _ = subst _ _’]
  >- gvs [DRESTRICT_DOMSUB_COMM]
  >- (rename1 ‘DRESTRICT f (COMPL (set l))’
      \\ AP_THM_TAC
      \\ AP_TERM_TAC
      \\ gvs [DRESTRICT_EQ_DRESTRICT]
      \\ irule_at Any DOMSUB_SUBMAP
      \\ fs [FDOM_DRESTRICT]
      \\ irule_at Any SUBMAP_TRANS
      \\ irule_at Any DRESTRICT_SUBMAP
      \\ fs [DOMSUB_SUBMAP]
      \\ qspecl_then [‘FDOM f’, ‘COMPL (set l)’, ‘v’] assume_tac DELETE_INTER
      \\ fs [Once INTER_COMM]
      \\ fs [GSYM DELETE_NON_ELEMENT])
  \\ rename1 ‘_ e' = _ e'’
  \\ PairCases_on ‘e'’
  \\ fs []
  >- (last_x_assum drule
      \\ gvs [DRESTRICT_DOMSUB_COMM]
      \\ rw []
      \\ pop_assum irule
      \\ rename1 ‘MEM (v2, e2) lcs’
      \\ first_x_assum $ qspecl_then [‘freevars e2’] assume_tac
      \\ fs [MEM_MAP]
      \\ pop_assum $ qspecl_then [‘(v2, e2)’] assume_tac
      \\ fs [])
  >- (rename1 ‘DRESTRICT f (COMPL (set l))’
      \\ AP_THM_TAC
      \\ AP_TERM_TAC
      \\ gvs [DRESTRICT_EQ_DRESTRICT]
      \\ irule_at Any DOMSUB_SUBMAP
      \\ fs [FDOM_DRESTRICT]
      \\ irule_at Any SUBMAP_TRANS
      \\ irule_at Any DRESTRICT_SUBMAP
      \\ fs [DOMSUB_SUBMAP]
      \\ qspecl_then [‘FDOM f’, ‘COMPL (set l)’, ‘v’] assume_tac DELETE_INTER
      \\ fs [Once INTER_COMM]
      \\ fs [GSYM DELETE_NON_ELEMENT])
QED*)

Theorem closed_subst2:
  ∀v f e e'. (∀v. v ∈ FRANGE f ⇒ closed v) ⇒ closed e ⇒ freevars e' ⊆ FDOM f ⇒ (closed (subst f e') ∧ closed (subst1 v e (subst (f \\ v) e')))
Proof
  rw []
  \\ rw [closed_def]
  \\ ‘∀v2. v2 ∈ FRANGE (f \\ v) ⇒ closed v2’
    by (rw []
        \\ first_x_assum irule
        \\ metis_tac [FRANGE_DOMSUB_SUBSET, SUBSET_DEF])
  \\ dxrule freevars_subst
  \\ dxrule freevars_subst
  \\ dxrule freevars_subst1
  \\ rw []
  \\ gvs [SUBSET_DIFF_EMPTY, DELETE_DEF, SUBSET_DEF]
  \\ rw []
  \\ gvs []
QED

Theorem App_Let:
  ∀v e e' e'' b. v ∉ freevars e'' ⇒ (App (Let v e e') e'' ≅? Let v e (App e' e'')) b
Proof
  rw []
  \\ irule eval_wh_IMP_exp_eq
  \\ rw []
  \\ gvs [subst_def, eval_wh_thm]
  \\ ‘∀v. v ∈ FRANGE f ⇒ closed v’ by gvs [FRANGE_FLOOKUP]
  \\ ‘closed (subst f e)’ by gvs [closed_def, freevars_subst, SUBSET_DIFF_EMPTY]
  \\ fs [bind1_def, subst1_def, eval_wh_App]
  \\ IF_CASES_TAC
  \\ fs []
  \\ rename1 ‘(subst1 v (subst f e) (subst (f \\ v) e'))’
  \\ Cases_on ‘dest_wh_Closure (eval_wh (subst1 v (subst f e) (subst (f \\ v) e')))’
  \\ fs []
  \\ rename1 ‘SOME x’
  \\ PairCases_on ‘x’
  \\ fs []
  \\ qspecl_then [‘v’, ‘f’, ‘subst f e’, ‘e''’] assume_tac closed_subst2
  \\ gvs []
  \\ AP_TERM_TAC
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ fs []
  \\ simp [GSYM subst_fdomsub]
QED

Theorem Apps_Let:
  ∀l v e e' b. EVERY (λe. v ∉ freevars e) l ⇒ (Apps (Let v e e') l ≅? Let v e (Apps e' l)) b
Proof
  Induct
  \\ fs [Apps_def, exp_eq_refl]
  \\ rw []
  \\ first_x_assum dxrule
  \\ rw []
  \\ dxrule App_Let
  \\ strip_tac
  \\ irule exp_eq_trans
  \\ first_x_assum $ irule_at Any
  \\ irule exp_eq_Apps_cong
  \\ fs [exp_eq_l_refl]
QED

Theorem Apps_Lams_fold:
  ∀l eL e b. EVERY (λx. EVERY (λe. x ∉ freevars e) eL) l ∧ LENGTH l = LENGTH eL ⇒
             (Apps (Lams l e) eL ≅?  FOLDR (λ (id, e') e. Let id e' e) e (ZIP (l, eL))) b
Proof
  Induct
  \\ fs [Lams_def, Apps_def, exp_eq_refl]
  \\ gen_tac
  \\ Cases
  \\ fs [Apps_def, ZIP_def]
  \\ rw []
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_App_cong
  \\ irule_at Any exp_eq_Lam_cong
  \\ first_x_assum $ irule_at Any
  \\ fs []
  \\ irule_at Any Apps_Let
  \\ gvs [exp_eq_refl, EVERY_CONJ]
QED

Theorem LetsSeq_com:
  ∀l e e' b. (FOLDR (λ (id, e') e. Let id e' e) (Seq e e') l ≅?
                 Seq (FOLDR (λ (id, e') e. Let id e' e) e l) (FOLDR (λ (id, e') e. Let id e' e) e' l)) b
Proof
  Induct
  \\ fs [exp_eq_refl]
  \\ Cases
  \\ rw []
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_App_cong
  \\ irule_at Any exp_eq_Lam_cong
  \\ pop_assum $ irule_at Any
  \\ irule_at Any exp_eq_refl
  \\ fs [Let_Seq]
QED

Theorem Apps_Lams_Seq_strong:
  ∀l eL e p b. EVERY (λx. EVERY (λe. x ∉ freevars e) eL) l ∧ LENGTH l = LENGTH eL ⇒
                     (Apps (Lams l (Seq p e)) eL ≅? Seq (Apps (Lams l p) eL) (Apps (Lams l e) eL)) b
Proof
  rw []
  \\ irule exp_eq_trans
  \\ irule_at Any Apps_Lams_fold
  \\ fs []
  \\ irule exp_eq_trans
  \\ irule_at Any LetsSeq_com
  \\ irule_at Any exp_eq_Prim_cong
  \\ gvs [Apps_Lams_fold, exp_eq_sym]
QED

Theorem FoldLets_Projs:
  ∀l ps e. FOLDR (λ(id, e1) e2. Let id e1 e2) (Projs ps e) l ≈ Projs ps (FOLDR (λ(id, e1) e2. Let id e1 e2) e l)
Proof
  Induct
  \\ fs [exp_eq_refl]
  \\ PairCases
  \\ rw []
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Projs
  \\ irule exp_eq_App_cong
  \\ gvs [exp_eq_refl, exp_eq_Lam_cong]
QED

Theorem ALL_DISTINCT_FLOOKUP:
  ∀l k v. ALL_DISTINCT (MAP FST l) ∧ MEM (k, v) l ⇒ ∀f. FLOOKUP (f |++ l) k = SOME v
Proof
  Induct
  \\ fs []
  \\ PairCases
  \\ rw []
  \\ gvs [FUPDATE_FUPDATE_LIST_COMMUTES, FUPDATE_LIST_THM, FLOOKUP_UPDATE]
  \\ IF_CASES_TAC
  >- (gvs [MEM_EL]
      \\ first_x_assum $ qspecl_then [‘n’] assume_tac
      \\ qabbrev_tac ‘p = EL n l’
      \\ PairCases_on ‘p’
      \\ gvs [EL_MAP])
  \\ first_x_assum irule
  \\ fs []
QED

Theorem eta_red_fold:
  ∀l f. ALL_DISTINCT (MAP FST l) ∧ EVERY (λv. v ∉ freevars f ∧ EVERY (λe. v ∉ freevars e) (MAP SND l)) (MAP FST l)
        ⇒ FOLDR (λ (id, e1) e2. Let id e1 e2) (Apps f (MAP (Var o FST) l)) l ≈ Apps f (MAP SND l)
Proof
  Induct
  \\ fs [exp_eq_refl]
  \\ PairCases
  \\ rw [Apps_def]
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_App_cong
  \\ irule_at Any exp_eq_Lam_cong
  \\ first_x_assum $ irule_at Any
  \\ gvs [EVERY_CONJ, EVERY_MEM]
  \\ irule_at Any exp_eq_refl
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_Apps, subst_def, eval_wh_thm]
  \\ rename1 ‘bind1 _ (subst f2 h1) _’
  \\ ‘∀v. v ∈ FRANGE f2 ⇒ closed v’
    by (rw [] \\ first_x_assum irule
        \\ gvs [FRANGE_FLOOKUP]
        \\ pop_assum $ irule_at Any)
  \\ ‘closed (subst f2 h1)’
    by (irule IMP_closed_subst
        \\ fs [])
  \\ qpat_x_assum ‘h0 ∉ freevars f’ assume_tac
  \\ drule $ GSYM subst_fdomsub
  \\ strip_tac
  \\ gvs [bind1_def, subst_Apps, Once subst_subst1_UPDATE, subst_def, FLOOKUP_UPDATE, MAP_MAP_o]
  \\ AP_TERM_TAC
  \\ ‘subst1 h0 (subst f2 h1) (subst f2 f) = subst f2 f’
    by (irule subst1_ignore
        \\ gvs [freevars_subst])
  \\ rw []
  \\ AP_TERM_TAC
  \\ irule LIST_EQ
  \\ rw [EL_MAP]
  \\ rename1 ‘EL n l’
  \\ ‘h0 ∉ freevars (SND (EL n l))’ by
    (last_x_assum irule
     \\ gvs [MEM_EL]
     \\ first_assum $ irule_at Any
     \\ fs [EL_MAP])
  \\ dxrule $ GSYM subst_fdomsub
  \\ rw []
  \\ irule subst1_ignore
  \\ gvs [freevars_subst]
  \\ DISJ1_TAC
  \\ last_x_assum $ irule_at Any
  \\ gvs [MEM_EL]
  \\ first_assum $ irule_at Any
  \\ fs [EL_MAP]
QED

Theorem fdemands_exp_eq:
  ∀c p f f' len. exp_eq_in_ctxt c f f' ∧ f fdemands (p, len, c) ⇒ f' fdemands (p, len, c)
Proof
  Induct
  >- (PairCases >> rw [fdemands_def] >>
      irule needs_exp_eq >> pop_assum $ irule_at Any >>
      gvs [exp_eq_in_ctxt_Apps, exp_eq_in_ctxt_l_refl])
  >~[‘IsFree’]
  >- (rw [fdemands_def] >> last_x_assum irule >>
      first_x_assum $ irule_at Any >> irule_at Any exp_eq_in_ctxt_App >>
      irule_at Any exp_eq_in_ctxt_refl >> irule_at Any exp_eq_in_ctxt_Lam >>
      fs []) >>
  rw [fdemands_def, exp_eq_in_ctxt_def] >> last_x_assum irule >>
  rpt $ pop_assum $ irule_at Any
QED

Theorem fdemands_Seq:
  ∀c p len e1 e2. e2 fdemands (p, len, c) ⇒ (Seq e1 e2) fdemands (p, len, c)
Proof
  Induct
  >- (PairCases >> rw [fdemands_def] >>
      irule needs_exp_eq >> irule_at Any needs_Seq2 >> pop_assum $ irule_at Any >>
      gvs [exp_eq_in_ctxt_def, Once exp_eq_sym] >> irule_at Any Apps_Seq) >>
  rw [fdemands_def] >>
  irule fdemands_exp_eq >> last_x_assum $ irule_at Any >>
  first_x_assum $ irule_at Any >>
  once_rewrite_tac [exp_eq_in_ctxt_sym]
  >~[‘Letrec’]
  >- (irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any exp_eq_trans >> irule_at Any Letrec_Prim >>
      gvs [] >> rpt $ irule_at Any exp_eq_refl) >>
  irule_at Any exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any Let_Seq >> fs []
QED

(*Theorem fdemands_every_thing:
  f fdemands ((ps, i), k, c) ⇔ (i < k ∧ ∀el. LENGTH el = k ⇒ (Apps f el) needs ((ps, EL i el), c))
Proof
  eq_tac
  \\ rw [fdemands_def]
  >- (rename1 ‘EL i eL’
      \\ qspecl_then [‘freevars f ∪ s ∪ BIGUNION (set (MAP freevars eL))’, ‘LENGTH eL’] assume_tac exists_l_not_in_s
      \\ ‘∀s. MEM s (MAP freevars eL) ⇒ FINITE s’ by (rw [MEM_EL] \\ gvs [EL_MAP])
      \\ gvs [FINITE_UNION, freevars_FINITE, FINITE_BIGUNION]
      \\ rename1 ‘ALL_DISTINCT l’
      \\ first_x_assum $ qspecl_then [‘l’] assume_tac
      \\ irule needs_exp_eq
      \\ qexists_tac ‘Apps (Lams l (Apps f (MAP Var l))) eL’
      \\ conj_tac
      >- (gvs [needs_def, demands_def]
          \\ irule exp_eq_in_ctxt_trans
          \\ irule_at Any exp_eq_in_ctxt_Apps
          \\ irule_at Any exp_eq_in_ctxt_l_refl
          \\ irule_at Any exp_eq_in_ctxt_Lams
          \\ pop_assum $ irule_at Any
          \\ conj_tac
          >- (irule $ iffLR SUBSET_EMPTY
              \\ irule $ iffRL SUBSET_DEF
              \\ gvs [IN_INTER, DISJ_EQ_IMP, EVERY_MEM])
          \\ irule exp_eq_trans
          \\ irule_at Any Apps_Lams_Seq_strong
          \\ irule_at Any exp_eq_Prim_cong
          \\ gvs [exp_eq_refl]
          \\ irule_at Any exp_eq_trans
          \\ irule_at Any Apps_Lams_fold
          \\ irule_at Any exp_eq_trans
          \\ irule_at Any FoldLets_Projs
          \\ irule_at Any exp_eq_Projs_cong
          \\ irule_at Any exp_eq_trans
          \\ irule_at Any $ iffLR exp_eq_sym
          \\ irule_at Any Apps_Lams_fold
          \\ fs []
          \\ conj_tac
          >- (irule eval_wh_IMP_exp_eq
              \\ gen_tac \\ rpt strip_tac
              \\ qspecl_then [‘ZIP (l, MAP (subst f') eL)’, ‘subst (FDIFF f' (set l)) (Var (EL i l))’] assume_tac eval_Apps_Lams
              \\ qabbrev_tac ‘kvl = ZIP (l, MAP (subst f') eL)’
              \\ ‘ALL_DISTINCT (MAP FST kvl)’
                by (unabbrev_all_tac
                    \\ gvs [MAP_ZIP])
              \\ dxrule ALL_DISTINCT_FLOOKUP
              \\ strip_tac
              \\ pop_assum $ qspecl_then [‘EL i l’, ‘subst f' (EL i eL)’, ‘FEMPTY’] assume_tac
              \\ unabbrev_all_tac
              \\ ‘MEM (EL i l, subst f' (EL i eL)) (ZIP (l, MAP (subst f') eL))’
                by (gvs [MEM_EL]
                    \\ qexists_tac ‘i’
                    \\ gvs [EL_ZIP, EL_MAP])
              \\ gvs [MAP_ZIP, subst_Apps, subst_Lams, subst_def, FLOOKUP_FDIFF, EL_MEM,
                      EVERY_EL, EL_ZIP, BIGUNION_SUBSET, DISJOINT_EMPTY, FUPDATE_LIST, FLOOKUP_EMPTY]
              \\ first_x_assum irule
              \\ ‘∀v. v ∈ FRANGE f' ⇒ closed v’ by gvs [FRANGE_FLOOKUP]
              \\ rw [EL_MAP, closed_def, freevars_subst, SUBSET_DIFF_EMPTY]
              \\ first_x_assum $ irule_at Any
              \\ gvs [MEM_MAP]
              \\ irule_at Any EL_MEM
              \\ pop_assum $ irule_at Any
              \\ fs [])
          \\ gvs [EVERY_MEM]
          \\ rw []
          \\ first_x_assum dxrule
          \\ rw []
          \\ pop_assum $ qspecl_then [‘freevars e’] assume_tac
          \\ fs [MEM_MAP]
          \\ pop_assum $ qspecl_then [‘e’] assume_tac
          \\ gvs [])
      \\ qspecl_then [‘ZIP (l, eL)’] assume_tac eta_red_fold
      \\ irule exp_eq_trans
      \\ irule_at Any Apps_Lams_fold
      \\ gvs [MAP_ZIP]
      \\ pop_assum $ irule_at Any
      \\ gvs [EVERY_CONJ, EVERY_MEM]
      \\ rw []
      \\ first_x_assum drule
      \\ rpt strip_tac
      \\ first_x_assum $ qspecl_then [‘freevars e’] assume_tac
      \\ gvs [MEM_MAP])
  >- (qexists_tac ‘{}’
      \\ rw []
      \\ pop_assum $ qspecl_then [‘MAP Var l’] assume_tac
      \\ gvs [EL_MAP, needs_Var_is_demands])
QED*)

Definition find_fdemands_def:
  find_fdemands (fd: (string # ((string # num) list # num) # num) -> bool) (Var n) = {[], n} ∧
  find_fdemands fd (Seq e1 e2) = find_fdemands fd e1 ∪ find_fdemands fd e2 ∧
  find_fdemands fd (If e1 e2 e3) = find_fdemands fd e1 ∪
                              (find_fdemands fd e2 ∩ find_fdemands fd e3) ∧
  find_fdemands fd e = {}
End

(*Theorem find_fdemands_with_eval_to_soundness:
  ∀e k fd. (∀n p len k2. (n, p, len) ∈ fd ∧ k2 ≤ k ⇒ (Var n) fdemands_depth (p, len, k2))
           ⇒ ∀ps v. (ps, v) ∈ find_fdemands fd e
                    ⇒ ∀f. freevars e ⊆ FDOM f ∧ is_bot (eval_wh_to k (subst f (Projs ps (Var v))))
                          ⇒ is_bot (eval_wh_to k (subst f e))
Proof
  Induct using freevars_ind
  \\ fs [find_fdemands_def, Projs_def]
  \\ rename1 ‘Prim op es’
  \\ Cases_on ‘op’
  \\ Cases_on ‘es’
  \\ fs [find_fdemands_def]
  \\ rename1 ‘e1::tl’
  \\ Cases_on ‘tl’
  \\ fs [find_fdemands_def]
  \\ rename1 ‘e1::e2::tl’
  \\ Cases_on ‘tl’
  \\ fs [find_fdemands_def]
  >~ [‘Prim If (e1::e2::e3::t)’]
  >- (Cases_on ‘t’
      \\ fs [find_fdemands_def]
      \\ rw []
      \\ rename1 ‘(ps, v) ∈ find_fdemands fd e’
      \\ last_assum $ qspecl_then [‘e’] assume_tac
      \\ gvs []
      \\ ‘∀n p len k2. (n, p, len) ∈ fd ∧ k2 ≤ (k - 1) ⇒ Var n fdemands_depth (p, len, k2)’
        by (rw []
            \\ first_x_assum irule
            \\ gvs [])
      \\ first_x_assum drule
      \\ strip_tac
      \\ pop_assum drule
      \\ strip_tac
      \\ pop_assum drule
      \\ strip_tac
      \\ ‘k - 1 ≤ k’ by fs []
      \\ drule is_bot_continuous
      \\ strip_tac
      \\ pop_assum dxrule
      \\ strip_tac
      \\ fs [eval_wh_to_def, is_bot_def, subst_def]
      \\ IF_CASES_TAC
      \\ gvs []
      \\ rename1 ‘_ = ec ∨ _ = et ∨ _ = ee’
      \\ CASE_TAC \\ fs [] \\ rpt (IF_CASES_TAC \\ fs [])
      \\ first_x_assum irule
      \\ gvs []
      \\ first_x_assum $ irule_at Any
      \\ rw []
      \\ first_x_assum $ irule_at Any
      \\ gvs [])
  \\ rw []
  \\ rename1 ‘(ps, v) ∈ find_fdemands fd e’
  \\ last_x_assum $ qspecl_then [‘e’] assume_tac
  \\ fs []
  \\ ‘∀n p len k2. (n, p, len) ∈ fd ∧ k2 ≤ (k - 1) ⇒ Var n fdemands_depth (p, len, k2)’
        by (rw []
            \\ first_x_assum irule
            \\ gvs [])
  \\ first_x_assum dxrule
  \\ strip_tac
  \\ pop_assum dxrule
  \\ strip_tac
  \\ pop_assum dxrule
  \\ strip_tac
  \\ ‘k - 1 ≤ k’ by fs []
  \\ dxrule_then assume_tac is_bot_continuous
  \\ pop_assum $ dxrule_then assume_tac
  \\ gvs [eval_wh_to_def, is_bot_def, subst_def]
  \\ Cases_on ‘k’
  \\ fs []
  \\ rename1 ‘if p = wh_Diverge ∨ p = wh_Error then _ else _’
  \\ Cases_on ‘p’
  \\ fs []
QED*)

(*Theorem find_fdemands_soundness:
  ∀e fd. (∀n p k. (n, p, k) ∈ fd ⇒ (Var n) fdemands (p, k)) ⇒ ∀d. d ∈ find_fdemands fd e ⇒ e demands d
Proof
  Induct using freevars_ind
  \\ fs [find_fdemands_def, demands_Var]
  \\ rename1 ‘Prim op es’
  \\ Cases_on ‘op’
  \\ Cases_on ‘es’
  \\ fs [find_fdemands_def]
  \\ rename1 ‘e1::tl’
  \\ Cases_on ‘tl’
  \\ fs [find_fdemands_def]
  \\ rename1 ‘e1::e2::tl’
  \\ Cases_on ‘tl’
  \\ fs [find_fdemands_def]
  >~ [‘Prim If (e1::e2::e3::t)’]
  >- (Cases_on ‘t’
      \\ fs [find_fdemands_def]
      \\ rw []
      \\ rename1 ‘d ∈ find_fdemands fd e’
      \\ last_assum $ qspecl_then [‘e’] assume_tac
      \\ fs []
      \\ pop_assum drule
      \\ strip_tac
      \\ pop_assum drule
      \\ strip_tac
      \\ fs [demands_If]
      \\ rename1 ‘If ec et ee’
      \\ last_x_assum $ qspecl_then [‘et’] assume_tac
      \\ fs []
      \\ pop_assum dxrule
      \\ strip_tac
      \\ pop_assum dxrule
      \\ strip_tac
      \\ fs [demands_If2])
  \\ rw []
  \\ rename1 ‘d ∈ find_fdemands fd e’
  \\ last_x_assum $ qspecl_then [‘e’] assume_tac
  \\ fs []
  \\ pop_assum dxrule
  \\ strip_tac
  \\ pop_assum dxrule
  \\ strip_tac
  \\ fs [demands_Seq, demands_Seq2]
QED*)

Theorem demands_foldr:
  ∀l c e ps v. e demands ((ps, v), FOLDL (λc2 (v, e1) . Bind v e1 c2) c l) ∧ ¬MEM v (MAP FST l)
               ⇒ (FOLDR (λ(v, e1) e2. Let v e1 e2) e l) demands ((ps, v), c)
Proof
  Induct
  \\ fs []
  \\ PairCases
  \\ rw []
  \\ irule demands_Let2
  \\ fs []
QED

(*Theorem demands_means_fdemands_lemma:
  ∀l1 l2 e i ps c. i < LENGTH l1 ∧ LENGTH l1 = LENGTH l2
    ∧ e demands ((ps, EL i l1), FOLDL (λc (v, e). Bind v e c) c (ZIP (l1, MAP Var l2)))
    ∧ ALL_DISTINCT l1
    ∧ EVERY (λv. ¬MEM v l2) l1 ∧ EVERY (λv. ¬MEM v l1) l2
       ⇒ (FOLDR (λ(v1, e1) e2. Let v1 e1 e2) e (ZIP (l1, MAP Var l2))) demands ((ps, EL i l2), c)
Proof
  Induct
  \\ fs []
  \\ gen_tac
  \\ Cases
  \\ rw []
  \\ rename1 ‘EL i (hd::tl)’
  \\ Cases_on ‘i’
  \\ gvs []
  >- (irule demands_Let3
      \\ irule_at Any demands_foldr
      \\ gvs [MAP_ZIP])
  \\ irule demands_Let2
  \\ first_x_assum $ irule_at Any
  \\ gvs [EL_MEM, EVERY_CONJ]
  \\ strip_tac
  \\ qpat_x_assum ‘¬MEM h tl’ irule
  \\ gvs [EL_MEM]
QED*)

(*Theorem demands_means_fdemands:
  ∀l e i ps. i < LENGTH l ∧ e demands ((ps, EL i l), FOLDL (λc v. IsFree v c) c l) ∧ ALL_DISTINCT l
             ⇒ Lams l e fdemands ((ps, i), LENGTH l, c)
Proof
  rw [fdemands_def]
  \\ qexists_tac ‘set l’
  \\ fs [FINITE_LIST_TO_SET]
  \\ rw []
  \\ irule exp_eq_same_demands
  \\ irule_at Any demands_means_fdemands_lemma
  \\ irule_at Any $ iffLR exp_eq_in_ctxt_sym
  \\ irule_at Any exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Apps_Lams_fold
  \\ dxrule $ iffRL SUBSET_EMPTY
  \\ strip_tac
  \\ dxrule $ iffLR SUBSET_DEF
  \\ strip_tac
  \\ gvs [EVERY_MAP, IN_INTER, EVERY_MEM]
  \\ irule_at Any demands_IsFree_List
  \\ rw [MAP_ZIP]
  \\ metis_tac []
QED*)

(*Theorem find_fdemands_Lambda_soundness:
  ∀e l fname c. ALL_DISTINCT l ∧ i < LENGTH l ∧ (ps, EL i l) ∈ find_fdemands {} e
                 ⇒ (Lams l e) fdemands ((ps, i), LENGTH l, c)
Proof
  rw []
  \\ irule demands_means_fdemands
  \\ fs []
  \\ irule find_fdemands_soundness
  \\ pop_assum $ irule_at Any
  \\ gvs []
QED*)

Theorem is_bot_eval_wh_to_Apps:
  ∀eL k f. is_bot (eval_wh_to k f) ⇒ is_bot (eval_wh_to k (Apps f eL))
Proof
  Induct
  \\ rw []
  \\ fs [Apps_def, eval_wh_to_def, is_bot_def]
QED

(*
Theorem find_fdemands_Letrec:
  ∀k e fd fname vL.ALL_DISTINCT vL ∧
                   (∀n ps i l. (n, (ps, i), l) ∈ fd ⇒ l = LENGTH vL ∧ n = fname ∧ (ps, EL i vL) ∈ find_fdemands fd e)
                 ⇒ ∀ps i. (ps, EL i vL) ∈ find_fdemands fd e
                          ⇒ ∀f eL. is_bot (eval_wh_to k (subst f (Projs ps (EL i eL)))) ∧ LENGTH eL = LENGTH vL
                                     ⇒ is_bot (eval_wh_to k (subst f (
                                                              Apps
                                                                (Letrec [(fname, Lams vL e)] (Var fname))
                                                                eL)))
Proof
  Induct
  >- (rw [subst_Apps, subst_def, subst_Lams, FLOOKUP_FDIFF]
      \\ irule is_bot_eval_wh_to_Apps
      \\ rw [eval_wh_to_def, is_bot_def])
  \\
*)

(*Theorem find_fdemands_Letrec_soundness:
  ∀e fd l fname. ALL_DISTINCT l
              ∧ (∀n ps i k. (n, (ps, i), k) ∈ fd ∧ n = fname ⇒ k = LENGTH l ∧ (ps, EL i l) ∈ find_fdemands fd e)
                 ⇒ ∀p k. (fname, p, k) ∈ fd ⇒ (Letrec [(fname, Lams l e)] (Var fname)) fdemands (p, k)
Proof
  rw []
  \\ cheat
QED*)

Theorem Lam_require:
  ∀l l' i h c.
    LENGTH l = LENGTH l' ∧ ¬MEM h l ⇒
    Apps (Lams l (Var h)) l' demands (([], h), c)
Proof
  Induct
  \\ fs [Apps_def, Lams_def, demands_Var]
  \\ gen_tac
  \\ Cases
  \\ rw [Apps_def]
  \\ irule exp_eq_same_demands
  \\ first_x_assum $ irule_at Any
  \\ last_x_assum $ irule_at Any
  \\ fs []
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_Apps_cong
  \\ fs [exp_eq_l_refl]
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_thm]
  \\ AP_TERM_TAC
  \\ ‘∀v. v ∈ FRANGE f ⇒ closed v’ by
    (rw []
     \\ first_x_assum irule
     \\ fs [FRANGE_FLOOKUP]
     \\ first_x_assum $ irule_at Any)
  \\ ‘closed (subst f h')’ by gvs [freevars_subst, closed_def, SUBSET_DIFF_EMPTY]
  \\ fs [bind1_def, subst_Lams, subst1_def, subst_def, FLOOKUP_FDIFF,
         DOMSUB_FLOOKUP_NEQ, FLOOKUP_DEF]
QED

Theorem subst1_Lams:
  ∀l h e e'. ¬ MEM h l ⇒ subst1 h e (Lams l e') = Lams l (subst1 h e e')
Proof
  Induct
  \\ fs [Lams_def]
  \\ rw [bind1_def, subst1_def]
QED

(*Theorem Lams_require_arg:
  ∀l i.
    ALL_DISTINCT l ∧ i < LENGTH l ⇒
    Lams l (Var (EL i l)) fdemands (([], i), LENGTH l, c)
Proof
  Induct
  \\ fs [Lams_def, fdemands_def]
  \\ gen_tac
  \\ Cases
  \\ strip_tac
  \\ gvs []
  >- (Cases
      \\ fs [Apps_def]
      \\ strip_tac
      \\ irule needs_exp_eq
      \\ irule_at Any needs_Let1
      \\ irule_at Any demands_Var
      \\ irule_at Any Lam_require
      \\ rename1 ‘MAP Var t’
      \\ qspecl_then [‘l++t’] assume_tac exists_str_not_in_list
      \\ fs [MEM_APPEND]
      \\ qexists_tac ‘l’
      \\ qexists_tac ‘MAP Var t’
      \\ rename1 ‘MEM s t’
      \\ first_assum $ irule_at Any
      \\ fs [LENGTH_MAP, Once exp_eq_in_ctxt_sym]
      \\ irule exp_eq_IMP_exp_eq_in_ctxt
      \\ irule exp_eq_trans
      \\ irule_at (Pos last) Apps_Let
      \\ conj_tac
      >- (rw [EVERY_EL, EL_MAP]
          \\ strip_tac
          \\ gvs [MEM_EL])
      \\ irule exp_eq_Apps_cong
      \\ fs [exp_eq_l_refl]
      \\ irule eval_wh_IMP_exp_eq
      \\ rw [subst_def, subst_Lams, eval_wh_thm, FLOOKUP_DEF]
      \\ AP_TERM_TAC
      \\ simp [bind1_def]
      \\ rw [subst1_Lams, subst1_def])
  \\ first_x_assum drule
  \\ strip_tac
  \\ first_x_assum $ irule_at Any
  \\ Cases
  \\ fs [Apps_def]
  \\ strip_tac
  \\ irule exp_eq_same_demands
  \\ first_x_assum $ irule_at Any
  \\ rename1 ‘h2 INSERT _’
  \\ Cases_on ‘h2 ∈ s’
  \\ gvs [INSERT_INTER]
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ irule exp_eq_Apps_cong
  \\ fs [exp_eq_l_refl]
  \\ irule eval_wh_IMP_exp_eq
  \\ rw []
  \\ fs [MEM_EL, subst_def, eval_wh_thm, FLOOKUP_DEF, bind1_def]
  \\ ‘closed (Lams l (Var (EL n' l)))’ by fs [closed_Lams, EL_MEM]
  \\ fs [closed_subst]
QED*)

Theorem exists_diff_list_commute:
  ∀(l : string list) s. FINITE s ⇒ ∃l'. LENGTH l = LENGTH l' ∧ ALL_DISTINCT l' ∧ EVERY (λv. v ∉ s ∧ ¬ MEM v l) l'
Proof
  Induct
  \\ fs []
  \\ rw []
  \\ first_x_assum $ qspecl_then [‘s ∪ {h}’] assume_tac
  \\ fs [FINITE_UNION, FINITE_SING]
  \\ pop_assum drule
  \\ rw []
  \\ ‘INFINITE 𝕌(:string)’ by simp []
  \\ ‘∃x. x ∉ set l' ∪ set l ∪ s ∪ {h}’ by
    fs[pred_setTheory.NOT_IN_FINITE, FINITE_UNION, FINITE_SING]
  \\ qexists_tac ‘x::l'’
  \\ fs [EVERY_EL]
QED

Definition dest_fd_SND_def:
  dest_fd_SND NONE = {} ∧
  dest_fd_SND (SOME (bL, s)) = s
End

Inductive find: (* i i i o o o *)
[find_Drop_fd:]
  (∀e e' c fds ds fd.
     find e c fds ds e' fd ⇒ find e c fds ds e' NONE) ∧
[find_smaller_fd:]
  (∀e e' c fds ds bL fd fd'.
     find e c fds ds e' (SOME (bL, fd)) ∧ fd' ⊆ fd
     ⇒ find e c fds ds e' (SOME (bL, fd'))) ∧
[find_Bottom:]
  (∀e (c:ctxt) (fdc : (string # (bool list)) -> bool).
    find e c fdc {} e NONE) ∧
[find_Seq:]
  (∀e e' c (p:(string#num) list) ds v fdc fd.
    find e c fdc ds e' fd ∧ (p,v) ∈ ds ⇒
    find e c fdc ds (Seq (Var v) e') fd) ∧
[find_Seq2:]
  (∀e e' e2 e2' c ds ds2 fdc fd fd2.
     find e c fdc ds e' fd ∧ find e2 c fdc ds2 e2' fd2 ⇒
     find (Seq e e2) c fdc (ds ∪ ds2) (Seq e' e2') fd2) ∧
[find_If:]
  (∀ec et ee ec' et' ee' c dsc dst dse fdc fd fdt fde.
     find ec c fdc dsc ec' fd
     ∧ find et c fdc dst et' fdt
     ∧ find ee c fdc dse ee' fde
     ⇒ find (If ec et ee) c fdc (dsc ∪ (dst ∩ dse)) (If ec' et' ee') NONE) ∧
[find_Var:]
  (∀n c fdc. find (Var n) c fdc {([],n)} (Var n) NONE) ∧
[find_Var2:]
  (∀n c fdc argsDemanded.
     (n, argsDemanded) ∈ fdc
     ⇒ find (Var n) c fdc {([],n)} (Var n) (SOME (argsDemanded, {}))) ∧
[find_No_args:]
  (∀c fdc e e' ds ds'.
     find e c fdc ds e' (SOME ([], ds'))
     ⇒ find e c fdc (ds ∪ ds') e' NONE) ∧
[find_App:]
  (∀f f' e e' fdc c ds ds2 fd1 fd2.
     find f c fdc ds f' fd1 ∧
     find e c fdc ds2 e' fd2 ⇒
     find (App f e) c fdc ds (App f' e') NONE) ∧
[find_App_arg_strict:]
  (∀f f' e e' fdc c ds ds2 ds3 fd argD.
     find f c fdc ds f' (SOME (T::argD, ds3))
     ∧ find e c fdc ds2 e' fd
     ⇒ find (App f e) c fdc ds (App f' e') (SOME (argD, ds2 ∪ ds3))) ∧
[find_App_arg_not_strict:]
  (∀f f' e e' fdc c ds ds2 ds3 fd argD b.
     find f c fdc ds f' (SOME (b::argD, ds3))
     ∧ find e c fdc ds2 e' fd
     ⇒ find (App f e) c fdc ds (App f' e') (SOME (argD, ds3))) ∧
[find_Apps:]
  (∀f f' el el' c ds fdc fd.
     LIST_REL (λe e'. ∃ds fd. find e c fdc ds e' fd) el el' ∧
     find f c fdc ds f' fd ⇒ find (Apps f el) c fdc ds (Apps f' el') NONE) ∧
[find_Apps_fd:]
  (∀f f' el el' c ds ds' fdc bL fd dsL.
     LIST_REL (λe (ds, e'). ∃ fd. find e c fdc ds e' fd) el (ZIP (dsL, el'))
     ∧ LENGTH el' = LENGTH bL ∧ LENGTH dsL = LENGTH el'
     ∧ find f c fdc ds f' (SOME (bL, fd))
     ∧ (∀p. p ∈ ds' ⇒ p ∈ ds ∨ ∃i. i < LENGTH bL ∧ p ∈ EL i dsL ∧ EL i bL)
     ⇒ find (Apps f el) c fdc ds' (Apps f' el') NONE) ∧
[find_Prim:]
  (∀c el el' ope fdc.
     LENGTH el = LENGTH el' ∧ (∀k. k < LENGTH el ⇒ ∃ds fd. find (EL k el) c fdc ds (EL k el') fd)
     ⇒ find (Prim ope el) c fdc {} (Prim ope el') NONE) ∧
[find_Prim1:]
  (∀c el el' ope ds fdc fd.
      LIST_REL (λe e'. ∃ds2 fd2. find e c fdc ds2 e' fd2) el el'
      ∧ find (EL 0 el) c fdc ds (EL 0 el') fd ∧ el ≠ [] ∧ well_formed ope el
      ⇒ find (Prim ope el) c fdc ds (Prim ope el') NONE) ∧
[find_Prim_Fail:]
  (∀c el ope fdc.
     ¬ (well_written ope el) ⇒ find (Prim ope el) c fdc {} Fail NONE) ∧
[find_Proj:]
  (∀e e' n i c ds fdc fd.
     find e c fdc ds e' fd ⇒ find (Proj n i e) c fdc ds (Proj n i e') NONE) ∧
[find_IsEq:]
  (∀e e' n i c ds fdc fd.
     find e c fdc ds e' fd ⇒ find (IsEq n i e) c fdc ds (IsEq n i e') NONE) ∧
[find_Atom:]
  (∀el dsl el' fdc c op fd.
     LENGTH dsl = LENGTH el' ∧
     LIST_REL (λe (ds, e'). find e c fdc ds e' fd) el (ZIP (dsl, el')) ⇒
     find (Prim (AtomOp op) el) c fdc (BIGUNION (set dsl)) (Prim (AtomOp op) el') NONE) ∧
[find_Subset:]
  (∀e e' c ds ds' fdc fdc' fd.
     find e c fdc' ds e' fd
     ∧ (∀ps v. (ps, v) ∈ ds' ⇒ ∃ps'. (ps++ps', v) ∈ ds)
     ∧ fdc' ⊆ fdc
     ⇒ find e c fdc ds' e' fd) ∧
[find_Let:]
  (∀e e' e2 e2' ds ds' c v fdc fdc' fd fd'.
     find e c fdc ds e' fd ∧ find e2 (Bind v e c) fdc' ds' e2' fd'
     ∧ (∀ps. (ps, v) ∉ ds')
     ∧ (∀n argDemands. (n, argDemands) ∈ fdc' ⇒ (n ≠ v ∧ (n, argDemands) ∈ fdc))
     ∧ (∀l. (l, v) ∉ dest_fd_SND fd')
     ⇒ find (Let v e e2) c fdc ds' (Let v e' e2') fd') ∧
[find_Let2:]
  (∀ e e' e2 e2' ds ds' ds'' c v ps fdc fdc' fd fd'.
     find e c fdc ds e' fd ∧ find e2 (Bind v e c) fdc' ds' e2' fd'
     ∧ (ps,v) ∈ ds'
     ∧ (∀ps' v'. (ps', v') ∈ ds'' ⇒ ((ps', v') ∈ ds' ∧ v' ≠ v) ∨ (ps', v') ∈ ds)
     ∧ (∀n argDemands. (n, argDemands) ∈ fdc' ⇒ n ≠ v ∧ (n, argDemands) ∈ fdc)
     ∧ (∀l. (l, v) ∉ dest_fd_SND fd')
     ⇒ find (Let v e e2) c fdc ds'' (Let v e' e2') fd') ∧
[find_Lam:]
  (∀e e' c ds v fdc fd.
     find e (IsFree v c) fdc ds e' fd ∧ (∀argDs. (v, argDs) ∉ fdc)
     ⇒ find (Lam v e) c fdc {} (Lam v e') NONE) ∧
[find_Lams:]
  (∀e e' c ds vl fdc fd.
     find e (FOLDL (λc n. IsFree n c) c vl) fdc ds e' fd
     ∧ EVERY (λv. ∀argDs. (v, argDs) ∉ fdc) vl
     ⇒ find (Lams vl e) c fdc {} (Lams vl e') NONE ) ∧
[find_Lams_fd:]
  (∀e e' c ds vl fdc bL.
     find e (FOLDL (λc n. IsFree n c) c vl) fdc ds e' NONE
     ∧ EVERY (λv. ∀argDs. (v, argDs) ∉ fdc) vl
     ∧ LIST_REL (λb v. if b then ∃ps. (ps, v) ∈ ds else T) bL vl
     ⇒ find (Lams vl e) c fdc {} (Lams vl e') (SOME (bL, {}))) ∧
[find_Eq:]
  (∀e e' c fdc. exp_eq_in_ctxt c e e' ⇒ find e c fdc {} e' NONE) ∧
[find_Letrec:]
  (∀e e' ds c b b' fdc fd.
     LIST_REL (λ(n1, e1) (n2, e2). n1 = n2 ∧ e1 ≈ e2) b b'
     ∧ find e (RecBind b c) fdc ds e' fd
     ∧ EVERY (λv. ∀argDs. (v, argDs) ∉ fdc) (MAP FST b)
     ⇒ find (Letrec b e) c fdc {} (Letrec b e') NONE)
End

fun apply_to_first_n 0 tac = ALL_TAC
  | apply_to_first_n n tac = apply_to_first_n (n-1) tac >- tac;

Theorem fdemands_IsFree:
  ∀d c v e len. v ∉ freevars e ∧ e fdemands (d, len, c) ⇒ e fdemands (d, len, IsFree v c)
Proof
  rw [fdemands_def] >> irule fdemands_exp_eq >> first_x_assum $ irule_at Any >>
  irule exp_eq_IMP_exp_eq_in_ctxt >>
  irule eval_IMP_exp_eq >> dxrule $ GSYM subst_fdomsub >>
  rw [subst_def, eval_thm, IMP_closed_subst, FRANGE_FLOOKUP, bind1_def]
QED

Theorem fdemands_Bind:
  ∀d c v e e2 len. v ∉ freevars e ∧ e fdemands (d, len, c) ⇒ e fdemands (d, len, Bind v e2 c)
Proof
  rw [fdemands_def] >> irule fdemands_exp_eq >> first_x_assum $ irule_at Any >>
  irule exp_eq_IMP_exp_eq_in_ctxt >>
  irule eval_IMP_exp_eq >> dxrule $ GSYM subst_fdomsub >>
  rw [subst_def, eval_thm, IMP_closed_subst, FRANGE_FLOOKUP, bind1_def]
QED

Theorem fdemands_App:
  ∀c e e2 ps i len. e fdemands ((ps, SUC i), SUC len, c) ⇒ App e e2 fdemands  ((ps, i), len, c)
Proof
  Induct
  >- (rw [fdemands_def, GSYM Apps_def] >>
      rename1 ‘e2::l’ >> pop_assum $ qspecl_then [‘e2::l’] assume_tac >>
      gvs []) >>
  rw [fdemands_def] >> irule fdemands_exp_eq >>
  rpt $ last_x_assum $ irule_at Any >>
  irule_at Any $ iffLR exp_eq_in_ctxt_sym
  >~[‘Letrec’] >- (irule_at Any exp_eq_IMP_exp_eq_in_ctxt >> irule_at Any Letrec_App) >>
  irule_at Any Let_App_in_ctxt
QED

Theorem fdemands_App2:
  ∀d e e2 eL len c. e fdemands (([], 0), SUC len, c) ∧ e2 demands (d, c) ∧ LENGTH eL = len
            ⇒ Apps (App e e2) eL demands (d, c)
Proof
  PairCases >> rw [] >>
  dxrule_then assume_tac fdemands_alt >>
  gvs [fdemands_def, GSYM Apps_def, GSYM needs_Var_is_demands] >>
  rename1 ‘e2::eL’ >> last_x_assum $ qspecl_then [‘e2::eL’] assume_tac >>
  irule needs_trans >>
  pop_assum $ irule_at Any >>
  gvs []
QED

Theorem fdemands_subset:
  ∀fdc fdc'.
    (∀n l i. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, c))
    ∧ fdc' ⊆ fdc
    ⇒ (∀n l i. (n, l) ∈ fdc' ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, c))
Proof
  gvs [SUBSET_DEF]
QED

Theorem fdemands_set_Bind:
  ∀fdc v e.
    (∀n l i. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, c))
    ∧ (∀n l. (n, l) ∈ fdc ⇒ n ≠ v)
    ⇒ (∀n l i. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l
               ⇒ Var n fdemands (([], i), LENGTH l, Bind v e c))
Proof
  rw []
  \\ irule fdemands_Bind
  \\ gvs []
  \\ strip_tac \\ gvs []
QED

Theorem fdemands_set_IsFree:
  ∀fdc v.
    (∀n l i. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, c))
    ∧ (∀l. (v, l) ∉ fdc)
    ⇒ (∀n l i. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l
               ⇒ Var n fdemands (([], i), LENGTH l, IsFree v c))
Proof
  rw []
  \\ irule fdemands_IsFree
  \\ gvs []
  \\ strip_tac \\ gvs []
QED

Theorem fdemands_set_FOLDL_IsFree:
  ∀vL fdc c.
    (∀n l i. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, c))
    ∧ EVERY (λv. ∀argDs. (v, argDs) ∉ fdc) vL
    ⇒ (∀n l i. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l
               ⇒ Var n fdemands (([], i), LENGTH l, FOLDL (λc n. IsFree n c) c vL))
Proof
  Induct \\ rw []
  \\ last_x_assum irule
  \\ gvs []
  \\ last_assum $ irule_at Any
  \\ dxrule_then assume_tac fdemands_set_IsFree
  \\ pop_assum $ dxrule_then assume_tac
  \\ fs []
QED

Theorem Letrec_Apps:
  ∀eL bL e b. (Letrec bL (Apps e eL) ≅? Apps (Letrec bL e) (MAP (Letrec bL) eL)) b
Proof
  Induct >> rw [Apps_def, exp_eq_refl] >>
  irule exp_eq_trans >> pop_assum $ irule_at Any >>
  irule exp_eq_Apps_cong >> gvs [exp_eq_l_refl, Letrec_App]
QED

Theorem fdemands_RecBind:
  ∀c p l e b. e fdemands (p, l, c)
              ∧ EVERY (λv. v ∉ freevars e) (MAP FST b)
              ⇒ e fdemands (p, l, RecBind b c)
Proof
  rw [fdemands_def] >> irule fdemands_exp_eq >>
  last_x_assum $ irule_at Any >>
  irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >>
  gvs [Letrec_not_in_freevars]
QED

(*Theorem rewrite_fdemands:
  ∀c f len ps. (∀e. App f e needs_when_applied ((ps, e), len, c))
                   ⇒ f fdemands ((ps, 0), SUC len, c)
Proof
  Induct >>
  gvs [fdemands_def, needs_when_applied_def, eq_when_applied_def]
  >- (gvs [needs_def, exp_eq_in_ctxt_def, GSYM Apps_def] >>
      rpt $ gen_tac >> strip_tac >> Cases >> rw [] >>
      irule exp_eq_trans >> pop_assum $ irule_at Any >> fs [Apps_def, Apps_Seq]) >>
  rw [] >> last_x_assum irule >> gen_tac >>
  irule eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
  irule_at Any eq_when_applied_trans >> last_x_assum $ irule_at Any >>
  once_rewrite_tac [exp_eq_sym] >>
  irule_at Any exp_eq_in_ctxt_IMP_eq_when_applied >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt
        
  >- (eq_tac >> rw [])
QED*)

Theorem Letrec_closed:
  ∀l e b. closed e ⇒ (Letrec l e ≅? e) b
Proof
  cheat
QED
        
Theorem Lam_fdemand:
  ∀c v e ps len. e demands_when_applied ((ps, v), len, IsFree v c)
                 ⇒ Lam v e fdemands ((ps, 0), SUC len, c)
Proof
  Induct >> gvs [demands_when_applied_def, eq_when_applied_def, fdemands_def]
  >- (rpt $ gen_tac >> strip_tac >> Cases >> gvs [Apps_def, needs_def, exp_eq_in_ctxt_def] >>
      rw [] >> irule exp_eq_trans >> last_x_assum $ irule_at Any >> fs [] >>
      conj_tac >- cheat >>
      irule exp_eq_trans >> irule_at Any exp_eq_Apps_cong >>
      irule_at Any exp_eq_l_refl >> irule_at (Pos hd) Let_Seq >>
      irule exp_eq_trans >> irule_at Any Apps_Seq >>
      irule exp_eq_Prim_cong >> fs [exp_eq_refl] >>
      irule exp_eq_trans >> irule_at Any Let_Projs >>
      irule exp_eq_Projs_cong >> irule_at Any Let_Var) >>
  rw [] >>
  irule fdemands_exp_eq >>
  irule_at Any exp_eq_IMP_exp_eq_in_ctxt
  >~[‘Letrec lcs (Lam v e)’]
  >- (irule_at Any exp_eq_trans >>
      irule_at (Pos $ el 2) exp_eq_Letrec_cong >>
      irule_at Any exp_eq_l_refl >>
      once_rewrite_tac [exp_eq_sym] >> irule_at Any exp_alpha_exp_eq >>
      irule_at Any exp_alpha_Alpha >>
      irule_at Any Letrec_Lam_weak >>
      ‘∃s. s ∉ BIGUNION (set (MAP freevars (MAP SND lcs))) ∪ set (MAP FST lcs)
             ∪ {v} ∪ freevars e’
        by (‘INFINITE 𝕌(:string)’ by simp [] >>
            dxrule_then irule $ iffLR NOT_IN_FINITE >>
            gvs [NOT_IN_FINITE, FINITE_BIGUNION, MEM_MAP] >> rw [] >> fs [freevars_FINITE]) >>
      fs [] >> first_assum $ irule_at Any >>
      fs [] >> conj_asm1_tac
      >- (rw [EVERY_MEM] >> rename1 ‘MEM e2 (MAP SND _)’ >>
          last_x_assum $ qspecl_then [‘freevars e2’] assume_tac >>
          gvs [MEM_MAP]) >>
      last_x_assum irule >> gen_tac >> strip_tac >>
      irule eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any Let_Letrec >> gvs [closed_def] >>
      irule eq_when_applied_trans_exp_eq >> irule_at Any exp_eq_IMP_exp_eq_in_ctxt >>
      irule_at Any exp_eq_Letrec_cong >> irule_at Any exp_eq_l_refl >>
      irule_at Any exp_eq_App_cong >> once_rewrite_tac [exp_eq_sym] >>
      irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
      irule_at Any exp_eq_refl >> gvs [] >>
      irule eq_when_applied_trans >> last_x_assum $ irule_at Any >> fs [] >>
      irule exp_eq_in_ctxt_IMP_eq_when_applied >> irule 
      
      ) >>
  irule_at Any exp_eq_trans >>
  irule_at (Pos $ el 2) exp_alpha_exp_eq >>
QED

Theorem Lams_fdemands:
  ∀c vl e ps i. i < LENGTH vl ∧ e demands ((ps, EL i vl), FOLDL (λc n. IsFree n c) c vl)
                ⇒ Lams vl e fdemands ((ps, i), LENGTH vl, c)
Proof
  Induct
  >- cheat >>
  rw [fdemands_def]
  >- 
  cheat
QED

Theorem fdemands_set_RecBind:
  ∀fdc c b.
    (∀n l i. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ Var n fdemands (([], i), LENGTH l, c))
    ∧ EVERY (λv. ∀argDs. (v, argDs) ∉ fdc) (MAP FST b)
    ⇒ (∀n l i. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l
               ⇒ Var n fdemands (([], i), LENGTH l, RecBind b c))
Proof
  rw [] >> irule fdemands_RecBind >>
  gvs [EVERY_EL, EL_MAP] >> rw [] >> strip_tac >>
  first_x_assum $ dxrule_then assume_tac >> gvs []
QED

(*Theorem Let_Let_nothing:
  ∀e s v b. v ≠ s ∧ s ∉ freevars e ⇒ (Let s (Var v) (Let v (Var s) e) ≅? e) b
Proof
  Induct using freevars_ind >> rpt strip_tac
  >~[‘Let s _ (Let v _ (Var n))’]
  >- (irule eval_IMP_exp_eq >>
      rw [Once eval_thm, subst_def] >>
      Cases_on ‘FLOOKUP f v’
      >~[‘FLOOKUP f v = NONE’] >- gvs [FLOOKUP_DEF] >>
      first_assum $ drule_then assume_tac >>
      Cases_on ‘n = v’ >>
      gvs [eval_thm, bind1_def, subst1_def, DOMSUB_FLOOKUP, DOMSUB_FLOOKUP_NEQ, FLOOKUP_UPDATE] >>
      Cases_on ‘FLOOKUP f n’ >> gvs [FLOOKUP_DEF])
  >~[‘Prim’]
  >- (irule exp_eq_trans >>
      irule_at Any exp_eq_App_cong >> irule_at Any exp_eq_Lam_cong >>
      irule_at Any Let_Prim >> irule_at Any exp_eq_refl >>
      irule_at Any exp_eq_trans >> irule_at Any Let_Prim >>
      irule exp_eq_Prim_cong >> rw [LIST_REL_EL_EQN, EL_MAP] >>
      last_x_assum irule >> gvs [EL_MEM] >>
      rename1 ‘EL n es’ >> last_x_assum $ qspecl_then [‘freevars (EL n es)’] assume_tac >> fs [] >>
      strip_tac >> first_x_assum irule >> gvs [MEM_EL] >>
      first_assum $ irule_at Any >> fs [EL_MAP])
  >~[‘Let s _ (Let v _ (App _ _))’]
  >- (irule exp_eq_trans >>
      irule_at (Pos hd) exp_eq_App_cong >> irule_at Any exp_eq_Lam_cong >>
      irule_at Any Let_App >> irule_at Any exp_eq_refl >>
      irule exp_eq_trans >> irule_at Any Let_App >>
      fs [exp_eq_App_cong])
  >~[‘Let s _ (Let v _ (Lam n e))’]
  >- (Cases_on ‘v = n’ >> rw []
      >~[‘Let _ _ (Let v _ (Lam v e))’]
      >- (irule exp_eq_trans >>
          irule_at Any exp_eq_App_cong >> irule_at (Pos hd) exp_eq_Lam_cong >>
          irule_at (Pos $ el 2) exp_eq_refl >>
          qexists_tac ‘Lam v e’ >> conj_tac >>
          irule eval_IMP_exp_eq >> rw [Ntimes subst_def 2] >>
          rename1 ‘subst (f \\ _)’ >> qspecl_then [‘f’, ‘Lam v e’] assume_tac $ GSYM subst_fdomsub >>
          gvs [eval_thm, bind1_def, subst1_ignore, IMP_closed_subst, FRANGE_FLOOKUP]) >>
      ‘∃s2. s2 ∉ freevars (Lam n e) ∪ {n} ∪ {v} ∪ {s} ’
        by (‘INFINITE 𝕌(:string)’ by simp [] >> gvs [NOT_IN_FINITE]) >>
      irule exp_eq_trans >> irule_at Any exp_eq_App_cong >>
      irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
      qexists_tac ‘s2’ >> once_rewrite_tac [perm_exp_def] >> irule_at Any exp_eq_refl >>
      irule_at Any exp_eq_trans >> irule_at Any exp_eq_App_cong >>
      irule_at (Pos hd) exp_eq_Lam_cong >> irule_at (Pos hd) exp_eq_App_cong >>
      once_rewrite_tac [perm_exp_def] >>
      irule_at (Pos hd) exp_eq_Lam_cong >> irule_at (Pos hd) $ iffLR exp_eq_sym >>
      irule_at (Pos hd) exp_alpha_exp_eq >> irule_at (Pos hd) exp_alpha_perm_irrel >>
      rpt $ irule_at Any exp_eq_refl >> gvs [perm_exp_def, perm1_def] >>
      irule exp_eq_trans >>
      irule_at Any exp_eq_App_cong >> irule_at (Pos hd) exp_eq_Lam_cong >>
      irule_at Any Let_Lam_weak >> irule_at Any exp_eq_refl >>
      irule_at Any exp_eq_trans >> irule_at Any Let_Lam_weak >>
      irule_at Any exp_eq_Lam_cong >> last_x_assum $ irule_at Any >>
      gvs [])
  >~[‘Let s _ (Let w _ (Letrec lcs _))’]
  >- (Cases_on ‘MEM w (MAP FST lcs)’
      >~[‘¬MEM w (MAP FST lcs)’]
      >- (‘∃s2. s2 ∉ freevars e ∪ BIGUNION (set (MAP freevars (MAP SND lcs)))
                   ∪ {w} ∪ set (MAP FST lcs) ∪ {s}’
            by (‘INFINITE 𝕌(:string)’ by simp [] >>
                dxrule_then irule $ iffLR NOT_IN_FINITE >>
                gvs [NOT_IN_FINITE, FINITE_BIGUNION, MEM_MAP] >>
                rw [] >> fs [freevars_FINITE]) >>
          irule exp_eq_trans >> irule_at Any exp_eq_App_cong >>
          irule_at (Pos hd) exp_alpha_exp_eq >> irule_at Any exp_alpha_Alpha >>
          qexists_tac ‘s2’ >> once_rewrite_tac [perm_exp_def] >> irule_at Any exp_eq_refl >>
          irule_at Any exp_eq_trans >> irule_at Any exp_eq_App_cong >>
          irule_at (Pos hd) exp_eq_Lam_cong >> irule_at (Pos hd) exp_eq_App_cong >>
          once_rewrite_tac [perm_exp_def] >>
          irule_at (Pos hd) exp_eq_Lam_cong >> irule_at (Pos hd) $ iffLR exp_eq_sym >>
          irule_at (Pos hd) exp_alpha_exp_eq >> irule_at (Pos hd) exp_alpha_perm_irrel >>
          rpt $ irule_at Any exp_eq_refl >> first_x_assum $ irule_at (Pos hd) >>
          gvs [perm_exp_def, perm1_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
          irule exp_eq_trans >>
          irule_at Any exp_eq_App_cong >> irule_at Any exp_eq_Lam_cong >>
          irule_at Any Let_Letrec2 >> irule_at Any exp_eq_refl >>
          irule_at (Pos last) exp_eq_trans >> irule_at (Pos hd) Let_Letrec2 >>
          irule_at Any exp_eq_Letrec_cong2 >>
          first_x_assum $ irule_at (Pos $ el 2) >>
          irule_at Any fmap_rel_FUPDATE_LIST_same >> irule_at Any LIST_EQ >>
          irule_at Any $ iffRL LIST_REL_EL_EQN >>
          gvs [EL_MAP, EVERY_EL, MEM_EL] >>
          rw [] >> rename1 ‘n < LENGTH lcs’ >> qabbrev_tac ‘p = EL n lcs’ >> PairCases_on ‘p’ >> gvs [EL_MAP]
          >- (last_x_assum irule >> first_assum $ irule_at Any >> gvs [] >>
              first_x_assum $ qspecl_then [‘freevars p1’] assume_tac >> fs [] >>
              pop_assum $ qspecl_then [‘n’] assume_tac >> gvs [EL_MAP])
          >- (strip_tac >> first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [EL_MAP])
          >- (strip_tac >> last_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [EL_MAP])
          >- (strip_tac >> first_x_assum $ qspecl_then [‘n’] assume_tac >> gvs [EL_MAP]))
      >- (irule exp_eq_trans >> irule_at Any exp_eq_App_cong >> irule_at (Pos hd) exp_eq_Lam_cong >>
          irule_at (Pos $ el 2) exp_eq_refl >>
          qexists_tac ‘Letrec lcs e’ >> conj_tac >>
          irule eval_IMP_exp_eq >> rw [Ntimes subst_def 2] >>
          rename1 ‘subst (f \\ _ )’ >> qspecl_then [‘f’, ‘Letrec lcs e’] assume_tac $ GSYM subst_fdomsub >>
          gvs [eval_thm, bind1_def, subst1_ignore, IMP_closed_subst, FRANGE_FLOOKUP]))
QED

Theorem demands_Apps2:
  ∀d v e e2 eL v c.
    (∀eL'. LENGTH eL' = LENGTH eL ⇒ Apps e2 eL' demands (d, Bind v e c)) ∧ v ≠ SND d
    ⇒ Apps (Let v e e2) eL demands (d, c)
Proof
  PairCases >> rw [GSYM needs_Var_is_demands, needs_def, exp_eq_in_ctxt_def] >>
  ‘∃s. s ∉ freevars (Let v e e2) ∪ {d1} ∪ BIGUNION (set (MAP freevars eL)) ∪ {v}’
    by (‘INFINITE 𝕌(:string)’ by simp [] >>
        dxrule_then irule $ iffLR NOT_IN_FINITE >>
        gvs [NOT_IN_FINITE, FINITE_BIGUNION, MEM_MAP] >> rw [] >> fs [freevars_FINITE]) >>
  irule exp_eq_in_ctxt_trans >> irule_at Any exp_eq_in_ctxt_Apps >>
  qexists_tac ‘MAP (λe. Let s (Var v) e) (MAP (λe. Let v (Var s) e) eL)’ >>
  qexists_tac ‘(Let s (Var v) (Let v e e2))’ >>
  conj_asm1_tac
  >- (rw [LIST_REL_EL_EQN, EL_MAP] >>
      irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >>
      irule Let_Let_nothing >> gvs [] >>
      rename1 ‘EL n eL’ >> first_x_assum $ qspecl_then [‘freevars (EL n eL)’] assume_tac >>
      gvs [MEM_MAP] >> pop_assum $ qspecl_then [‘EL n eL’] assume_tac >> gvs [MEM_EL]) >>
  conj_asm1_tac
  >- (irule exp_eq_IMP_exp_eq_in_ctxt >> irule $ iffLR exp_eq_sym >> irule eval_IMP_exp_eq >>
      rw [Ntimes subst_def 2] >>
      rename1 ‘subst (f \\ _ )’ >> qspecl_then [‘f’, ‘Let v e e2’] assume_tac $ GSYM subst_fdomsub >>
      gvs [eval_thm, bind1_def, subst1_ignore, IMP_closed_subst, FRANGE_FLOOKUP]) >>
  irule exp_eq_in_ctxt_trans >> irule_at (Pos hd) $ iffLR exp_eq_in_ctxt_sym >>
  irule_at Any Let_Apps_in_ctxt >>
QED*)

Theorem find_soundness_lemma:
  ∀e c fdc ds e' fd. find e c fdc ds e' fd
    ⇒ (∀n l i. (n, l) ∈ fdc ∧ i < LENGTH l ∧ EL i l ⇒ (Var n) fdemands (([], i), LENGTH l, c))
    ⇒ exp_eq_in_ctxt c e e' ∧ (∀d. d ∈ ds ⇒ e demands (d, c))
      ∧ (∀argDs ds2.
           fd = SOME (argDs, ds2)
           ⇒ (∀i. i < LENGTH argDs ∧ EL i argDs ⇒ e' fdemands (([], i), LENGTH argDs, c))
             ∧ ∀d2. d2 ∈ ds2 ⇒  e' demands_when_applied (d2, LENGTH argDs, c))
(*           ∧ ∀eL d2. (LENGTH eL = LENGTH argDs ∧ d2 ∈ ds2) ⇒ (Apps e' eL) demands (d2, c))*)
Proof
  Induct_on ‘find’
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ gvs [exp_eq_in_ctxt_refl, demands_Var]
  >~[‘exp_eq_in_ctxt c e (Seq (Var v) e2)’] (* find_Seq *)
  >- (strip_tac
      \\ strip_tac
      \\ fs []
      \\ first_x_assum $ drule
      \\ strip_tac \\ conj_asm1_tac
      >- (dxrule_then assume_tac demands_empty_proj
          \\ fs [demands_def, Projs_def]
          \\ irule exp_eq_in_ctxt_trans
          \\ pop_assum $ irule_at Any
          \\ irule exp_eq_in_ctxt_Prim
          \\ fs [exp_eq_in_ctxt_refl])
      \\ rw []
      >- (first_x_assum $ drule_then assume_tac
          \\ gvs [fdemands_Seq])
      >- gvs [demands_when_applied_Seq])
  >~[‘exp_eq_in_ctxt c (Seq e e2) (Seq e' e2')’] (* find_Seq2 *)
  >- (rw []
      \\ gvs [exp_eq_in_ctxt_Prim, demands_Seq, demands_Seq2, fdemands_Seq,
             demands_when_applied_Seq])
  >~[‘exp_eq_in_ctxt c (If ec et ee) (If ec' et' ee')’]
  >- (rw [] \\ fs [exp_eq_in_ctxt_Prim, demands_If, demands_If2])
  >~[‘_ demands_when_applied (_, 0, _)’]
  >- (rw [] \\ gvs [demands_when_applied_0]
      \\ irule exp_eq_same_demands
      \\ metis_tac [exp_eq_in_ctxt_sym])
  >~[‘exp_eq_in_ctxt c (App f e) (App f' e')’] (* find_App *)
  >- (rw [] \\ fs [exp_eq_in_ctxt_App, demands_App])
  >>~[‘exp_eq_in_ctxt c (Apps e el') (Apps e' el'')’] (* find_Apps *)
  >- (rw []
      \\ fs [Apps_demands]
      \\ irule exp_eq_in_ctxt_Apps
      \\ fs [LIST_REL_EL_EQN] \\ rw []
      \\ rename1 ‘n < LENGTH _’
      \\ first_x_assum $ qspecl_then [‘n’] assume_tac
      \\ metis_tac [])
  >- (rw [] (* find_Apps_fd *)
      >- (irule exp_eq_in_ctxt_Apps
          \\ fs [LIST_REL_EL_EQN] \\ rw []
          \\ rename1 ‘n < LENGTH _’ \\ last_x_assum $ qspecl_then [‘n’] assume_tac
          \\ gvs [EL_ZIP])
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gvs [Apps_demands, LIST_REL_EL_EQN]
      \\ last_x_assum $ drule_then assume_tac
      \\ gvs [EL_ZIP]
      \\ rename1 ‘Apps _ _ demands (d, _)’ \\ PairCases_on ‘d’
      \\ once_rewrite_tac [GSYM needs_Var_is_demands]
      \\ irule needs_trans \\ irule_at (Pos hd) needs_exp_eq
      \\ irule_at Any exp_eq_in_ctxt_Apps
      \\ irule_at Any exp_eq_in_ctxt_l_refl
      \\ last_x_assum $ dxrule_then assume_tac \\ gvs []
      \\ dxrule_then assume_tac fdemands_alt \\ fs []
      \\ rpt $ first_x_assum $ irule_at Any
      \\ gvs [exp_eq_in_ctxt_sym, needs_Var_is_demands])
  >~[‘exp_eq_in_ctxt c (Proj n i e) (Proj n i e')’] (* find_Proj *)
  >- (strip_tac
      \\ fs [exp_eq_in_ctxt_Prim, demands_Proj])
  >~[‘exp_eq_in_ctxt c (IsEq n i e) (IsEq n i e')’] (* find_IsEq *)
  >- (rw []
      \\ fs [exp_eq_in_ctxt_Prim, demands_IsEq])
  >~[‘exp_eq_in_ctxt c (Prim (AtomOp op) el1) (Prim (AtomOp op) el2)’] (* find_Atom *)
  >- (rw []
      >- (irule exp_eq_in_ctxt_Prim
          \\ fs [LIST_REL_EL_EQN]
          \\ rw []
          \\ rename1 ‘n < LENGTH _’
          \\ first_x_assum $ qspecl_then [‘n’] assume_tac
          \\ gvs [EL_ZIP])
      \\ fs [LIST_REL_EL_EQN, MEM_EL]
      \\ rename1 ‘ds = EL n dsl’
      \\ first_x_assum $ qspecl_then [‘n’] assume_tac
      \\ irule demands_AtomOp
      \\ gvs [EL_ZIP, EXISTS_MEM]
      \\ first_x_assum $ irule_at Any
      \\ fs [EL_MEM])
  >>~[‘exp_eq_in_ctxt c (Prim ope el1) (Prim ope el2)’] (* find_Prim *)
  >- (rw []
      \\ irule exp_eq_in_ctxt_Prim
      \\ rw [LIST_REL_EL_EQN, EL_MAP]
      \\ rename1 ‘EL n _’
      \\ ‘n < LENGTH el1’ by fs []
      \\ first_x_assum drule
      \\ rw [])
  >- (rw [] (* find_Prim1 *)
      >- (irule exp_eq_in_ctxt_Prim
          \\ gvs [LIST_REL_EL_EQN, EL_MAP] \\ rw []
          \\ rename1 ‘EL n _’
          \\ ‘n < LENGTH el1’ by fs []
          \\ first_x_assum drule
          \\ rw [])
      \\ last_x_assum dxrule
      \\ rw []
      \\ Cases_on ‘el1’
      \\ fs [demands_Prim])
  >~[‘exp_eq_in_ctxt c (Prim ope el1) Fail’] (* find_Prim_Fail *)
  >- (rw []
      \\ fs [exp_eq_IMP_exp_eq_in_ctxt, not_well_written_is_fail])
  >>~[‘exp_eq_in_ctxt c (Let v e e2) (Let v e' e2')’] (* find_Let *)
  >- (rw [exp_eq_in_ctxt_def]
      \\ drule_then assume_tac fdemands_subset
      \\ ‘fdc' ⊆ fdc’
        by (gvs [SUBSET_DEF] \\ PairCases \\ gvs [])
      \\ first_x_assum $ dxrule_then assume_tac
      \\ dxrule_then assume_tac fdemands_set_Bind
      \\ ‘∀n l. (n, l) ∈ fdc' ⇒ n ≠ v’
        by (pop_assum kall_tac \\ pop_assum kall_tac
            \\ rw [] \\ first_x_assum $ dxrule_then assume_tac \\ gvs [])
      \\ first_x_assum $ dxrule_then assume_tac
      \\ pop_assum $ qspecl_then [‘e’] assume_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ last_x_assum $ dxrule_then assume_tac \\ fs [fdemands_def]
      >- (irule exp_eq_in_ctxt_trans \\ first_x_assum $ irule_at Any
          \\ gvs [exp_eq_in_ctxt_App, exp_eq_in_ctxt_refl])
      >~[‘Let _ _ _ demands (d, c)’]
      >- (PairCases_on ‘d’
          \\ irule demands_Let2
          \\ ‘d1 = v ∨ d1 ≠ v’ by fs []
          \\ gvs [])
      >~[‘Let _ _ _ fdemands _’]
      >- (irule fdemands_exp_eq
          \\ first_x_assum $ irule_at (Pos hd)
          \\ gvs [exp_eq_in_ctxt_refl, exp_eq_in_ctxt_App])
      \\ pop_assum $ drule_then assume_tac
      \\ rename1 ‘_ demands_when_applied (d2, _, _)’ \\ PairCases_on ‘d2’
      \\ gvs [demands_when_applied_def, eq_when_applied_def]
      \\ irule eq_when_applied_trans_exp_eq \\ irule_at Any exp_eq_in_ctxt_App
      \\ irule_at (Pos $ el 2) $ iffLR exp_eq_in_ctxt_sym
      \\ first_assum $ irule_at Any \\ irule_at Any exp_eq_in_ctxt_refl
      \\ irule eq_when_applied_trans \\ pop_assum $ irule_at Any
      \\ irule exp_eq_in_ctxt_IMP_eq_when_applied \\ irule exp_eq_in_ctxt_trans
      \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt \\ irule_at Any Let_Seq
      \\ irule exp_eq_in_ctxt_Prim \\ fs []
      \\ irule_at Any exp_eq_in_ctxt_App \\ fs [exp_eq_in_ctxt_refl]
      \\ irule exp_eq_IMP_exp_eq_in_ctxt \\ irule exp_eq_trans
      \\ irule_at Any Let_Projs \\ irule exp_eq_Projs_cong
      \\ irule Let_Var2
      \\ strip_tac \\ gvs [dest_fd_SND_def])
  >- (rw [exp_eq_in_ctxt_def]
      \\ drule_then assume_tac fdemands_subset
      \\ ‘fdc' ⊆ fdc’
        by (gvs [SUBSET_DEF] \\ PairCases \\ gvs [])
      \\ first_x_assum $ dxrule_then assume_tac
      \\ dxrule_then assume_tac fdemands_set_Bind
      \\ ‘∀n l. (n, l) ∈ fdc' ⇒ n ≠ v’
        by (pop_assum kall_tac \\ pop_assum kall_tac
            \\ rw [] \\ first_x_assum $ dxrule_then assume_tac \\ gvs [])
      \\ first_x_assum $ dxrule_then assume_tac
      \\ pop_assum $ qspecl_then [‘e’] assume_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ last_x_assum $ dxrule_then assume_tac \\ fs []
      >- (irule exp_eq_in_ctxt_trans
          \\ first_x_assum $ irule_at Any
          \\ fs [exp_eq_in_ctxt_App, exp_eq_in_ctxt_refl])
      >~[‘Let _ _ _ fdemands _’]
      >- (irule fdemands_exp_eq \\ fs [fdemands_def]
          \\ first_x_assum $ irule_at (Pos hd)
          \\ gvs [exp_eq_in_ctxt_refl, exp_eq_in_ctxt_App])
      >~[‘Let _ _ _ demands (d, c)’]
      >- (rename1 ‘_ demands (d, c)’ \\ PairCases_on ‘d’
          \\ last_x_assum $ dxrule_then assume_tac
          \\ fs [demands_Let2]
          \\ irule demands_Let1
          \\ first_x_assum $ drule_then assume_tac
          \\ dxrule_then assume_tac demands_empty_proj \\ fs [])
      \\ pop_assum $ drule_then assume_tac
      \\ rename1 ‘_ demands_when_applied (d2, _, _)’ \\ PairCases_on ‘d2’
      \\ gvs [demands_when_applied_def, eq_when_applied_def]
      \\ irule eq_when_applied_trans_exp_eq \\ irule_at Any exp_eq_in_ctxt_App
      \\ irule_at (Pos $ el 2) $ iffLR exp_eq_in_ctxt_sym
      \\ first_assum $ irule_at Any \\ irule_at Any exp_eq_in_ctxt_refl
      \\ irule eq_when_applied_trans \\ pop_assum $ irule_at Any
      \\ irule exp_eq_in_ctxt_IMP_eq_when_applied \\ irule exp_eq_in_ctxt_trans
      \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt \\ irule_at Any Let_Seq
      \\ irule exp_eq_in_ctxt_Prim \\ fs []
      \\ irule_at Any exp_eq_in_ctxt_App \\ fs [exp_eq_in_ctxt_refl]
      \\ irule exp_eq_IMP_exp_eq_in_ctxt \\ irule exp_eq_trans
      \\ irule_at Any Let_Projs \\ irule exp_eq_Projs_cong
      \\ irule Let_Var2
      \\ strip_tac \\ gvs [dest_fd_SND_def])
  >~[‘SOME (T::argD, ds3)’]
  >- (rw [] \\ gvs [exp_eq_in_ctxt_App, demands_App, fdemands_App, demands_when_applied_App]
      >- (irule fdemands_0_App_demands \\ last_assum $ irule_at Any \\ gvs []
          \\ irule_at Any exp_eq_same_demands
          \\ first_x_assum $ dxrule_then assume_tac
          \\ pop_assum $ irule_at Any \\ gvs [])
      \\ rw [GSYM Apps_def])
  >~[‘SOME (b::argD, ds3)’]
  >- (rw [] \\ gvs [exp_eq_in_ctxt_App, demands_App, fdemands_App, demands_when_applied_App])
  >~[‘SOME (bL, fd)’]
  >- (rw [] \\ gvs [SUBSET_DEF])
  >- (rw [] \\ dxrule_then (dxrule_then assume_tac) fdemands_subset (* find_Subset *)
      \\ gvs []
      \\ rename1 ‘e demands (d, c)’ \\ PairCases_on ‘d’
      \\ gvs []
      \\ first_x_assum $ drule_then assume_tac \\ fs []
      \\ first_x_assum $ drule_then assume_tac
      \\ drule demands_projs_reduce
      \\ fs [])
  >- (rw [] \\ dxrule_then assume_tac fdemands_set_IsFree  (* find_Lam *)
      \\ pop_assum $ dxrule_then assume_tac
      \\ last_x_assum $ dxrule_then assume_tac
      \\ gvs [exp_eq_in_ctxt_Lam])
  >- (rw [] \\ dxrule_then (dxrule_then assume_tac) fdemands_set_FOLDL_IsFree
      \\ gvs [exp_eq_in_ctxt_Lams])
  >- (rw [] \\ dxrule_then (dxrule_then assume_tac) fdemands_set_FOLDL_IsFree
      \\ gvs [exp_eq_in_ctxt_Lams, LIST_REL_EL_EQN]
      \\ irule Lams_fdemands
      \\ irule_at Any exp_eq_same_demands
      \\ last_x_assum $ irule_at Any \\ fs []
      \\ irule_at Any demands_empty_proj
      \\ rpt $ last_x_assum $ irule_at Any)
  >- (rw [] \\ dxrule_then (dxrule_then assume_tac) fdemands_set_RecBind
      \\ gvs [exp_eq_in_ctxt_def])
QED

Theorem find_soundness:
  find e Nil {} ds e' fd ⇒ e ≈ e'
Proof
  rw []
  \\ dxrule find_soundness_lemma
  \\ fs [exp_eq_in_ctxt_def]
QED

(*Datatype:
  demands_tree = DemandNode bool (((string # num) # demands_tree) list)
End

Definition dt_to_set_def:
  dt_to_set (DemandNode T []) ps v = {(ps,v)} ∧
  dt_to_set (DemandNode F []) ps v = {} ∧
  dt_to_set (DemandNode b ((p, dt)::tl)) ps v = (dt_to_set dt (ps ++ [p]) v) ∪ (dt_to_set (DemandNode b tl) ps v)
End

Definition merge_dt_def:
  merge_dt (DemandNode b1 f1) (DemandNode b2 []) = DemandNode (b1 ∨ b2) f1 ∧
  merge_dt (DemandNode b1 []) (DemandNode b2 f2) = DemandNode (b1 ∨ b2) f2 ∧
  merge_dt (DemandNode b1 ((id1,dt1)::tl1)) (DemandNode b2 ((id2,dt2)::tl2)) =
  if id1 = id2
  then
    case merge_dt (DemandNode b1 tl1) (DemandNode b2 tl2) of
    | DemandNode b3 tl3 => DemandNode b3 ((id1, merge_dt dt1 dt2)::tl3) (* id1 = id2 *)
  else
    if FST id1 < FST id2 ∨ (FST id1 = FST id2 ∧ SND id1 < SND id2)
    then
      case merge_dt (DemandNode b1 tl1) (DemandNode b2 ((id2,dt2)::tl2)) of
      | DemandNode b3 tl3 => DemandNode b3 ((id1, dt1)::tl3) (* id1 < id2 *)
    else
      case merge_dt (DemandNode b1 ((id1,dt1)::tl1)) (DemandNode b2 tl2) of
      | DemandNode b3 tl3 => DemandNode b3 ((id2, dt2)::tl3) (* id2 < id1 *)
End

Definition find_function_def:
  find_function (Var v) c = ((FEMPTY : (string |-> demands_tree)) |+ (v, DemandNode T []), Var v) ∧
  (find_function (If ce te ee) c =
   let (cd, ce') = find_function ce c in
     let (td, te') = find_function te c in
       let (ed, ee') = find_function ee c in
         (cd, If ce' te' ee')) ∧
  (find_function (Prim If _) c = (FEMPTY, Fail)) ∧
  (find_function (Proj s i e) c =
   let (d, e') = find_function e c in
     (d, Proj s i e')) ∧
  (find_function (Prim (Proj s i) _) c = (FEMPTY, Fail)) ∧
  (find_function (IsEq s i e) c =
   let (d, e') = find_function e c in
     (d, IsEq s i e')) ∧
  (find_function (Prim (IsEq s i) _) c = (FEMPTY, Fail)) ∧
  (find_function (Seq e1 e2) c =
   let (d1, e1') = find_function e1 c in
     let (d2, e2') = find_function e2 c in
       (d1, Seq e1' e2')) ∧
  (find_function (Prim Seq _) c = (FEMPTY, Fail)) ∧
  (find_function (Prim op l) c =
  (FEMPTY, Prim op (MAP (λe. SND (find_function e c)) l))) ∧
  (find_function (App (Lam v e2) e) c = let (d, e') = find_function e c in
                                          let (d2, e2') = find_function e2 (Bind v e c) in
                                           case FLOOKUP d2 v of
                                             | NONE => (d2, App (Lam v e2') e')
                                             | SOME s => (FMERGE merge_dt d (d2 \\ v), Let v e' (Seq (Var v) e2'))) ∧
  (find_function (App f e) c = let (d, f') = find_function f c in
                                 let (_, e') = find_function e c in
                                   (d, App f' e')) ∧
  find_function e c = ((FEMPTY, e) : (string |-> demands_tree) # exp)
Termination
  WF_REL_TAC ‘measure (exp_size o FST)’
  \\ rw [] \\ fs []
  \\ assume_tac exp_size_lemma
  \\ fs []
  \\ first_x_assum dxrule
  \\ fs []
End

Theorem exp_size_cmp_exp3_size:
  ∀l e. MEM e l ⇒ exp_size e < exp3_size l
Proof
  fs [exp_size_lemma]
QED

Definition demands_tree_size_def:
  demands_tree_size (DemandNode b []) = 1 ∧
  demands_tree_size (DemandNode b ((v,dt)::tl)) = 1 + demands_tree_size dt + demands_tree_size (DemandNode b tl)
End

Theorem dt_to_set_union:
  ∀l b p v. dt_to_set (DemandNode T l) p v = {(p, v)} ∪ dt_to_set (DemandNode b l) p v
Proof
  Induct
  \\ rw [dt_to_set_def]
  >- (rename1 ‘DemandNode b []’
      \\ Cases_on ‘b’
      \\ rw [dt_to_set_def])
  \\ rename1 ‘DemandNode b (hd::tl)’
  \\ Cases_on ‘hd’
  \\ rw [dt_to_set_def]
  \\ metis_tac [UNION_COMM, UNION_ASSOC]
QED

Theorem merge_dt_is_set_union:
  ∀dt1 dt2 p v. dt_to_set (merge_dt dt1 dt2) p v = (dt_to_set dt1 p v) ∪ (dt_to_set dt2 p v)
Proof
  Induct using demands_tree_size_ind
  >- (Cases
      \\ Cases
      \\ rename1 ‘DemandNode b2 l’
      \\ Cases_on ‘b2’
      \\ Cases_on ‘l’
      \\ rw [merge_dt_def, dt_to_set_def]
      \\ fs [dt_to_set_union])
  \\ Induct using demands_tree_size_ind
  >- (rpt gen_tac
      \\ rename1 ‘DemandNode b2 []’
      \\ Cases_on ‘b2’
      \\ rw [dt_to_set_def, merge_dt_def]
      \\ metis_tac [dt_to_set_union, UNION_COMM, UNION_ASSOC])
  \\ rpt gen_tac
  \\ rename1 ‘merge_dt (DemandNode b1 ((v1,dt1)::tl1)) (DemandNode b2 ((v2,dt2)::tl2))’
  \\ rw [merge_dt_def]
  >- (qabbrev_tac ‘dt3 = merge_dt (DemandNode b1 tl1) (DemandNode b2 tl2)’
      \\ Cases_on ‘dt3’
      \\ rw [dt_to_set_def]
      \\ unabbrev_all_tac
      \\ metis_tac [UNION_COMM, UNION_ASSOC])
  >- (qabbrev_tac ‘dt3 = merge_dt (DemandNode b1 tl1) (DemandNode b2 ((v2,dt2)::tl2))’
      \\ Cases_on ‘dt3’
      \\ rw [dt_to_set_def]
      \\ unabbrev_all_tac
      \\ metis_tac [UNION_COMM, UNION_ASSOC, dt_to_set_def])
  >- (qabbrev_tac ‘dt3 = merge_dt (DemandNode b1 tl1) (DemandNode b2 ((v2,dt2)::tl2))’
      \\ Cases_on ‘dt3’
      \\ rw [dt_to_set_def]
      \\ unabbrev_all_tac
      \\ metis_tac [UNION_COMM, UNION_ASSOC, dt_to_set_def])
  \\ qabbrev_tac ‘dt3 = merge_dt (DemandNode b1 ((v1, dt1)::tl1)) (DemandNode b2 tl2)’
  \\ Cases_on ‘dt3’
  \\ rw [dt_to_set_def]
  \\ unabbrev_all_tac
  \\ metis_tac [UNION_COMM, UNION_ASSOC]
QED

Theorem find_function_soundness_lemma:
  ∀ e c d e' b.
    find_function e c = (d, e') ⇒
    ∃ds. find e c ds e' ∧
         (∀s ps. (ps, s) ∈ ds ⇒ ∃dt. FLOOKUP d s = SOME dt ∧ (ps, s) ∈ dt_to_set dt [] s) ∧
         (∀s. s ∈ FDOM d ⇒ ∃ps. (ps, s) ∈ ds)
Proof
  completeInduct_on ‘exp_size e’
  \\ rename1 ‘k = exp_size _’
  \\ gen_tac \\ Cases_on ‘e’
  \\ fs [exp_size_def]
  >- (rw [find_function_def] (* Var v *)
      \\ rename1 ‘(v, DemandNode T [])’
      \\ qexists_tac ‘{([], v)}’
      \\ fs [find_Var]
      \\ qexists_tac ‘DemandNode T []’
      \\ rw [dt_to_set_def, FLOOKUP_UPDATE])
  >- (rw [] (* Prim op l *)
      \\ rename1 ‘Prim op es’
      \\ Cases_on ‘es’
      >- (Cases_on ‘op’ (* Prim op [] *)
          \\ fs [find_function_def]
          \\ qexists_tac ‘{}’
          \\ fs [find_Bottom]
          \\ irule find_Prim_Fail
          \\ fs [well_written_def])
      \\ rename1 ‘h::t’
      \\ Cases_on ‘op’ >~[‘Prim (Cons s) (h::tl)’]
      >- (fs [find_function_def]
          \\ qabbrev_tac ‘es = h::tl’
          \\ qexists_tac ‘{}’
          \\ fs []
          \\ rw []
          \\ irule find_Prim
          \\ rw [] >~[‘LENGTH _ = _’] >- (unabbrev_all_tac \\ fs [])
          \\ rename1 ‘EL k' es’
          \\ ‘exp_size (EL k' es) < exp3_size es + (op_size (Cons s) + 1)’ by
            (‘exp_size (EL k' es) < exp3_size es’ by
               (irule exp_size_cmp_exp3_size
                \\ fs [MEM_EL]
                \\ qexists_tac ‘k'’
                \\ fs []
                \\ unabbrev_all_tac
                \\ fs [])
             \\ fs [])
          \\ first_x_assum dxrule
          \\ rw []
          \\ ‘exp_size (EL k' es) = exp_size (EL k' es)’ by fs []
          \\ first_x_assum dxrule
          \\ qabbrev_tac ‘de = find_function (EL k' es) c’
          \\ PairCases_on ‘de’
          \\ rw []
          \\ ‘de1 = EL k' (MAP (λe. SND (find_function e c)) es)’ by
            fs [EL_MAP]
          \\ fs[]
          \\ unabbrev_all_tac
          \\ fs []
          \\ first_x_assum drule
          \\ rw []
          \\ first_x_assum $ irule_at Any)
      >- (Cases_on ‘t’
          >- (fs [find_function_def] (* Prim If [e] *)
              \\ qexists_tac ‘{}’
              \\ fs []
              \\ rw []
              \\ fs [find_Prim_Fail, well_written_def])
          \\ rename1 ‘h::h1::t’
          \\ Cases_on ‘t’
          >- (fs [find_function_def] (* Prim If [e, e'] *)
              \\ qexists_tac ‘{}’
              \\ rw []
              \\ fs [find_Prim_Fail, well_written_def])
          \\ rename1 ‘ce::te::ee::t’
          \\ Cases_on ‘t’
          >- (fs [find_function_def] (* If _ _ _ *)
              \\ qabbrev_tac ‘ce' = find_function ce c’ \\ PairCases_on ‘ce'’
              \\ qabbrev_tac ‘te' = find_function te c’ \\ PairCases_on ‘te'’
              \\ qabbrev_tac ‘ee' = find_function ee c’ \\ PairCases_on ‘ee'’
              \\ fs []
              \\ first_assum $ qspecl_then [‘exp_size ce’] assume_tac
              \\ first_assum $ qspecl_then [‘exp_size te’] assume_tac
              \\ first_assum $ qspecl_then [‘exp_size ee’] assume_tac
              \\ fs [exp_size_def]
              \\ last_x_assum $ qspecl_then [‘ce’] assume_tac
              \\ last_x_assum $ qspecl_then [‘te’] assume_tac
              \\ last_x_assum $ qspecl_then [‘ee’] assume_tac
              \\ fs []
              \\ first_x_assum dxrule
              \\ first_x_assum dxrule
              \\ first_x_assum dxrule
              \\ rw []
              \\ qexists_tac ‘ds’
              \\ fs []
              \\ irule find_Subset
              \\ irule_at Any find_If
              \\ first_x_assum $ irule_at Any
              \\ first_x_assum $ irule_at Any
              \\ first_x_assum $ irule_at Any
              \\ rw []
              \\ qexists_tac ‘[]’
              \\ fs [])
          \\ fs [find_function_def]
          \\ qexists_tac ‘{}’
          \\ rw []
          \\ fs [find_Prim_Fail, well_written_def])
      >- (Cases_on ‘t’ (* IsEq *)
          \\ fs [find_function_def]
          >- (qabbrev_tac ‘ff = find_function h c’
              \\ PairCases_on ‘ff’
              \\ first_x_assum $ qspecl_then [‘exp_size h’] assume_tac
              \\ fs [exp_size_def]
              \\ pop_assum $ qspecl_then [‘h’] assume_tac
              \\ fs []
              \\ pop_assum dxrule
              \\ rw []
              \\ irule_at Any find_IsEq
              \\ first_x_assum $ irule_at Any
              \\ fs [])
          \\ qexists_tac ‘{}’
          \\ fs [find_Prim_Fail, well_written_def])
      >- (Cases_on ‘t’ (* Proj *)
          \\ fs [find_function_def]
          >- (qabbrev_tac ‘ff = find_function h c’
              \\ PairCases_on ‘ff’
              \\ first_x_assum $ qspecl_then [‘exp_size h’] assume_tac
              \\ fs [exp_size_def]
              \\ pop_assum $ qspecl_then [‘h’] assume_tac
              \\ fs []
              \\ pop_assum dxrule
              \\ rw []
              \\ irule_at Any find_Proj
              \\ first_x_assum $ irule_at Any
              \\ fs [])
          \\ qexists_tac ‘{}’
          \\ fs [find_Prim_Fail, well_written_def])
      >- (qabbrev_tac ‘l = h::t’ (* AtomOp *)
          \\ qexists_tac ‘{}’
          \\ fs [find_function_def]
          \\ rw []
          \\ irule find_Prim
          \\ rw []
          \\ rename1 ‘n < LENGTH l’
          \\ ‘exp_size (EL n l) < exp3_size l + (op_size (AtomOp a) + 1)’ by
            ( ‘exp_size (EL n l) < exp3_size l’ by fs [exp_size_cmp_exp3_size, EL_MEM]
              \\ fs [])
          \\ first_x_assum $ qspecl_then [‘exp_size (EL n l)’] assume_tac
          \\ pop_assum $ dxrule_then assume_tac
          \\ pop_assum $ qspecl_then [‘EL n l’] assume_tac
          \\ fs []
          \\ qabbrev_tac ‘p = find_function (EL n l) c’
          \\ PairCases_on ‘p’
          \\ fs []
          \\ rw [EL_MAP]
          \\ first_x_assum dxrule
          \\ rw []
          \\ first_x_assum $ irule_at Any)
      >- (Cases_on ‘t’ (* Seq *)
          >- (fs [find_function_def]
              \\ qexists_tac ‘{}’
              \\ fs [find_Prim_Fail, well_written_def])
          \\ rename1 ‘h0::h1::tl’
          \\ Cases_on ‘tl’
          >- (first_assum $ qspecl_then [‘exp_size h0’] assume_tac
              \\ first_x_assum $ qspecl_then [‘exp_size h1’] assume_tac
              \\ fs [exp_size_def]
              \\ first_x_assum $ qspecl_then [‘h1’] assume_tac
              \\ first_x_assum $ qspecl_then [‘h0’] assume_tac
              \\ fs []
              \\ fs [find_function_def]
              \\ qabbrev_tac ‘f1 = find_function h1 c’
              \\ PairCases_on ‘f1’
              \\ qabbrev_tac ‘f0 = find_function h0 c’
              \\ PairCases_on ‘f0’
              \\ fs []
              \\ first_x_assum dxrule
              \\ first_x_assum dxrule
              \\ rw []
              \\ irule_at Any find_Subset
              \\ irule_at Any find_Seq2
              \\ first_x_assum $ irule_at Any
              \\ first_x_assum $ irule_at Any
              \\ qexists_tac ‘ds'’
              \\ rw []
              \\ fs []
              \\ qexists_tac ‘[]’
              \\ fs [])
          \\ fs [find_function_def]
          \\ qexists_tac ‘{}’
          \\ fs [find_Prim_Fail, well_written_def]))
  >- (rw [] (* App *)
      \\ rename1 ‘App f e’
      \\ first_assum $ qspecl_then [‘exp_size f’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘f’] assume_tac
      \\ qabbrev_tac ‘e1p = find_function f c’
      \\ PairCases_on ‘e1p’
      \\ fs []
      \\ first_x_assum drule
      \\ strip_tac
      \\ Cases_on ‘f’ >~[‘Let s e e2’]
      >- (
       first_assum $ qspecl_then [‘exp_size e’] assume_tac
       \\ first_x_assum $ qspecl_then [‘exp_size e2’] assume_tac
       \\ fs [exp_size_def, find_function_def]
       \\ qabbrev_tac ‘ep = find_function e c’
       \\ PairCases_on ‘ep’
       \\ qabbrev_tac ‘e2p = find_function e2 (Bind s e c)’
       \\ PairCases_on ‘e2p’
       \\ last_x_assum $ qspecl_then [‘e’] assume_tac
       \\ last_x_assum $ qspecl_then [‘e2’] assume_tac
       \\ fs []
       \\ first_x_assum dxrule
       \\ first_x_assum dxrule
       \\ rw []
       \\ rename1 ‘find e2 _ ds2 _’
       \\ rename1 ‘find e _ ds1 _’
       \\ ‘s ∈ FDOM e2p0 ∨ s ∉ FDOM e2p0’ by fs []
       \\ fs [FLOOKUP_DEF]
       \\ rw []
       >- (
         irule_at Any find_Let2
         \\ first_x_assum $ irule_at Any
         \\ irule_at Any find_Seq
         \\ first_x_assum $ irule_at Any
         \\ first_assum $ dxrule
         \\ rw []
         \\ first_assum $ irule_at Any
         \\ first_x_assum $ irule_at Any
         \\ ‘∃ds'''. ∀ps v. (ps, v) ∈ ds''' ⇔ ((ps, v) ∈ ds2 ∧ v ≠ s) ∨ (ps, v) ∈ ds1’ by
            (qexists_tac ‘ds1 ∪ BIGUNION (IMAGE (λ(ps,v). if v = s then {} else {(ps,v)}) ds2)’
             \\ rw []
             \\ eq_tac
             \\ rw []
             \\ fs []
             >- (rename1 ‘p ∈ ds2’
                 \\ PairCases_on ‘p’
                 \\ fs []
                 \\ ‘p1 = s ∨ p1 ≠ s’ by fs []
                 \\ fs [])
             \\ rw [DISJ_EQ_IMP]
             \\ qexists_tac ‘{(ps, v)}’
             \\ fs []
             \\ first_x_assum $ irule_at Any
             \\ fs [])
         \\ qexists_tac ‘ds'''’
         \\ fs []
         \\ rw []
         \\ first_x_assum dxrule
         \\ fs []
         >- (rw [FMERGE_DEF]
             >- (qsuff_tac ‘FLOOKUP (e2p0 \\ s) s' = FLOOKUP e2p0 s'’
                 >- rw [FLOOKUP_DEF]
                 \\ fs [DOMSUB_FLOOKUP_NEQ])
             \\ fs [merge_dt_is_set_union]
             \\ qsuff_tac ‘FLOOKUP (e2p0 \\ s) s' = FLOOKUP e2p0 s'’
             >- rw [FLOOKUP_DEF]
             \\ fs [DOMSUB_FLOOKUP_NEQ])
         >- rw [FMERGE_DEF, merge_dt_is_set_union]
         >- (rw []
             \\ qexists_tac ‘ps’
             \\ fs [])
         \\ rw []
         \\ qexists_tac ‘ps’
         \\ fs [])
       \\ irule_at Any find_Let
       \\ last_x_assum $ irule_at Any
       \\ last_x_assum $ irule_at Any
       \\ fs []
       \\ rw []
       >- (strip_tac
           \\ first_x_assum dxrule
           \\ fs [])
       \\ first_assum drule
       \\ fs [])
      \\ fs [find_function_def]
      \\ last_x_assum $ qspecl_then [‘exp_size e’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘e’] assume_tac
      \\ fs []
      \\ qabbrev_tac ‘ep = find_function e c’
      \\ PairCases_on ‘ep’
      \\ fs []
      \\ first_x_assum dxrule
      \\ rw []
      \\ irule_at Any find_App
      \\ first_assum $ irule_at Any >~[‘Var s’]
      >- (irule_at Any find_Var
          \\ qexists_tac ‘[]’
          \\ fs []
          \\ rw [FLOOKUP_UPDATE, dt_to_set_def])
      \\ first_assum $ irule_at Any
      \\ fs [])
  >- (rw [find_function_def] (* Lam *)
      \\ irule_at Any find_Bottom
      \\ fs [])
  >- (rw [find_function_def] (* Letrec *)
      \\ irule_at Any find_Bottom
      \\ fs [find_Bottom])
QED


Definition demand_analysis_def:
  demand_analysis = SND o (λe. find_function e Nil)
End

Theorem demand_analysis_soundness:
  ∀e. is_closed e ⇒ e ≈ demand_analysis e
Proof
  rw [demand_analysis_def]
  \\ qabbrev_tac ‘p = find_function e Nil’
  \\ PairCases_on ‘p’
  \\ fs []
  \\ irule find_soundness
  \\ drule find_function_soundness_lemma
  \\ rw []
  \\ first_assum $ irule_at Any
QED*)

(*
  let foo = lam (a + 2) in
    lam x (foo x)
-->
  let foo = lam a (seq a (a + 2)) in
    lam x (foo x)
-->
  let foo = lam a (seq a (a + 2)) in
    lam x (seq x (foo x))

  Letrec [(f,x)] rest
*)

val _ = export_theory();

(*
  Formalize the notion of context and a new relation coming with it
*)

open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory dep_rewrite
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_miscTheory pure_exp_relTheory pure_congruenceTheory;
open  pure_alpha_equivTheory;

val _ = new_theory "pure_exp_eq_in_ctxt";

(* Preliminaries *)

Theorem exp_eq_l_refl:
  ∀b l. LIST_REL (λx y. (x ≅? y) b) l l
Proof
  gen_tac
  \\ Induct
  \\ fs [exp_eq_refl]
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

Theorem Letrec_closed:
  ∀l e b. closed e ⇒ (Letrec l e ≅? e) b
Proof
  rw [exp_eq_def, bind_def] >> IF_CASES_TAC >>
  gvs [app_bisimilarity_eq, exp_eq_refl] >>
  irule_at (Pos $ el 2) IMP_closed_subst >>
  gvs [subst_def, closed_subst, FRANGE_FLOOKUP] >>
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
  rw [exp_eq_refl]
QED

Theorem Let_Letrec:
  ∀s l e1 e2 b. EVERY (λe. s ∉ freevars e) (MAP SND l) ∧ ¬MEM s (MAP FST l) ∧ closed e1
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
  gvs [exp_eq_refl, Letrec_closed]
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

(* Part on context *)

Datatype:
  ctxt = Nil
       | IsFree string ctxt
       | Bind string exp ctxt
       | RecBind ((string # exp) list) ctxt
End

Definition exp_eq_in_ctxt_def:
  exp_eq_in_ctxt Nil = (λe1 e2. e1 ≈ e2) ∧
  exp_eq_in_ctxt (IsFree s c) e1 e2 = (∀e3. closed e3 ⇒ exp_eq_in_ctxt c (Let s e3 e1) (Let s e3 e2)) ∧
  exp_eq_in_ctxt (Bind s e3 c) e1 e2 = exp_eq_in_ctxt c (Let s e3 e1) (Let s e3 e2) ∧
  exp_eq_in_ctxt (RecBind l c) e1 e2 = exp_eq_in_ctxt c (Letrec l e1) (Letrec l e2)
End

Definition ctxt_size_def:
  ctxt_size Nil = 0n ∧
  ctxt_size (IsFree s ctxt) = 1 + ctxt_size ctxt ∧
  ctxt_size (Bind s e ctxt) = 1 + list_size char_size s +  exp_size e + ctxt_size ctxt ∧
  ctxt_size (RecBind sel ctxt) = 1 + exp1_size sel + ctxt_size ctxt
End


Theorem exp_eq_in_ctxt_refl:
  ∀c e. exp_eq_in_ctxt c e e
Proof
  Induct
  \\ gvs [exp_eq_in_ctxt_def, exp_eq_refl]
QED

Theorem exp_eq_in_ctxt_sym:
  ∀c e1 e2. exp_eq_in_ctxt c e1 e2 ⇔ exp_eq_in_ctxt c e2 e1
Proof
  Induct
  \\ rw [] \\ eq_tac
  \\ gvs [exp_eq_in_ctxt_def, exp_eq_sym]
QED

Theorem exp_eq_in_ctxt_trans:
  ∀c e1 e2 e3. exp_eq_in_ctxt c e1 e2 ∧ exp_eq_in_ctxt c e2 e3 ⇒ exp_eq_in_ctxt c e1 e3
Proof
  Induct
  \\ rw []
  \\ gvs [exp_eq_in_ctxt_def]
  >- (irule exp_eq_trans
      \\ pop_assum $ irule_at Any \\ fs [])
  \\ rw []
  \\ last_x_assum irule
  \\ first_x_assum $ irule_at Any
  \\ gvs []
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

Theorem exp_eq_in_ctxt_Prim:
  ∀c eL eL' ope. LIST_REL (exp_eq_in_ctxt c) eL eL' ⇒ exp_eq_in_ctxt c (Prim ope eL) (Prim ope eL')
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

Theorem exp_eq_in_ctxt_App:
  ∀c f1 f2 e1 e2. exp_eq_in_ctxt c f1 f2 ∧ exp_eq_in_ctxt c e1 e2
                  ⇒ exp_eq_in_ctxt c (App f1 e1) (App f2 e2)
Proof
  Induct
  \\ gvs [exp_eq_in_ctxt_def,exp_eq_App_cong]
  \\ rw []
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at Any exp_eq_in_ctxt_trans
  \\ last_x_assum $ irule_at (Pos $ el 2)
  \\ first_x_assum $ irule_at (Pos $ el 2)
  \\ rpt $ last_assum $ irule_at Any
  \\ gvs [exp_eq_IMP_exp_eq_in_ctxt, Let_App, Letrec_App, exp_eq_sym]
QED

Theorem exp_eq_in_ctxt_Apps:
  ∀eL eL' e e' c. LIST_REL (exp_eq_in_ctxt c) eL eL' ⇒ exp_eq_in_ctxt c e e'
                  ⇒ exp_eq_in_ctxt c (Apps e eL) (Apps e' eL')
Proof
  Induct
  >- (Cases
      \\ fs [Apps_def])
  \\ gen_tac
  \\ Cases
  \\ rw [Apps_def]
  \\ first_x_assum irule
  \\ fs [exp_eq_in_ctxt_App]
QED

Theorem Let_App_in_ctxt:
  ∀c s e1 e2 e3. exp_eq_in_ctxt c (Let s e1 (App e2 e3)) (App (Let s e1 e2) (Let s e1 e3))
Proof
  rpt gen_tac
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ gvs [Let_App]
QED

Theorem Let_freevars:
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

Theorem Let_Let_in_ctxt:
  ∀v w e1 e2 e3 c. v ≠ w ∧ v ∉ freevars e2 ∧ w ∉ freevars e1 ⇒
                   exp_eq_in_ctxt c (Let v e1 (Let w e2 e3)) (Let w e2 (Let v e1 e3))
Proof
  rw []
  \\ irule exp_eq_IMP_exp_eq_in_ctxt
  \\ gvs [Let_Let]
QED

Theorem exp_eq_in_ctxt_Lam:
  ∀c s e1 e2. exp_eq_in_ctxt (IsFree s c) e1 e2
              ⇒ exp_eq_in_ctxt c (Lam s e1) (Lam s e2)
Proof
  Induct
  \\ fs[exp_eq_in_ctxt_def] \\ rw [exp_eq_in_ctxt_def]
  >- (rw [exp_eq_Lam_strong]
      \\ first_x_assum $ drule_then assume_tac
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
      \\ irule exp_eq_in_ctxt_trans
      \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any exp_eq_l_refl
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ fs []
      \\ first_assum $ irule_at Any \\ fs []
      \\ irule exp_eq_in_ctxt_trans
      \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
      \\ irule_at Any Letrec_Lam_weak
      \\ conj_tac
      >- (rw [EVERY_MEM]
          \\ rename1 ‘MEM e _’ \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
          \\ fs [MEM_MAP]
          \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
          \\ rw [])
      \\ fs []
      \\ irule exp_eq_in_ctxt_trans
      \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ irule_at Any exp_eq_l_refl
      \\ first_assum $ irule_at Any \\ fs []
      \\ irule exp_eq_in_ctxt_trans
      \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any Letrec_Lam_weak
      \\ fs []
      \\ conj_tac
      >- (rw [EVERY_MEM]
          \\ rename1 ‘MEM e _’ \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
          \\ fs [MEM_MAP]
          \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
          \\ rw [])
      \\ last_x_assum irule
      \\ rw []
      \\ irule exp_eq_in_ctxt_trans
      \\ irule_at Any exp_eq_in_ctxt_trans
      \\ last_x_assum $ irule_at Any
      \\ first_assum $ irule_at Any
      \\ irule_at (Pos last) $ iffLR exp_eq_in_ctxt_sym
      \\ conj_tac
      \\ irule exp_eq_IMP_exp_eq_in_ctxt
      \\ irule exp_eq_trans
      \\ irule_at Any Let_Letrec
      \\ fs []
      \\ irule_at Any exp_eq_Letrec_cong
      \\ irule_at Any $ iffLR exp_eq_sym
      \\ irule_at Any exp_eq_App_cong
      \\ irule_at Any exp_alpha_exp_eq
      \\ irule_at Any exp_alpha_Alpha
      \\ rw [EVERY_MEM, exp_eq_refl, exp_eq_l_refl]
      \\ rename1 ‘MEM e _’
      \\ last_x_assum $ qspecl_then [‘freevars e’] assume_tac
      \\ fs [MEM_MAP]
      \\ rename1 ‘e = SND pair’ \\ pop_assum $ qspecl_then [‘pair’] assume_tac
      \\ rw [])
  \\ rename1 ‘Let v e3 (Lam w _)’
  \\ ‘∃s. s ∉ {v} ∪ {w} ∪ freevars e3 ∪ freevars e1 ∪ freevars e2’
    by (‘INFINITE 𝕌(:string)’ by simp []
        \\ gvs [NOT_IN_FINITE])
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any exp_eq_App_cong \\ irule_at Any exp_eq_Lam_cong
  \\ irule_at Any exp_alpha_exp_eq
  \\ irule_at Any exp_alpha_Alpha
  \\ fs [] \\ first_assum $ irule_at Any
  \\ irule_at Any exp_eq_refl \\ fs []
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos hd) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any Let_Lam_weak \\ fs []
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ irule_at Any exp_eq_App_cong \\ irule_at Any exp_eq_Lam_cong
  \\ irule_at Any exp_alpha_exp_eq
  \\ irule_at Any exp_alpha_Alpha
  \\ first_assum $ irule_at Any
  \\ irule_at Any exp_eq_refl \\ fs []
  \\ irule exp_eq_in_ctxt_trans
  \\ irule_at (Pos last) exp_eq_IMP_exp_eq_in_ctxt
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ irule_at Any Let_Lam_weak \\ fs []
  \\ last_x_assum $ irule_at Any
  \\ rw []
  \\ irule exp_eq_in_ctxt_trans \\ irule_at Any exp_eq_in_ctxt_trans
  \\ last_x_assum $ irule_at Any
  \\ first_assum $ irule_at (Pos hd)
  \\ rpt $ irule_at Any exp_eq_IMP_exp_eq_in_ctxt
  \\ TRY $ last_assum $ irule_at Any
  \\ irule_at (Pos last) $ iffLR exp_eq_sym
  \\ conj_tac
  \\ irule exp_eq_trans
  \\ irule_at (Pos last) Let_Let
  \\ gvs [closed_def]
  \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
  \\ irule exp_eq_Lam_cong
  \\ irule exp_eq_App_cong \\ fs [exp_eq_refl]
  \\ irule exp_alpha_exp_eq
  \\ irule exp_alpha_Alpha
  \\ fs []
QED

Theorem exp_eq_in_ctxt_Lams:
  ∀vl c e e'. exp_eq_in_ctxt (FOLDL (λc n. IsFree n c) c vl) e e' ⇒
              exp_eq_in_ctxt c (Lams vl e) (Lams vl e')
Proof
  Induct
  \\ rw [Lams_def]
  \\ irule exp_eq_in_ctxt_Lam
  \\ last_x_assum $ irule_at Any
  \\ fs []
QED

val _ = export_theory();

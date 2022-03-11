(*
   Formalises the notion of "demand" as used in demand/strictness analysis.
*)

open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory dep_rewrite
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_miscTheory pure_exp_relTheory pure_congruenceTheory;

val _ = new_theory "pure_demand";

Definition Projs_def:
  Projs [] e = e ∧
  Projs ((x,i)::ps) e = Projs ps (Proj x i e)
End

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

Theorem Seq_App:
  ∀b. (App (Seq p f) e ≅? Seq p (App f e)) b
Proof
  irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_App, eval_wh_Seq]
  \\ fs []
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

Theorem exp_eq_l_refl:
  ∀b l. LIST_REL (λx y. (x ≅? y) b) l l
Proof
  gen_tac
  \\ Induct
  \\ fs [exp_eq_refl]
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
  (e demands (p,v)) = (e ≈ Seq (Projs p (Var v)) e)
End

val _ = set_fixity "needs" (Infixl 480);
Definition needs_def:
  (e needs (ps, e')) = (e ≈ Seq (Projs ps e') e)
End

Theorem needs_Var_is_demands:
  e needs (ps, Var v) ⇔ e demands (ps, v)
Proof
  rw [needs_def, demands_def] \\ fs []
QED

Theorem needs_refl:
  ∀e. e needs ([],e)
Proof
  rw [needs_def, Projs_def]
  \\ metis_tac [Seq_id, exp_eq_sym]
QED

Theorem needs_Var:
  (Var v) needs ([], Var v)
Proof
  fs [needs_refl]
QED

Theorem needs_Proj:
  e needs d ⇒ (Proj n i e) needs d
Proof
  PairCases_on ‘d’
  \\ rename1 ‘(ps, e')’
  \\ rw [needs_def, Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq e (Proj n i e)’
  \\ conj_tac >- fs [Proj_Seq]
  \\ qabbrev_tac ‘p = Projs ps e'’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq p e) (Proj n i e)’
  \\ conj_tac
  >- (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq p (Seq e (Proj n i e))’
  \\ conj_tac >- fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl, Let_Var]
  \\ metis_tac [Proj_Seq, exp_eq_sym]
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
  e needs (ps,e') ∧ e' needs (ps',e'') ⇒ e needs (ps',e'')
Proof
  rw [needs_def]
  \\ irule exp_eq_trans
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq (Projs ps' e'') (Projs ps e')) e’
  \\ conj_tac >-
   (irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
    \\ assume_tac needs_Projs \\ metis_tac [needs_def])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Projs ps' e'') (Seq (Projs ps e') e)’
  \\ conj_tac >- fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong
  \\ fs [exp_eq_refl, exp_eq_sym]
QED

Theorem needs_Projs_Var:
  (Proj s i (Var v)) needs ([(s,i)], Var v)
Proof
  rw [needs_def, Projs_def]
  \\ metis_tac [Seq_id, exp_eq_sym]
QED

Theorem needs_Seq:
  e needs d ⇒ (Seq e e') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq (Projs d0 d1) e) e'’
  \\ conj_tac >-
   (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ fs [Seq_assoc]
QED


Theorem needs_Seq2:
  e' needs d ⇒ (Seq e e') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq e (Seq (Projs d0 d1) e')’
  \\ fs [exp_eq_Prim_cong, exp_eq_refl]
  \\ irule exp_eq_trans
  \\ irule_at Any Seq_assoc
  \\ irule exp_eq_trans
  \\ irule_at Any Seq_comm
  \\ metis_tac [Seq_assoc, exp_eq_sym]
QED

Theorem needs_Let1:
  e needs d ∧ e' demands ([],w) ⇒ (Let w e e') needs d
Proof
  PairCases_on ‘d’
  \\ rw [demands_def,needs_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qabbrev_tac ‘p = (Projs d0 d1)’
  \\ qexists_tac ‘Let w e (Seq (Var w) e')’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w e (Var w)) (Let w e e')’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq e (Let w e e')’
  \\ conj_tac
  THEN1 (irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Seq p e) (Let w e e')’
  \\ conj_tac THEN1
   (irule exp_eq_Prim_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq p (Seq e (Let w e e'))’
  \\ conj_tac THEN1 fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
  \\ once_rewrite_tac [exp_eq_sym]
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_App_cong
  \\ irule_at Any exp_eq_Lam_cong
  \\ irule_at (Pos $ el 2) exp_eq_refl
  \\ first_x_assum $ irule_at Any
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_Prim_cong
  \\ fs [exp_eq_refl, Let_Var]
QED

Theorem needs_Let_Cons: (* expects program to be in ANF *)
  e demands ((s,LENGTH xs)::ps,w) ⇒
  (Let w (Cons s (xs ++ e'::ys)) e) needs (ps,e')
Proof
  rw [demands_def,needs_def,Projs_def]
  \\ qabbrev_tac ‘cons = (Cons s (xs ++ e'::ys))’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w cons (Seq (Projs ps (Proj s (LENGTH xs) (Var w))) e)’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ fs [GSYM Projs_def]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Projs
  \\ fs [Projs_def]
  \\ irule exp_eq_Projs_cong \\ fs [exp_eq_refl,Let_Var]
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_Prim_cong \\ fs [PULL_EXISTS]
  \\ irule_at Any Let_Var
  \\ unabbrev_all_tac
  \\ fs [Proj_Cons]
QED

Theorem needs_Let_Proj: (* expects program to be in ANF *)
  e demands (ps,w) ⇒
  (Let w (Proj s i e') e) needs ((s,i)::ps,e')
Proof
  rw [demands_def,needs_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w (Proj s i e') (Seq (Projs ps (Var w)) e)’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w (Proj s i e') (Projs ps (Var w)))
                      (Let w (Proj s i e') e)’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ps (Let w (Proj s i e') (Var w))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var]
QED

Theorem needs_App:
  f needs d ⇒ (App f e) needs d
Proof
  PairCases_on ‘d’ \\ rename1 ‘(ps,e')’
  \\ rw [needs_def]
  \\ qabbrev_tac ‘proj = Projs ps e'’
  \\ irule exp_eq_trans
  \\ qexists_tac ‘App (Seq proj f) e’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ rw [exp_eq_refl])
  \\ fs [Seq_App]
QED

Theorem needs_If:
  e needs d ⇒ (If e e' e'') needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ qabbrev_tac ‘p = Projs d0 d1’
  \\ irule exp_eq_trans
  \\ irule_at Any If_Seq
  \\ irule exp_eq_Prim_cong
  \\ fs [exp_eq_refl, exp_eq_sym]
QED

Theorem needs_If2:
  et needs d ∧ ee needs d ⇒ (If ec et ee) needs d
Proof
  PairCases_on ‘d’
  \\ rw [needs_def]
  \\ irule exp_eq_trans
  \\ irule_at Any If_Seq2
  \\ irule exp_eq_Prim_cong
  \\ fs [exp_eq_refl, exp_eq_sym]
QED

Theorem needs_exp_eq:
  ∀e e' d. e ≈ e' ⇒ e needs d ⇒ e' needs d
Proof
  gen_tac
  \\ gen_tac
  \\ Cases
  \\ rw [needs_def]
  \\ irule exp_eq_trans
  \\ irule_at Any $ iffLR exp_eq_sym
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_trans
  \\ pop_assum $ irule_at Any
  \\ fs [exp_eq_Prim_cong, exp_eq_refl]
QED

        (********************************************)

Theorem demands_Var:
  (Var v) demands ([],v)
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
  (Proj s i (Var v)) demands ([(s,i)],v)
Proof
  rw [demands_def,Projs_def]
  \\ metis_tac [Seq_id,exp_eq_sym]
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
  e demands d ∧ e' demands ([],w) ⇒ (Let w e e') demands d
Proof
  PairCases_on ‘d’
  \\ metis_tac [needs_def, needs_Var_is_demands, needs_Let1]
QED

Theorem demands_Let2:
  e' demands (p,v) ∧ v ≠ w ⇒ (Let w e e') demands (p,v)
Proof
  rw [demands_def,Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let w e (Seq (Projs p (Var v)) e')’
  \\ conj_tac THEN1
   (irule exp_eq_App_cong \\ fs [exp_eq_refl]
    \\ irule exp_eq_Lam_cong \\ fs [exp_eq_refl])
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Seq (Let w e (Projs p (Var v))) (Let w e e')’
  \\ conj_tac THEN1 fs [Let_Seq]
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl,Let_Var]
  \\ qid_spec_tac ‘p’ \\ Induct
  THEN1 fs [Projs_def,Let_Var2]
  \\ fs [FORALL_PROD,Projs_def] \\ rw []
  \\ fs [GSYM Projs_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Projs ((p_1,p_2)::p') (Let w e (Var v))’
  \\ conj_tac THEN1 fs [Let_Projs]
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var2]
QED

Theorem demands_Let3:
  ∀e v h ps. e demands (ps, v) ⇒ (Let v (Var h) e) demands (ps, h)
Proof
  rw [demands_def]
  \\ irule exp_eq_trans
  \\ qexists_tac ‘Let v (Var h) (Seq (Projs ps (Var v)) e)’
  \\ irule_at Any exp_eq_App_cong \\ fs [exp_eq_refl]
  \\ irule_at Any exp_eq_Lam_cong \\ fs []
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Seq
  \\ irule exp_eq_Prim_cong \\ fs [exp_eq_refl]
  \\ irule exp_eq_trans
  \\ irule_at Any Let_Projs
  \\ irule exp_eq_Projs_cong
  \\ fs [Let_Var]
QED

Theorem demands_Let_Proj: (* expects program to be in ANF *)
  e demands (ps,w) ⇒
  (Let w (Proj s i (Var v)) e) demands ((s,i)::ps,v)
Proof
  metis_tac [needs_Let_Proj, needs_Var_is_demands]
QED

Theorem demands_Let_Cons: (* expects program to be in ANF *)
  e demands ((s,LENGTH xs)::ps,w) ⇒
  (Let w (Cons s (xs ++ (Var v)::ys)) e) demands (ps,v)
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
  \\ irule exp_eq_trans \\ qexists_tac ‘Prim ope ((Seq p e)::l)’
  \\ conj_tac
  >- (irule exp_eq_Prim_cong \\ fs [exp_eq_l_refl])
  \\ Cases_on ‘ope’ \\ fs [well_formed_def]
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
  ∀ps ps' e e'. e needs (ps ++ ps', e') ⇒ e needs (ps, e')
Proof
  rw [needs_def, double_Projs]
  \\ qabbrev_tac ‘p = Projs ps e'’
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq (Seq p (Projs ps' p)) e’
  \\ conj_tac
  >- (irule exp_eq_trans \\ first_assum $ irule_at Any
      \\ irule exp_eq_Prim_cong
      \\ fs [exp_eq_refl]
      \\ ‘p needs ([], p)’ by fs [needs_refl]
      \\ drule needs_Projs
      \\ rw [needs_def, Projs_def])
  \\ irule exp_eq_trans \\ qexists_tac ‘Seq p (Seq (Projs ps' p) e)’
  \\ fs [Seq_assoc]
  \\ irule exp_eq_Prim_cong
  \\ fs [exp_eq_refl, exp_eq_sym]
QED


Theorem demands_Projs_empty:
  ∀ps v. (Projs ps (Var v)) demands ([], v)
Proof
  rpt gen_tac
  \\ ‘(Projs ps (Var v)) demands (ps, v)’ by metis_tac [Projs_def, demands_def, Seq_id, exp_eq_sym]
  \\ irule $ iffLR needs_Var_is_demands
  \\ irule needs_projs_reduce
  \\ fs []
  \\ rw [needs_Var_is_demands]
  \\ first_assum $ irule_at Any
QED

Theorem demands_empty_proj:
  e demands (ps, v) ⇒ e demands ([], v)
Proof
  ‘ps = [] ++ ps’ by rw []
  \\ rw []
  \\ metis_tac [needs_projs_reduce, needs_Var_is_demands]
QED

Theorem demands_projs_reduce:
  e demands (ps ++ ps', v) ⇒ e demands (ps, v)
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
  \\ irule exp_eq_trans
  \\ irule_at Any exp_eq_Prim_cong
  \\ drule EXISTS_EL
  \\ rw []
  \\ rename1 ‘EL n l ≈ Seq p _’
  \\ qexists_tac ‘LUPDATE (Seq p (EL n l)) n l’
  \\ rw [LIST_REL_EL_EQN, EL_LUPDATE]
  >- (IF_CASES_TAC
      \\ fs [exp_eq_refl])
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
  ∀d e e'. e ≈ e' ⇒ e demands d ⇒ e' demands d
Proof
  PairCases
  \\ rw [demands_def]
  \\ irule exp_eq_trans
  \\ rw [Once exp_eq_sym]
  \\ first_assum $ irule_at Any
  \\ irule exp_eq_trans
  \\ first_x_assum $ irule_at Any
  \\ fs [exp_eq_Prim_cong, exp_eq_refl]
QED

Theorem last_Apps:
  ∀l x e. Apps e (l ++ [x]) = App (Apps e l) x
Proof
  Induct
  \\ fs [Apps_def]
QED

Theorem last_Lams:
  ∀l x e. Lams (l ++ [x]) e = Lams l (Lam x e)
Proof
  Induct
  \\ fs [Lams_def]
QED

val _ = set_fixity "fdemands" (Infixl 480);

Definition fdemands_def:
  f fdemands ((ps, i), k) = (i < k ∧ ∃s. FINITE s ∧ ∀l. (set l ∩ s = {} ∧ LENGTH l = k) ⇒ (Apps f (MAP Var l)) demands (ps, EL i l))
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
(*
Theorem freevars_closed_subset:
  ∀e f. (∀n v. FLOOKUP f n = SOME v ⇒ closed v) ⇒ freevars (subst f e) ⊆ (freevars e) DIFF (FDOM f)
Proof
  Induct using freevars_ind
  \\ rw [closed_def]
  >- (gvs [FLOOKUP_DEF, subst_def]
      \\ first_x_assum irule
      \\ first_x_assum $ irule_at Any
      \\ fs [EL_MEM, MEM_MAP]
      \\ rename1 ‘EL n es’
      \\ qexists_tac ‘EL n es’
      \\ fs [EL_MEM])
  >- rw [subst_def, FLOOKUP_DEF]
  >- (rw [subst_def, SUBSET_DEF, MEM_EL, MAP_MAP_o]
      \\ rename1 ‘n < LENGTH es’
      \\ last_x_assum $ qspecl_then [‘EL n es’] assume_tac
      \\ gvs [EL_MAP, EL_MEM, closed_def]
      \\ pop_assum $ qspecl_then [‘f’] assume_tac
      \\ pop_assum drule
      \\ strip_tac
      \\ gvs [SUBSET_DEF]
      \\ qexists_tac ‘freevars (EL n es)’
      \\ first_assum $ irule_at Any
      \\ gvs [EL_MAP])
  >- (fs [closed_def]
      \\ first_x_assum $ qspecl_then [‘f’] assume_tac
      \\ pop_assum drule
      \\ first_x_assum $ qspecl_then [‘f’] assume_tac
      \\ pop_assum drule
      \\ rw [subst_def, SUBSET_DEF, IN_DIFF]
      \\ first_x_assum dxrule
      \\ rw [])
  >- (first_x_assum $ qspecl_then [‘f \\ n’] assume_tac
      \\ fs [closed_def]
      \\ ‘∀n' v. FLOOKUP (f \\ n) n' = SOME v ⇒ freevars v = {}’
        by (rw [] \\ Cases_on ‘n = n'’
            \\ first_x_assum irule
            \\ gvs [DOMSUB_FLOOKUP_NEQ]
            \\ first_x_assum $ irule_at Any)
      \\ first_x_assum dxrule
      \\ rw [subst_def, closed_def, SUBSET_DEF, IN_DIFF, DELETE_DEF]
      \\ first_x_assum dxrule
      \\ rw [])
  \\ gvs [SUBSET_DEF, IN_DIFF, closed_def, subst_def]
  \\ first_x_assum $ qspecl_then [‘FDIFF f (set (MAP FST lcs))’] assume_tac
  \\ ‘∀n v. FLOOKUP (FDIFF f (set (MAP FST lcs))) n = SOME v ⇒ freevars v = {}’
    by (rw []
        \\ first_x_assum irule
        \\ gvs [FLOOKUP_DEF, FDOM_FDIFF, DRESTRICT_DEF, FDIFF_def]
        \\ first_x_assum $ irule_at Any
        \\ fs [])
  \\ first_x_assum drule
  \\ rw [] \\ gvs []
  >- (first_x_assum dxrule
      \\ rw [MEM_EL]
      \\ strip_tac
      \\ last_x_assum irule
      \\ gvs [EL_MAP, MEM_MAP]
      \\ rename1 ‘EL n lcs’
      \\ qabbrev_tac ‘p = EL n lcs’
      \\ PairCases_on ‘p’
      \\ qexists_tac ‘(p0, subst (FDIFF f (set (MAP FST lcs))) p1)’
      \\ fs []
      \\ qexists_tac ‘(p0, p1)’
      \\ fs [MEM_EL]
      \\ last_x_assum $ irule_at Any
      \\ fs [])
  >- (first_x_assum dxrule
      \\ rw [MEM_EL]
      \\ rename1 ‘EL n _’
      \\ strip_tac
      \\ first_x_assum irule
      \\ gvs [EL_MAP, MEM_MAP]
      \\ ‘MEM (EL n lcs) lcs’ by gvs [EL_MEM]
      \\ pop_assum $ irule_at Any
      \\ qabbrev_tac ‘p = EL n lcs’
      \\ PairCases_on ‘p’
      \\ fs [])
  >- (DISJ2_TAC
      \\ dxrule $ iffLR MEM_EL
      \\ rw []
      \\ rename1 ‘n < LENGTH lcs’
      \\ last_x_assum $ qspecl_then [‘FST (EL n lcs)’, ‘SND (EL n lcs)’] assume_tac
      \\ gvs [EL_MEM, EL_MAP]
      \\ pop_assum dxrule
      \\ rw []
      \\ qabbrev_tac ‘p = EL n lcs’
      \\ PairCases_on ‘p’
      \\ gvs []
      \\ first_x_assum dxrule
      \\ rw []
      \\ pop_assum kall_tac
      \\ pop_assum $ irule_at Any
      \\ gvs [MEM_EL]
      \\ first_assum $ irule_at Any
      \\ fs [EL_MAP])
  >- (rw [MEM_EL]
      \\ strip_tac
      \\ first_x_assum irule
      \\ gvs [MEM_EL, EL_MAP]
      \\ first_assum $ irule_at Any
      \\ gvs [EL_MAP]
      \\ rename1 ‘FST p’
      \\ PairCases_on ‘p’
      \\ fs [])
  >- (dxrule $ iffLR MEM_EL
      \\ rw []
      \\ rename1 ‘n < LENGTH lcs’
      \\ last_x_assum $ qspecl_then [‘FST (EL n lcs)’, ‘SND (EL n lcs)’] assume_tac
      \\ gvs [EL_MEM, EL_MAP]
      \\ pop_assum dxrule
      \\ rw []
      \\ qabbrev_tac ‘p = EL n lcs’
      \\ PairCases_on ‘p’
      \\ gvs []
      \\ first_x_assum dxrule
      \\ rw []
      \\ strip_tac
      \\ first_x_assum irule
      \\ gvs [MEM_EL, EL_MAP]
      \\ first_assum $ irule_at Any
      \\ gvs [EL_MAP]
      \\ rename1 ‘FST p’
      \\ PairCases_on ‘p’
      \\ fs [])
QED

Theorem freevars_closed_closed:
  ∀e f. (∀n v. FLOOKUP f n = SOME v ⇒ closed v) ∧ freevars e ⊆ FDOM f ⇒ closed (subst f e)
Proof
  rw []
  \\ dxrule freevars_closed_subset
  \\ rw [closed_def]
  \\ irule $ iffLR SUBSET_EMPTY
  \\ irule SUBSET_TRANS
  \\ pop_assum $ irule_at Any
  \\ gvs [SUBSET_DIFF_EMPTY, SUBSET_EMPTY]
QED
*)

Theorem DRESTRICT_DOMSUB_COMM:
  ∀f v s. DRESTRICT (f \\ v) s = (DRESTRICT f s) \\ v
Proof
  fs [EQ_FDOM_SUBMAP]
  \\ rw [DRESTRICT_DEF, DELETE_INTER, SUBMAP_DEF, DOMSUB_FAPPLY_THM]
QED

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
QED

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
  \\ simp [GSYM subst_does_not_change]
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

Theorem fdemands_every_thing:
  f fdemands ((ps, i), k) ⇔ (i < k ∧ ∀el. LENGTH el = k ⇒ (Apps f el) needs (ps, EL i el))
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
          \\ irule exp_eq_trans
          \\ irule_at Any exp_eq_Apps_cong
          \\ irule_at Any exp_eq_l_refl
          \\ irule_at Any exp_eq_Lams_cong
          \\ pop_assum $ irule_at Any
          \\ conj_tac
          >- (irule $ iffLR SUBSET_EMPTY
              \\ irule $ iffRL SUBSET_DEF
              \\ gvs [IN_INTER, DISJ_EQ_IMP, EVERY_MEM])
          \\ irule exp_eq_trans
          \\ irule_at Any Apps_Lams_Seq_strong
          \\ irule_at Any exp_eq_Prim_cong
          \\ gvs [EVERY_MEM, exp_eq_refl]
          \\ rw []
          >- cheat
          \\ first_x_assum dxrule
          \\ rw []
          \\ pop_assum $ qspecl_then [‘freevars e’] assume_tac
          \\ fs [MEM_MAP]
          \\ pop_assum $ qspecl_then [‘e’] assume_tac
          \\ gvs [])
      \\ cheat)
  >- (qexists_tac ‘{}’
      \\ rw []
      \\ pop_assum $ qspecl_then [‘MAP Var l’] assume_tac
      \\ gvs [EL_MAP, needs_Var_is_demands])
QED

Definition find_fdemands_def:
  find_fdemands fd (Var n) = {[], n} ∧
  find_fdemands fd (Seq e1 e2) = find_fdemands fd e1 ∪ find_fdemands fd e2 ∧
  find_fdemands fd (If e1 e2 e3) = find_fdemands fd e1 ∪
                              (find_fdemands fd e2 ∩ find_fdemands fd e3) ∧
  find_fdemands fd e = {}
End

Theorem find_fdemands_soundness:
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
QED

(*
Theorem Lam_fdemands:
  ∀e ps v. e demands (ps, v) ⇒ Lam v e fdemands ((ps, 0), 1)
Proof
  rw [fdemands_def]
  \\ rename1 ‘MAP Var l2’
  \\ Cases_on ‘l2’
  \\ fs [Apps_def, demands_Let3]
QED

Theorem Lam_fdemands2:
  ∀k e ps i v. e fdemands ((ps, i), k) ⇒ Lam v e fdemands ((ps, SUC i), SUC k)
Proof
  Induct
  \\ fs [fdemands_def]
  \\ rw []
  \\ rename1 ‘MAP Var l’
  \\ Cases_on ‘l’ \\ fs [Apps_def]
  \\ first_x_assum irule
QED
*)

Theorem Lam_require:
  ∀l l' i h.
    LENGTH l = LENGTH l' ∧ ¬MEM h l ⇒
    Apps (Lams l (Var h)) l' demands ([], h)
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

Theorem Lams_require_arg:
  ∀l i.
    ALL_DISTINCT l ∧ i < LENGTH l ⇒
    Lams l (Var (EL i l)) fdemands (([], i), LENGTH l)
Proof
  Induct
  \\ fs [Lams_def, fdemands_def]
  \\ rpt gen_tac
  \\ strip_tac
  \\ Cases
  \\ fs []
  \\ rename1 ‘EL i (h::l)’
  \\ Cases_on ‘i’
  \\ fs [Apps_def]
  >- (strip_tac
      \\ irule exp_eq_same_demands
      \\ irule_at Any demands_Let1
      \\ irule_at (Pos hd) demands_Var
      \\ irule_at Any Lam_require
      \\ rename1 ‘MAP Var t’
      \\ qspecl_then [‘l++t’] assume_tac exists_str_not_in_list
      \\ fs [MEM_APPEND]
      \\ qexists_tac ‘l’
      \\ qexists_tac ‘MAP Var t’
      \\ rename1 ‘MEM s t’
      \\ first_assum $ irule_at Any
      \\ fs [LENGTH_MAP, Once exp_eq_sym]
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
  \\ strip_tac
  \\ irule exp_eq_same_demands
  \\ first_x_assum $ irule_at Any
  \\ fs []
  \\ irule exp_eq_Apps_cong
  \\ fs [exp_eq_l_refl]
  \\ irule eval_wh_IMP_exp_eq
  \\ rw []
  \\ fs [MEM_EL, subst_def, eval_wh_thm, FLOOKUP_DEF, bind1_def]
  \\ ‘closed (Lams l (Var (EL n' l)))’ by fs [closed_Lams, EL_MEM]
  \\ fs [closed_subst]
QED

Theorem last_exists:
  ∀l. LENGTH l > 0 ⇒ ∃x t. l = t ++ [x]
Proof
  Induct
  \\ fs []
  \\ rw []
  \\ rename1 ‘hd::tl’
  \\ Cases_on ‘tl’
  \\ fs []
QED

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

Theorem Lams_equiv:
  ∀ l l' e b. ALL_DISTINCT l ∧ ALL_DISTINCT l' ∧ LENGTH l = LENGTH l' ⇒
            (Lams l e ≅? Lams l' (subst (FEMPTY |++ REVERSE (ZIP (l', MAP Var l))) e)) b
Proof
  Induct
  \\ fs [Lams_def]
  >- fs [FUPDATE_LIST, exp_eq_refl]
  \\ gen_tac
  \\ Cases
  \\ fs [Lams_def]
  \\ rw []

QED

Theorem Apps_Lams_Seq:
  ∀l l' e1 e2 b. LENGTH l = LENGTH l' ⇒
           (Apps (Lams l (Seq e1 e2)) l' ≅? Seq (Apps (Lams l e1) l') (Apps (Lams l e2) l')) b
Proof
  Induct
  \\ fs [Apps_def, Lams_def, exp_eq_refl]
  \\ gen_tac
  \\ Cases
  \\ fs [Apps_def]
  \\ rw []
  \\ cheat


(*  gen_tac
  \\ completeInduct_on ‘LENGTH l’
  \\ rename1 ‘v = _’
  \\ Cases_on ‘v’
  \\ fs [Apps_def, Lams_def, exp_eq_refl]
  \\ gen_tac
  \\ strip_tac
  \\ ‘LENGTH l > 0’ by fs []
  \\ drule last_exists
  \\ rw []
  \\ rename1 ‘Apps _ l2’
  \\ ‘LENGTH l2 > 0’ by fs []
  \\ drule last_exists
  \\ rw [last_Lams]
  \\ rw [last_Apps]
  \\ *)

QED

Theorem find_fdemands_soundness:
  ∀e m. m = find_fdemands {} e ⇒
        (∀l i ps. ALL_DISTINCT l ∧ i < LENGTH l ⇒ (ps, EL i l) ∈ m ⇒ (Lams l e) fdemands ((ps, i), LENGTH l))
Proof
  Induct using freevars_ind
  \\ fs [find_fdemands_def]
  \\ fs [Lams_require_arg]
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
  >~[‘Seq e1 e2’]
  >- (rw [fdemands_def]
         )
QED

Theorem subst_Apps:
  ∀l f e. subst f (Apps e l) = Apps (subst f e) (MAP (subst f) l)
Proof
    Induct
    \\ fs [Apps_def, subst_def]
QED
(*

Theorem Letrec_not_user_first:
  ∀l2 l1 m h e2 n. MEM m l1 ⇒
            App (Letrec [(n, Lams (h::l1) (Var m))] (Var n)) e2
                 ≈ Letrec [(n, Lams l1 (Var m))] (Var n)
Proof
  rw []
  \\ irule eval_wh_IMP_exp_eq
  \\ rw [subst_def, eval_wh_thm, FLOOKUP_FDIFF, subst_funs_def, bind_def,
         FUPDATE_LIST, FLOOKUP_UPDATE, Lams_def]
  \\ cheat
QED


Theorem demands_letRec:
  ∀l l' i. LENGTH l ≤ LENGTH l' ∧ i < LENGTH l ⇒ Apps (Letrec [(n, Lams l (Var (EL i l)))] (Var n)) (MAP Var l') demands ([], EL i l')
Proof
  Induct
  \\ fs [demands_def, Projs_def]
  \\ rw []
  \\ rename1 ‘MAP Var l'’
  \\ Cases_on ‘l'’
  \\ fs []
  \\ rename1 ‘Lams (h1::tl1)’
  \\ rename1 ‘Var h2::MAP Var tl2’
  \\ fs [Apps_def]
  \\ Cases_on ‘i’
  \\ fs []
  >-  (irule eval_wh_IMP_exp_eq
       \\ rw []
       \\ fs [subst_def, subst_Apps, eval_wh_Seq, FLOOKUP_FDIFF]
       \\ cheat)
  \\ irule exp_eq_trans
  \\ cheat
QED

Theorem find_fdemands_soudness:
  ∀e fd m l n. m = find_fdemands l fd e ∧
               (∀n ps i len. (n, (ps, i), len) ∈ fd ⇒ i < len) ∧
             (∀ps i. i < LENGTH l ∧ (n, (ps, i), LENGTH l) ∈ fd ⇒ (ps, EL i l) ∈ m)
             ⇒ (∀d. (n, d, LENGTH l) ∈ fd ⇒ (Letrec [(n, Lams l e)] (Var n)) fdemands (d, LENGTH l))
Proof
  completeInduct_on ‘exp_size e’
  \\ Cases
  \\ fs [find_fdemands_def]
  \\ strip_tac
  \\ rpt gen_tac
  \\ strip_tac
  \\ PairCases
  \\ rw [fdemands_def]
  \\ first_assum drule
  \\ fs []
  \\ strip_tac
  >~[‘App _ _’]
  >- (first_x_assum $ qspecl_then [‘d0’, ‘d1’] assume_tac
      \\ gvs [])
  >~[‘Lam _ _’]
  >- (first_x_assum $ qspecl_then [‘d0’, ‘d1’] assume_tac
      \\ gvs [])
  >~[‘Letrec [(_, Lams _ (Letrec _ _))]’]
  >- (first_x_assum $ qspecl_then [‘d0’, ‘d1’] assume_tac
      \\ gvs [])
  >~[‘Prim ope exprl’]
  >- (Cases_on ‘ope’
      \\ fs [find_fdemands_def]
      >~[‘Prim Seq _’]
      >- cheat
      >~[‘Prim If _’]
      >- cheat
      \\ Cases_on ‘exprl’
      \\ first_x_assum $ qspecl_then [‘d0’, ‘d1’] assume_tac
      \\ gvs [find_fdemands_def])
  >- (first_assum $ qspecl_then [‘d0’, ‘d1’] assume_tac
      \\ gvs [demands_def, Projs_def]
      \\ irule eval_wh_IMP_exp_eq
      \\ last_x_assum $ kall_tac
      \\ last_x_assum $ kall_tac
      \\ last_x_assum $ kall_tac
      \\ last_x_assum $ kall_tac
      \\ Induct_on ‘l'’
      \\ fs []
      \\ rw [subst_def, subst_Apps]
      \\ cheat)
QED*)

Datatype:
  ctxt = Nil
       | IsFree string ctxt
       | Bind string exp ctxt ctxt
       | RecBind ((string # exp) list) ctxt
End

Definition ctxt_size_def:
  ctxt_size Nil = 0n ∧
  ctxt_size (IsFree s ctxt) = 1 + ctxt_size ctxt ∧
  ctxt_size (Bind s e ctxt tl) = 1 + list_size char_size s +  exp_size e + ctxt_size ctxt + ctxt_size tl ∧
  ctxt_size (RecBind sel ctxt) = 1 + exp1_size sel + ctxt_size ctxt
End

Definition subst_ctxt_def:
  (subst_ctxt ctxt (App f e) = App (subst_ctxt ctxt f) (subst_ctxt ctxt e)) ∧
  (subst_ctxt  ctxt (Prim op l) = Prim op (MAP (subst_ctxt ctxt) l)) ∧
  (subst_ctxt ctxt (Lam v e) = Lam v (subst_ctxt (IsFree v ctxt) e)) ∧
  (subst_ctxt Nil (Var n) = Var n) ∧
  (subst_ctxt (IsFree v ctxt) (Var n) = if n = v
                                        then Var n
                                        else subst_ctxt ctxt (Var n)) ∧
  (subst_ctxt (Bind v exp ctxt tl) (Var n) = if n = v
                                         then subst_ctxt ctxt exp
                                         else subst_ctxt tl (Var n)) ∧
  (subst_ctxt (RecBind nel ctxt) (Var n) = if MEM n (MAP FST nel)
                                                then Var n
                                                else subst_ctxt ctxt (Var n)) ∧
  (subst_ctxt ctxt (Letrec nel e) = Letrec nel (subst_ctxt (RecBind nel ctxt) e))
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<) (λ(c,e).(exp_size e + ctxt_size c, exp_size e))’
  \\ rw [ctxt_size_def] \\ fs []
End

Inductive find: (* i i o o *)
[find_Bottom:]
  (∀e (c:ctxt).
    find e c {} e) ∧
[find_Seq:]
  (∀e e' c (p:(string#num) list) ds v.
    find e c ds e' ∧ (p,v) ∈ ds ⇒
    find e c ds (Seq (Var v) e')) ∧
[find_Seq2:]
  (∀e e' e2 e2' c ds ds2.
     find e c ds e' ∧ find e2 c ds2 e2' ⇒
     find (Seq e e2) c (ds ∪ ds2) (Seq e' e2')) ∧
[find_If:]
  (∀ec et ee ec' et' ee' c dsc dst dse.
     find ec c dsc ec' ∧
     find et c dst et' ∧
     find ee c dse ee' ⇒
     find (If ec et ee) c (dsc ∪ (dst ∩ dse)) (If ec' et' ee')) ∧
[find_Var:]
  (∀n c. find (Var n) c {([],n)} (Var n)) ∧
[find_App:]
  (∀f f' e e' c ds ds2.
     find f c ds f' ∧
     find e c ds2 e' ⇒
     find (App f e) c ds (App f' e')) ∧
[find_Apps:]
  (∀f f' el el' c ds.
     LIST_REL (λe e'. ∃ds. find e c ds e') el el' ∧
     find f c ds f' ⇒ find (Apps f el) c ds (Apps f' el')) ∧
[find_Prim:]
  (∀c el el' ope.
     LENGTH el = LENGTH el' ∧ (∀k. k < LENGTH el ⇒ ∃ds. find (EL k el) c ds (EL k el') )
     ⇒ find (Prim ope el) c {} (Prim ope el')) ∧
[find_Prim1:]
  (∀c el el' ope ds.
     LENGTH el = LENGTH el' ∧
     (∀k. k < LENGTH el ⇒ ∃ds'. find (EL k el) c ds' (EL k el')) (* Rewritte with LIST_REL *)
     ∧ find (EL 0 el) c ds (EL 0 el') ∧ el ≠ [] ∧ well_formed ope el ⇒ find (Prim ope el) c ds (Prim ope el')) ∧
[find_Prim_Fail:]
  (∀c el ope.
     ¬ (well_written ope el) ⇒ find (Prim ope el) c {} Fail) ∧
[find_Proj:]
  (∀e e' n i c ds.
     find e c ds e' ⇒ find (Proj n i e) c ds (Proj n i e')) ∧
[find_IsEq:]
  (∀e e' n i c ds.
     find e c ds e' ⇒ find (IsEq n i e) c ds (IsEq n i e')) ∧
[find_Atom:]
  (∀el dsl el' c op.
     LENGTH dsl = LENGTH el' ∧
     LIST_REL (λe (ds, e'). find e c ds e') el (ZIP (dsl, el')) ⇒
     find (Prim (AtomOp op) el) c (BIGUNION (set dsl)) (Prim (AtomOp op) el')) ∧
[find_Subset:]
  (∀e e' c ds ds'.
     find e c ds e' ∧ (∀ps v. (ps, v) ∈ ds' ⇒ ∃ps'. (ps++ps', v) ∈ ds) ⇒ find e c ds' e') ∧
[find_Let:]
  (∀e e' e2 e2' ds ds' c v.
     find e c ds e' ∧ find e2 (Bind v e c c) ds' e2'
     ∧ (∀ps. (ps, v) ∉ ds')
     ⇒ find (Let v e e2) c ds' (Let v e' e2')) ∧
[find_Let2:]
  (∀ e e' e2 e2' ds ds' ds'' c v ps.
     find e c ds e' ∧ find e2 (Bind v e c c) ds' e2'
     ∧ (ps,v) ∈ ds'
     ∧ (∀ps' v'. (ps', v') ∈ ds'' ⇒ ((ps', v') ∈ ds' ∧ v' ≠ v) ∨ (ps', v') ∈ ds)
     ⇒ find (Let v e e2) c ds'' (Let v e' e2')) ∧
[find_Lam:]
  (∀e e' c ds v.
     find e c ds e' ⇒ find (Lam v e) c {} (Lam v e')) ∧
[find_Lams:]
  (∀e e' c ds vl.
     find e (FOLDL (λc n. IsFree n c) c vl) ds e' ⇒ find (Lams vl e) c {} (Lams vl e')) ∧
[find_Eq:]
  (∀e e' c. e ≈ e' ⇒ find e c {} e') ∧
[find_Letrec:]
  (∀e e' ds c b b'. LIST_REL (λ(n1, e1) (n2, e2). n1 = n2 ∧ e1 ≈ e2) b b' ∧ find e (RecBind b c) ds e' ⇒ find (Letrec b e) c {} (Letrec b e'))
End


fun apply_to_first_n 0 tac = ALL_TAC
  | apply_to_first_n n tac = apply_to_first_n (n-1) tac >- tac;

Theorem find_soundness_lemma:
  ∀e c ds e'. find e c ds e'  ⇒
                e ≈ e' ∧
                (∀d. d ∈ ds ⇒ e demands d)
Proof
  Induct_on ‘find’
  \\ rpt conj_tac
  \\ rpt gen_tac
  >- fs [exp_eq_refl] (* find_Bottom *)
  >~[‘e ≈ Seq (Var v) e2’] (* find_Seq *)
  >- (strip_tac
      \\ strip_tac
      \\ fs []
      \\ first_x_assum $ drule
      \\ rw []
      \\ dxrule_then assume_tac demands_empty_proj
      \\ fs [demands_def, Projs_def]
      \\ irule exp_eq_trans
      \\ first_assum $ irule_at Any
      \\ irule exp_eq_Prim_cong
      \\ fs [exp_eq_refl])
  >~[‘Seq e e2 ≈ Seq e' e2'’] (* find_Seq2 *)
  >- (rw []
      \\ fs [exp_eq_Prim_cong, demands_Seq, demands_Seq2])
  >~[‘If ec et ee ≈ If ec' et' ee'’]
  >- (rw []
      \\ fs [demands_If, demands_If2, exp_eq_Prim_cong])
  >~[‘Var n ≈ Var n’] (* find_Var *)
  >- fs [exp_eq_refl, demands_Var]
  >~[‘App f e ≈ App f' e'’] (* find_App *)
  >- (rw []
      \\ fs [exp_eq_App_cong, demands_App])
  >~[‘Apps e el' ≈ Apps e' el''’]
  >- (rw []
      \\ fs [Apps_demands]
      \\ irule exp_eq_Apps_cong
      \\ fs [LIST_REL_EL_EQN]
      \\ rw []
      \\ first_x_assum $ qspecl_then [‘n’] assume_tac
      \\ metis_tac [])
  >~[‘Proj n i e ≈ Proj n i e'’] (* find_Proj *)
  >- (strip_tac
      \\ fs [exp_eq_Prim_cong, demands_Proj])
  >~[‘IsEq n i e ≈ IsEq n i e'’] (* find_IsEq *)
  >- (rw []
      \\ fs [exp_eq_Prim_cong, demands_IsEq])
  >~[‘Prim (AtomOp op) el1 ≈ Prim (AtomOp op) el2’]
  >- (rw []
      >- (irule exp_eq_Prim_cong
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
      \\ pop_assum $ irule_at Any
      \\ fs [MEM_EL]
      \\ first_x_assum $ irule_at Any
      \\ fs [])
  >>~[‘Prim ope el1 ≈ Prim ope el2’] (* find_Prim *)
  >- (rw []
      \\ irule exp_eq_Prim_cong
      \\ rw [LIST_REL_EL_EQN, EL_MAP]
      \\ rename1 ‘EL n _’
      \\ ‘n < LENGTH el1’ by fs []
      \\ first_x_assum drule
      \\ rw [])
  >- (rw [] (* find_Prim1 *)
      >- (irule exp_eq_Prim_cong
          \\ rw [LIST_REL_EL_EQN, EL_MAP]
          \\ rename1 ‘EL n _’
          \\ ‘n < LENGTH el1’ by fs []
          \\ first_x_assum drule
          \\ rw []
          \\ fs [])
      \\ rw []
      \\ last_x_assum dxrule
      \\ rw []
      \\ Cases_on ‘el1’
      \\ fs [demands_Prim])
  >~[‘Prim ope el1 ≈ Fail’] (* find_Prim_Fail *)
  >- (rw []
      \\ fs [not_well_written_is_fail])
  >>~[‘Let v e e2 ≈ Let v e' e2'’] (* find_Let *)
  >- (rw []
      \\ fs [exp_eq_App_cong, exp_eq_Lam_cong]
      \\ rename1 ‘_ demands d’
      \\ PairCases_on ‘d’
      \\ irule demands_Let2
      \\ ‘d1 = v ∨ d1 ≠ v’ by fs []
      \\ fs []
      \\ last_x_assum irule
      \\ first_x_assum $ irule_at Any)
  >- (rw []
      \\ fs [exp_eq_App_cong, exp_eq_Lam_cong]
      \\ rename1 ‘_ demands d’
      \\ PairCases_on ‘d’
      \\ first_x_assum dxrule
      \\ rw []
      >- fs [demands_Let2]
      \\ irule demands_Let1
      \\ fs []
      \\ first_x_assum drule
      \\ rw []
      \\ drule demands_empty_proj
      \\ fs [])
  >- (rw [] (* find_Subset *)
      \\ rename1 ‘e demands d’ \\ PairCases_on ‘d’
      \\ first_x_assum drule
      \\ rw []
      \\ first_x_assum drule
      \\ rw []
      \\ drule demands_projs_reduce
      \\ fs [])
  >- (rw [] (* find_Lam *)
      \\ fs [exp_eq_Lam_cong])
  >- (rw []
      \\ fs [exp_eq_Lams_cong])
  >- (rw []
      \\ fs [])
  >- (rw []
      \\ fs [exp_eq_Letrec_cong, exp_eq_l_refl])
QED

Theorem find_soundness:
  find e Nil ds e' ⇒ e ≈ e'
Proof
  rw []
  \\ dxrule find_soundness_lemma
  \\ fs []
QED

Datatype:
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
                                          let (d2, e2') = find_function e2 (Bind v e c c) in
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
       \\ qabbrev_tac ‘e2p = find_function e2 (Bind s e c c)’
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
QED

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

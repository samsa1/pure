(*
   Verification of a compiler that ensures every Letrec bound name is a lambda (Lam).
*)
open HolKernel Parse boolLib bossLib BasicProvers;
open arithmeticTheory listTheory alistTheory optionTheory pairTheory dep_rewrite
     pred_setTheory relationTheory rich_listTheory finite_mapTheory;
open pure_expTheory pure_exp_lemmasTheory pure_exp_relTheory pure_evalTheory
     pure_congruenceTheory pure_miscTheory pure_eval_lemmasTheory
     pure_letrecTheory pure_letrecProofTheory
     pure_letrec_lamTheory pure_beta_equivTheory;

val _ = new_theory "pure_letrec_lamProof";


Definition apps_ok_def:
  apps_ok (apps : string |-> exp) ⇔
    (* each substition replaces a ‘Var n’ by ‘App (Var n) arg’ *)
    ∀n v. FLOOKUP apps n = SOME v ⇒ ∃arg. v = App (Var n) arg ∧ closed arg
End

Definition lams_ok_def:
  lams_ok apps xs ys ⇔
    (* all the substitions in apps must be within set of defined names *)
    FDOM apps ⊆ set (MAP FST xs) ∧
    LIST_REL
      (λ(v1,x1) (v2,x2).
         (* bound names stay the same *)
         v1 = v2 ∧
         if v1 IN FDOM apps then
           (* if this is an updated binding, then add a Lam, and subst apps: *)
           ∃w. ~(MEM w (freevars x1)) ∧ ~(MEM w (MAP FST xs)) ∧
               x2 = Lam w (subst apps x1)
         else (* otherwise only subst apps: *) x2 = subst apps x1)
      xs ys
End

Inductive letrec_lam:
  (∀xs x apps ys.
     apps_ok apps ∧ lams_ok apps xs ys ∧ closed (Letrec xs x) ⇒
     letrec_lam
       (Letrec xs x)
       (Letrec ys (subst apps x)))
  ∧
  (∀xs x apps ys arg.
     apps_ok apps ∧ lams_ok apps xs ys ∧
     closed arg ∧ closed (Letrec xs x) ∧ w ∉ set (MAP FST xs) ⇒
     letrec_lam
       (Letrec xs x)
       (App (Letrec ys (Lam w (subst apps x))) arg))
End

(********************)

Theorem apps_ok_FRANGE_freevars:
  ∀apps. apps_ok apps ⇒ ∀v. v ∈ FRANGE apps ⇒ freevars v ⊆ FDOM apps
Proof
  rw[apps_ok_def, IN_FRANGE_FLOOKUP] >>
  last_x_assum drule >> strip_tac >> gvs[FLOOKUP_DEF, closed_def]
QED

Theorem apps_ok_freevars_subst:
  ∀apps x. apps_ok apps ⇒ freevars (subst apps x) = (freevars x : string list)
Proof
  recInduct subst_ind >> rw[] >> gvs[apps_ok_def, subst_def]
  >- (CASE_TAC >> simp[] >> first_x_assum drule >> rw[] >> gvs[closed_def])
  >- (simp[MAP_MAP_o, combinTheory.o_DEF] >> AP_TERM_TAC >> rw[MAP_EQ_f])
  >- gvs[DOMSUB_FLOOKUP_THM]
  >- (
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    gvs[FDIFF_def, FLOOKUP_DRESTRICT] >>
    AP_TERM_TAC >> simp[] >> AP_TERM_TAC >> simp[] >>
    rw[MAP_EQ_f] >> PairCases_on `e` >> gvs[] >> res_tac
    )
QED

Triviality lams_ok_imps:
  ∀apps xs ys. lams_ok apps xs ys ⇒
  MAP FST xs = MAP FST ys ∧ LENGTH xs = LENGTH ys ∧ FDOM apps ⊆ set (MAP FST xs)
Proof
  rw[lams_ok_def] >> gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2] >> rw[] >>
  last_x_assum drule >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Triviality lams_ok_imp_freevars:
  ∀apps xs ys.
    lams_ok apps xs ys ∧ apps_ok apps
  ⇒ MAP (λ(fn,e). freevars e) xs = MAP (λ(fn,e). freevars e) ys
Proof
  rw[MAP_EQ_EVERY2] >> gvs[lams_ok_def, LIST_REL_EL_EQN] >> rw[] >>
  last_x_assum drule >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  EVERY_CASE_TAC >> gvs[] >>
  drule apps_ok_freevars_subst >> simp[] >>
  gvs[EXTENSION] >> rw[] >> metis_tac[]
QED

Theorem letrec_lam_closed:
  ∀x y. letrec_lam x y ⇒ closed x ∧ closed y
Proof
  rw[letrec_lam_cases] >> simp[] >> imp_res_tac lams_ok_imps >> gvs[] >>
  gvs[apps_ok_freevars_subst, DELETE_SUBSET_INSERT, SUBSET_INSERT_RIGHT] >>
  imp_res_tac lams_ok_imp_freevars >>
  gvs[EVERY_MEM, MEM_EL, MAP_EQ_EVERY2, PULL_EXISTS, EL_MAP] >> rw[] >>
  gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> last_x_assum drule >>
  Cases_on `EL n xs` >> Cases_on `EL n ys` >> gvs[] >>
  rw[] >> gvs[]
QED

Theorem letrec_rel_lam_freevars:
  ∀x y. letrec_rel letrec_lam x y ⇒ freevars x = freevars y
Proof
  ho_match_mp_tac letrec_rel_ind >> rw[] >> gvs[freevars_set_def]
  >- (
    rw[EXTENSION] >> gvs[LIST_REL_EL_EQN, MEM_MAP, PULL_EXISTS] >>
    metis_tac[EL_MEM, MEM_EL]
    )
  >- (
    drule letrec_lam_closed >> simp[] >> strip_tac >>
    gvs[closed_def, SUBSET_DIFF_EMPTY] >>
    gvs[EVERY_MEM, SUBSET_DEF, MEM_MAP, PULL_EXISTS, FORALL_PROD, EXISTS_PROD] >>
    rw[] >> first_x_assum irule >>
    pop_assum mp_tac >> simp[Once MEM_EL] >> rw[] >>
    qexistsl_tac [`SND (EL n xs1)`, `p_1`] >> gvs[LIST_REL_EL_EQN] >>
    last_x_assum drule >> gvs[EL_MAP] >> strip_tac >> gvs[] >>
    Cases_on `EL n xs` >> Cases_on `EL n xs1` >> gvs[] >>
    qpat_x_assum `MAP _ _ = MAP _ _` mp_tac >>
    simp[Once LIST_EQ_REWRITE] >>
    disch_then drule >> rw[EL_MAP] >>
    metis_tac[EL_MEM]
    )
  >- (
    qsuff_tac `MAP (λ(fn,e). freevars e) xs = MAP (λ(fn,e). freevars e) xs1`
    >- gvs[] >>
    gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2] >> rw[] >>
    ntac 2 (last_x_assum drule) >> gvs[UNCURRY, EL_MAP]
    )
QED

Theorem letrec_lam_subst:
  ∀f x g y.  letrec_lam x y ⇒ letrec_lam (subst f x) (subst g y)
Proof
  rw[] >> drule letrec_lam_closed >> simp[]
QED

Theorem letrec_rel_lam_subst:
  ∀x y.
    letrec_rel letrec_lam x y ⇒
    ∀f g. fmap_rel (letrec_rel letrec_lam) f g ⇒
          letrec_rel letrec_lam (subst f x) (subst g y)
Proof
  ho_match_mp_tac letrec_rel_ind >> rw[] >>
  simp[subst_def, Once letrec_rel_cases]
  >- (
    gvs[fmap_rel_OPTREL_FLOOKUP] >>
    last_x_assum (qspec_then `n` mp_tac) >>
    CASE_TAC >> CASE_TAC >> gvs[] >> simp[Once letrec_rel_cases]
    )
  >- (
    last_x_assum irule >>
    gvs[fmap_rel_OPTREL_FLOOKUP, DOMSUB_FLOOKUP_THM] >> rw[]
    )
  >- (gvs[LIST_REL_EL_EQN] >> rw[EL_MAP]) >>
  (
    qexists_tac
      `MAP (λ(p1,p2). (p1, subst (FDIFF g (set (MAP FST xs1))) p2)) xs1` >>
    qexists_tac `subst (FDIFF g (set (MAP FST xs1))) y` >> simp[] >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    first_x_assum (irule_at Any) >> gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[]
    >- (gvs[fmap_rel_OPTREL_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >> rw[])
    >- (
      last_x_assum drule >> Cases_on `EL n xs` >> Cases_on `EL n xs1` >> gvs[] >>
      disch_then irule >>
      gvs[fmap_rel_OPTREL_FLOOKUP, FDIFF_def, FLOOKUP_DRESTRICT] >> rw[]
      ) >>
    disj1_tac >> drule letrec_lam_subst >> simp[subst_def]
  )
QED

Triviality letrec_rel_lam_subst_single:
  letrec_rel letrec_lam x y ∧
  letrec_rel letrec_lam a b ⇒
  letrec_rel letrec_lam (subst s a x) (subst s b y)
Proof
  rw[] >> irule letrec_rel_lam_subst >>
  simp[fmap_rel_OPTREL_FLOOKUP, FLOOKUP_UPDATE] >> rw[]
QED

Theorem letrec_rel_lam_subst_funs:
  ∀a c as bs cs s sub.
  letrec_rel letrec_lam a c ∧
  LIST_REL (letrec_rel letrec_lam) (MAP SND as) (MAP SND bs) ∧
  MAP FST as = MAP FST bs ∧
  apps_ok sub ∧ lams_ok sub bs cs ∧
  closed (Letrec as Fail) ∧ closed (Letrec cs Fail)
  ⇒ letrec_rel letrec_lam
      (subst (FDIFF (FEMPTY |++ (MAP (λ(v,e). (v,Letrec as e)) as)) s) a)
      (subst (FDIFF (FEMPTY |++ (MAP (λ(v,e). (v,Letrec cs e)) cs)) s)
        (subst (FDIFF sub s) c))
Proof
  Induct_on `letrec_rel` >> rw[]
  >- (
    simp[subst_def, FDIFF_def, FLOOKUP_DRESTRICT] >>
    reverse IF_CASES_TAC >> gvs[]
    >- (simp[subst_def, FLOOKUP_DRESTRICT, Once letrec_rel_cases]) >>
    Cases_on `FLOOKUP sub n` >> gvs[]
    >- (
      simp[subst_def, FLOOKUP_DRESTRICT] >>
      simp[flookup_fupdate_list, GSYM MAP_REVERSE, ALOOKUP_MAP] >>
      imp_res_tac lams_ok_imps >> gvs[] >>
      CASE_TAC >> gvs[]
      >- (
        CASE_TAC >> gvs[] >- simp[Once letrec_rel_cases] >>
        simp[Once letrec_rel_cases] >> pop_assum mp_tac >> gvs[] >>
        qsuff_tac `ALOOKUP (REVERSE cs) n = NONE` >> gvs[] >>
        gvs[ALOOKUP_NONE, MAP_REVERSE]
        ) >>
      drule ALOOKUP_SOME_EL_2 >>
      disch_then (qspec_then `REVERSE cs` assume_tac) >> gvs[MAP_REVERSE] >>
      rename1 `EL k (_ cs) = (_, ec)` >> rename1 `_ (_ as) = (_, ea)` >>
      drule (GSYM EL_REVERSE) >>
      qspecl_then [`k`,`cs`] mp_tac (GSYM EL_REVERSE) >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >> rw[] >>
      qmatch_asmsub_abbrev_tac `EL kr _` >>
      simp[Once letrec_rel_cases] >> goal_assum drule >> simp[] >>
      `kr < LENGTH cs` by (unabbrev_all_tac >> DECIDE_TAC) >>
      qexists_tac `SND (EL kr bs)` >> rw[]
      >- (gvs[LIST_REL_EL_EQN, EL_MAP] >> last_x_assum drule >> simp[]) >>
      disj1_tac >>
      qpat_abbrev_tac `b = EL kr bs` >> PairCases_on `b` >> gvs[] >>
      simp[letrec_lam_cases] >> goal_assum (drule_at Any) >> simp[] >>
      gvs[lams_ok_def, LIST_REL_EL_EQN] >>
      first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
      gvs[FLOOKUP_DEF] >> rw[] >> gvs[EVERY_EL, EL_MAP] >> rw[] >>
      last_x_assum drule >> simp[] >> strip_tac >>
      drule letrec_rel_lam_freevars >> strip_tac >> gvs[] >>
      last_x_assum drule >> simp[]
      )
    >- (
      imp_res_tac apps_ok_def >> gvs[] >>
      simp[subst_def, FLOOKUP_DRESTRICT, flookup_fupdate_list] >>
      simp[GSYM MAP_REVERSE, ALOOKUP_MAP] >>
      imp_res_tac lams_ok_imps >> gvs[] >>
      pop_assum mp_tac >> simp[SUBSET_DEF] >> rw[] >> gvs[FLOOKUP_DEF] >>
      pop_assum imp_res_tac >>
      CASE_TAC >> gvs[ALOOKUP_NONE, MAP_REVERSE] >>
      CASE_TAC >> gvs[ALOOKUP_NONE, MAP_REVERSE] >>
      simp[Once letrec_rel_cases] >> goal_assum drule >> simp[] >>
      drule ALOOKUP_SOME_EL_2 >>
      disch_then (qspec_then `REVERSE as` assume_tac) >> gvs[MAP_REVERSE] >>
      rename1 `EL k (_ cs) = (_, ec)` >> rename1 `_ (_ as) = (_, ea)` >>
      drule (GSYM EL_REVERSE) >>
      qspecl_then [`k`,`as`] mp_tac (GSYM EL_REVERSE) >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >> rw[] >>
      qmatch_asmsub_abbrev_tac `EL kr _` >>
      qexists_tac `SND (EL kr bs)` >>
      `kr < LENGTH cs` by (unabbrev_all_tac >> DECIDE_TAC) >> rw[]
      >- (gvs[LIST_REL_EL_EQN, EL_MAP] >> last_x_assum drule >> simp[]) >>
      qpat_abbrev_tac `b = EL kr bs` >> PairCases_on `b` >> gvs[] >>
      imp_res_tac lams_ok_def >> gvs[LIST_REL_EL_EQN] >>
      pop_assum drule >> simp[] >> strip_tac >> gvs[] >>
      simp[letrec_lam_cases] >> irule_at Any EQ_REFL >> simp[] >>
      rw[] >> gvs[EVERY_EL, EL_MAP] >> rw[] >>
      last_x_assum drule >> simp[] >> strip_tac >>
      drule letrec_rel_lam_freevars >> strip_tac >> gvs[] >>
      last_x_assum drule >> simp[]
      )
    )
  >- (
    simp[subst_def, Once letrec_rel_cases] >>
    simp[GSYM fdiff_fdomsub_commute, fdiff_fdomsub_INSERT] >>
    last_x_assum irule >> simp[] >>
    irule_at Any EQ_REFL >> simp[]
    )
  >- (
    simp[subst_def, Once letrec_rel_cases] >>
    simp[GSYM fdiff_fdomsub_commute, fdiff_fdomsub_INSERT] >> rw[] >>
    last_x_assum irule >> simp[] >>
    irule_at Any EQ_REFL >> simp[]
    )
  >- (
    simp[subst_def, Once letrec_rel_cases] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    last_x_assum drule >> strip_tac >> pop_assum irule >> simp[] >>
    goal_assum (drule_at Any) >> simp[EL_MAP]
    )
  >- (
    rename1 `letrec_lam (Letrec zs _) z` >>
    simp[subst_def, FDIFF_FDIFF] >> qpat_abbrev_tac `r = s ∪ set (MAP FST zs)` >>
    simp[Once letrec_rel_cases] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM] >>
    gvs[LIST_REL_CONJ] >>
    irule_at Any OR_INTRO_THM1 >>
    qexists_tac
      `subst (FDIFF (FEMPTY |++ MAP (λ(v,e). (v,Letrec cs e)) cs) r)
          (subst (FDIFF sub r) c)` >>
    qexists_tac
      `MAP (λ(p1,p2). (p1,
        subst (FDIFF (FEMPTY |++ MAP (λ(v,e). (v,Letrec cs e)) cs) r)
          (subst (FDIFF sub r) p2))) zs` >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM] >>
    reverse (rw[])
    >- (
      first_x_assum irule >> simp[] >> goal_assum (drule_at Any) >> simp[]
      )
    >- (
      gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      qpat_abbrev_tac `x = EL n xs` >> qpat_abbrev_tac `zz = EL n zs` >>
      PairCases_on `x` >> PairCases_on `zz` >> gvs[] >>
      last_x_assum drule >> simp[] >> disch_then irule >> simp[] >>
      goal_assum (drule_at Any) >> simp[EL_MAP]
      ) >>
    drule letrec_lam_subst >>
    disch_then (qspecl_then [`FDIFF sub s`, `FDIFF sub s`] mp_tac) >>
    simp[subst_def, FDIFF_FDIFF] >> strip_tac >>
    drule letrec_lam_subst >>
    disch_then (qspecl_then [
      `FDIFF (FEMPTY |++ MAP (λ(v,e). (v,Letrec cs e)) cs) r`,
      `FDIFF (FEMPTY |++ MAP (λ(v,e). (v,Letrec cs e)) cs) r`
      ] mp_tac) >>
    simp[subst_def, FDIFF_FDIFF] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM] >>
    `r ∪ set (MAP FST zs) = r` by (
      unabbrev_all_tac >> gvs[EXTENSION] >> metis_tac[]) >> gvs[] >>
    qsuff_tac
      `subst (FDIFF (FEMPTY |++ MAP (λ(v,e). (v,Letrec cs e)) cs) r)
        (subst (FDIFF sub s) z) =
       subst (FDIFF (FEMPTY |++ MAP (λ(v,e). (v,Letrec cs e)) cs) s)
        (subst (FDIFF sub s) z)` >>
    gvs[] >>
    qpat_x_assum `letrec_lam _ _` mp_tac >> simp[Once letrec_lam_cases] >>
    strip_tac >> gvs[] >>
    `MAP FST ys = MAP FST zs` by (
      imp_res_tac lams_ok_imps >>
      gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM]) >>
    gvs[] >> simp[subst_def, FDIFF_FDIFF]
    )
  >- (
    rename1 `Letrec xs a` >> rename1 `Letrec ys c` >>
    simp[subst_def, Once letrec_rel_cases] >>
    gvs[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> gvs[GSYM FST_THM] >>
    gvs[FDIFF_FDIFF] >> qpat_abbrev_tac `r = s ∪ set (MAP FST ys)` >>
    qexists_tac
      `MAP (λ(p1,p2). (p1,
        subst (FDIFF (FEMPTY |++ MAP (λ(v,e). (v,Letrec cs e)) cs) r)
          (subst (FDIFF sub r) p2))) ys` >>
    qexists_tac
      `subst (FDIFF (FEMPTY |++ MAP (λ(v,e). (v,Letrec cs e)) cs) r)
        (subst (FDIFF sub r) c)` >>
    simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
    first_x_assum (irule_at Any) >> simp[] >>
    goal_assum (drule_at Any) >> simp[] >>
    gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
    qpat_abbrev_tac `x = EL n xs` >> qpat_abbrev_tac `y = EL n ys` >>
    PairCases_on `x` >> PairCases_on `y` >> gvs[] >>
    last_x_assum drule >> simp[] >> strip_tac >>
    pop_assum irule >> simp[] >>
    goal_assum (drule_at Any) >> simp[EL_MAP]
    )
QED

Theorem letrec_lam_correct:
  letrec_rel letrec_lam x y ∧ closed x ∧ closed y ⇒ x ≃ y
Proof
  rw [] \\ irule eval_to_sim_thm \\ fs []
  \\ qexists_tac ‘letrec_rel letrec_lam’ \\ fs []
  \\ simp [eval_to_sim_def]
  \\ rpt (pop_assum kall_tac)
  \\ qabbrev_tac ‘c = letrec_lam’
  \\ gen_tac \\ gen_tac
  \\ qid_spec_tac ‘e1’
  \\ qid_spec_tac ‘k’
  \\ ho_match_mp_tac eval_wh_to_ind \\ rw []
  THEN1
   (rename [‘Lam s x’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ rw []
    \\ fs [eval_wh_to_def]
    \\ unabbrev_all_tac \\ rw[]
    \\ irule letrec_rel_lam_subst_single
    \\ simp[letrec_rel_refl])
  THEN1
   (rename [‘App x1 x2’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ rw [] \\ fs []
    \\ fs [eval_wh_to_def]
    \\ Cases_on ‘eval_wh_to k x1 = wh_Diverge’
    THEN1 (fs [] \\ res_tac \\ qexists_tac ‘ck’ \\ fs [])
    \\ fs []
    \\ first_x_assum drule \\ fs [] \\ rw []
    \\ Cases_on ‘dest_wh_Closure (eval_wh_to k x1)’ \\ fs []
    THEN1
     (fs [AllCaseEqs()] \\ qexists_tac ‘ck’ \\ fs []
      \\ Cases_on ‘eval_wh_to k x1’ \\ fs [])
    \\ Cases_on ‘eval_wh_to k x1’ \\ gvs []
    \\ rename [‘eval_wh_to (ck + k) g = wh_Closure _ e1’]
    \\ ‘letrec_rel c (bind s x2 e) (bind s y e1)’ by (
      rw[bind_single_def] >> unabbrev_all_tac >>
      irule letrec_rel_lam_subst >> simp[] >>
      simp[fmap_rel_OPTREL_FLOOKUP, FLOOKUP_UPDATE] >> rw[])
    \\ Cases_on ‘k’ \\ fs []
    THEN1 (qexists_tac ‘0’ \\ fs [] >>
           IF_CASES_TAC >> simp[] >>
           drule eval_wh_inc >> disch_then (qspec_then `ck` (assume_tac o GSYM)) >>
           gvs[])
    \\ fs [ADD1]
    \\ last_x_assum drule \\ fs []
    \\ impl_tac THEN1 (
         simp[bind_single_def] >>
         imp_res_tac eval_wh_to_Closure_freevars_SUBSET >> simp[closed_def] >>
         once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
         dep_rewrite.DEP_REWRITE_TAC[freevars_subst_single] >> simp[] >>
         rw[EXTENSION, DISJ_EQ_IMP] >>
         first_x_assum drule >> rw[] >> gvs[closed_def])
    \\ strip_tac
    \\ Cases_on ‘eval_wh_to n (bind s x2 e) = wh_Diverge’ \\ fs []
    THEN1
     (qexists_tac ‘ck'’ \\ fs [] \\ IF_CASES_TAC \\ fs [] >>
      drule eval_wh_to_agree >>
      disch_then (qspec_then `ck + (n + 1)` (assume_tac o GSYM)) >>
      gvs[])
    \\ qexists_tac ‘ck+ck'’
    \\ ‘eval_wh_to (ck + (n + 1) + ck') g = wh_Closure s e1’ by (
      qspecl_then [`ck + (n + 1) + ck'`,`g`,`ck + (n + 1)`]
      assume_tac eval_wh_inc >>
      gvs[])
    \\ fs [] \\ Cases_on ‘eval_wh_to n (bind s x2 e)’ \\ fs []
    \\ ‘eval_wh_to (ck + (ck' + n)) (bind s y e1) =
        eval_wh_to (ck' + n) (bind s y e1)’ by (
      irule eval_wh_inc >> simp[]) >>
    fs[])
  THEN1
   (rename [‘Letrec f y’]
    \\ qpat_x_assum ‘letrec_rel c _ _’ mp_tac
    \\ simp [Once letrec_rel_cases] \\ reverse (rw []) \\ fs []
    THEN1
     (Cases_on ‘k’ \\ fs [eval_wh_to_def]
      THEN1 (qexists_tac ‘0’ \\ fs []) \\ fs [ADD1]
      \\ ‘letrec_rel c (subst_funs f y) (subst_funs xs1 y1)’ by (
        dep_rewrite.DEP_REWRITE_TAC[subst_funs_eq_subst] >> gvs[] >>
        unabbrev_all_tac >>
        irule letrec_rel_lam_subst >> simp[] >>
        irule fmap_rel_FUPDATE_LIST_same >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[GSYM FST_THM] >>
        gvs[LIST_REL_EL_EQN] >> rw[] >> gvs[EL_MAP] >>
        last_assum drule >> rename1 `EL foo f` >>
        qabbrev_tac `a = EL foo f` >> qabbrev_tac `b = EL foo xs1` >>
        PairCases_on `a` >> PairCases_on `b` >> gvs[] >> rw[] >>
        simp[Once letrec_rel_cases] >>
        goal_assum (drule_at Any) >> qexists_tac `xs1` >> simp[] >>
        gvs[LIST_REL_EL_EQN, EL_MAP])
      \\ first_x_assum drule \\ fs []
      \\ reverse impl_tac >- rw[] >>
         rw[subst_funs_def, bind_def] >> simp[closed_def] >>
         once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
         dep_rewrite.DEP_REWRITE_TAC[freevars_subst] >>
         simp[IN_FRANGE_FLOOKUP, PULL_EXISTS, FDOM_FUPDATE_LIST] >>
         simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
         simp[GSYM FST_THM] >> gvs[SUBSET_DEF, EXTENSION] >>
         metis_tac[])
    \\ unabbrev_all_tac
    \\ pop_assum mp_tac
    \\ simp [Once letrec_lam_cases] \\ rw []
    \\ ‘closed (subst_funs ys (subst apps y1)) ∧ closed (subst_funs f y)’ by (
        rw[subst_funs_def, bind_def, closed_def] >>
        once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
        DEP_ONCE_REWRITE_TAC[freevars_subst] >>
        drule apps_ok_freevars_subst >> simp[] >> strip_tac >>
        simp[FDOM_FUPDATE_LIST, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        simp[GSYM FST_THM, SUBSET_DIFF_EMPTY] >>
        imp_res_tac lams_ok_imps >> gvs[] >>
        ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >> simp[] >>
        simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS, FORALL_PROD] >> rw[] >>
        metis_tac[])
    \\ ‘letrec_rel letrec_lam (subst_funs f y) (subst_funs ys (subst apps y1))’ by (
        last_x_assum kall_tac >>
        DEP_REWRITE_TAC[subst_funs_eq_subst] >> simp[] >>
        imp_res_tac lams_ok_imps >> gvs[] >>
        drule letrec_rel_lam_subst_funs >>
        disch_then drule >> gvs[] >> ntac 2 (disch_then drule) >>
        disch_then (qspec_then `{}` mp_tac) >> simp[FDIFF_def, DRESTRICT_UNIV])
    THEN1 (* case 1 of letrec_lam *)
     (rewrite_tac [eval_wh_to_def]
      \\ IF_CASES_TAC THEN1 (gvs [] \\ qexists_tac ‘0’ \\ fs [])
      \\ gvs [] \\ last_x_assum irule \\ fs [])
    (* case 2 of letrec_lam *)
    \\ rewrite_tac [eval_wh_to_def]
    \\ IF_CASES_TAC THEN1 (gvs [] \\ qexists_tac ‘0’ \\ fs [])
    \\ gvs []
    \\ ‘subst_funs ys (Lam w (subst apps y1)) =
        Lam w (subst_funs ys (subst apps y1))’ by (
          simp[subst_funs_def, bind_def] >>
          reverse IF_CASES_TAC >> gvs[]
          >- (
            gvs[flookup_fupdate_list] >>
            pop_assum mp_tac >> CASE_TAC >> strip_tac >> gvs[] >>
            imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM, MEM_MAP, EXISTS_PROD] >>
            metis_tac[]
            ) >>
          simp[subst_def] >> irule (GSYM subst_fdomsub) >>
          simp[apps_ok_freevars_subst] >> metis_tac[SUBSET_DEF])
    \\ fs [eval_wh_to_def] \\ fs [bind_single_def])
  >- (
    rename [‘Prim p xs’] >>
    qpat_x_assum `letrec_rel c _ _` mp_tac >>
    simp[Once letrec_rel_cases] >> rw[] >>
    Cases_on `p` >> gvs[eval_wh_to_def]
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> gvs[]) >>
      IF_CASES_TAC >> gvs[LIST_REL_EL_EQN] >>
      `∃x1 x2 x3. xs = [x1;x2;x3]` by fs[LENGTH_EQ_NUM_compute] >>
      `∃y1 y2 y3. ys = [y1;y2;y3]` by fs[LENGTH_EQ_NUM_compute] >>
      gvs[wordsTheory.NUMERAL_LESS_THM, DISJ_IMP_THM, FORALL_AND_THM] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      reverse (Cases_on `eval_wh_to (k - 1) x1`) >> gvs[]
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[]) >>
      reverse (IF_CASES_TAC) >> gvs[]
      >- (
        reverse (IF_CASES_TAC) >> gvs[]
        >- (
          qexists_tac `ck` >> gvs[] >>
          Cases_on `l` >> gvs[] >> Cases_on `ys'` >> gvs[]
          ) >>
        last_x_assum drule_all >> strip_tac >> gvs[] >>
        reverse (Cases_on `eval_wh_to (k - 1) x3`) >> gvs[]
        >- (
          qexists_tac `ck'` >>
          Cases_on `eval_wh_to (ck' + k - 1) y1 = wh_Diverge` >> gvs[] >>
          drule eval_wh_to_agree >>
          disch_then (qspec_then `ck + k - 1` assume_tac) >> gvs[]
          ) >>
        qspecl_then [`ck + ck' + k - 1`,`y1`,`ck + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qspecl_then [`ck + ck' + k - 1`,`y3`,`ck' + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qexists_tac `ck + ck'` >> gvs[]
        )
      >- (
        first_x_assum drule_all >> strip_tac >> gvs[] >>
        reverse (Cases_on `eval_wh_to (k - 1) x2`) >> gvs[]
        >- (
          qexists_tac `ck'` >>
          Cases_on `eval_wh_to (ck' + k - 1) y1 = wh_Diverge` >> gvs[] >>
          drule eval_wh_to_agree >>
          disch_then (qspec_then `ck + k - 1` assume_tac) >> gvs[]
          ) >>
        qspecl_then [`ck + ck' + k - 1`,`y1`,`ck + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qspecl_then [`ck + ck' + k - 1`,`y2`,`ck' + k - 1`] mp_tac eval_wh_inc >>
        gvs[] >> strip_tac >>
        qexists_tac `ck + ck'` >> gvs[]
        )
      )
    >- (
      IF_CASES_TAC >> gvs[] >> qexists_tac `0` >> simp[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> simp[]) >>
      IF_CASES_TAC >> gvs[] >> gvs[LIST_REL_EL_EQN] >>
      `∃x. xs = [x]` by fs[LENGTH_EQ_NUM_compute] >>
      `∃y. ys = [y]` by fs[LENGTH_EQ_NUM_compute] >>
      gvs[] >>
      first_x_assum drule_all >> rw[] >>
      Cases_on `eval_wh_to (k - 1) x` >> gvs[] >>
      qexists_tac `ck` >> gvs[] >>
      IF_CASES_TAC >> gvs[] >>
      IF_CASES_TAC >> gvs[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> simp[]) >>
      IF_CASES_TAC >> gvs[] >> gvs[LIST_REL_EL_EQN] >>
      `∃x. xs = [x]` by fs[LENGTH_EQ_NUM_compute] >>
      `∃y. ys = [y]` by fs[LENGTH_EQ_NUM_compute] >>
      gvs[] >>
      first_x_assum drule_all >> rw[] >>
      reverse (Cases_on `eval_wh_to (k - 1) x`) >> gvs[]
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[])
      >- (qexists_tac `ck` >> gvs[]) >>
      reverse IF_CASES_TAC >> gvs[]
      >- (qexists_tac `ck` >> gvs[] >> EVERY_CASE_TAC >> gvs[]) >>
      first_x_assum drule >> rw[] >>
      last_x_assum drule >> impl_tac
      >- (
        gvs[closed_def, NIL_iff_NOT_MEM] >>
        CCONTR_TAC >> gvs[] >>
        imp_res_tac eval_wh_to_freevars_SUBSET >> gvs[MEM_MAP]
        >- (
          pop_assum kall_tac >> pop_assum mp_tac >> simp[PULL_EXISTS] >>
          goal_assum drule >> simp[EL_MEM]
          )
        >- (
          pop_assum mp_tac >> simp[PULL_EXISTS] >>
          goal_assum drule >> simp[EL_MEM]
          )
        ) >>
      rw[] >>
      reverse (Cases_on `eval_wh_to (k - 1) (EL n l)`) >> gvs[]
      >- (
        qexists_tac `ck'` >>
        Cases_on `eval_wh_to (ck' + k - 1) y = wh_Diverge` >> gvs[] >>
        drule eval_wh_to_agree >>
        disch_then (qspec_then `ck + k - 1` (assume_tac o GSYM)) >> gvs[]
        ) >>
      qspecl_then [`ck + ck' + k - 1`,`y`,`ck + k - 1`] mp_tac eval_wh_inc >>
      gvs[] >> strip_tac >>
      qspecl_then [`ck + ck' + k - 1`,`EL n ys'`,`ck' + k - 1`]
        mp_tac eval_wh_inc >>
      gvs[] >> strip_tac >>
      qexists_tac `ck + ck'` >> gvs[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> gvs[]) >>
      CASE_TAC >> gvs[]
      >- (
        qsuff_tac `get_atoms (MAP (λa. eval_wh_to (k − 1) a) ys) = NONE`
        >- (rw[] >> qexists_tac `0` >> simp[]) >>
        gvs[get_atoms_NONE_eq] >> imp_res_tac LIST_REL_LENGTH >> gvs[] >>
        csimp[EL_MAP] >> gvs[EL_MAP] >>
        map_every (fn pat => qpat_x_assum pat mp_tac)
          [`∀e1. MEM e1 _ ⇒ _`, `n < _`,`eval_wh_to _ _ = _`, `∀m. m < _ ⇒ _`,
           `EVERY _ _`, `EVERY _ _`, `LENGTH _ = _`] >>
        qid_spec_tac `n` >>
        qpat_x_assum `LIST_REL _ _ _` mp_tac >>
        map_every qid_spec_tac [`ys`,`xs`] >>
        ho_match_mp_tac LIST_REL_ind >> rw[] >>
        Cases_on `n` >> gvs[]
        >- (
          qexists_tac `0` >> gvs[] >>
          first_x_assum (qspec_then `h1` mp_tac) >> simp[] >>
          disch_then drule_all >> rw[] >>
          CCONTR_TAC >> drule eval_wh_inc >>
          disch_then (qspec_then `ck + k - 1` mp_tac) >> simp[]
          ) >>
        rename1 `n < _` >>
        Cases_on `eval_wh_to (k - 1) h2 = wh_Diverge`
        >- (qexists_tac `0` >> simp[]) >>
        last_x_assum (qspec_then `n` mp_tac) >> simp[IMP_CONJ_THM] >>
        impl_tac
        >- (rw[] >> last_x_assum (qspec_then `SUC m` mp_tac) >> simp[]) >>
        strip_tac >> rename1 `l < _` >>
        qexists_tac `SUC l` >> simp[] >> rw[] >>
        Cases_on `m` >> gvs[] >>
        last_x_assum (qspec_then `0` assume_tac) >> gvs[] >>
        first_x_assum (qspec_then `h1` mp_tac) >> simp[] >>
        disch_then drule_all >> strip_tac >>
        drule eval_wh_to_agree >>
        disch_then (qspec_then `ck + k - 1` mp_tac) >> rw[] >>
        metis_tac[]
        ) >>
      Cases_on `x` >> gvs[]
      >- (
        gvs[get_atoms_SOME_NONE_eq, EL_MAP] >>
        qsuff_tac
          `∃ck. get_atoms (MAP (λa. eval_wh_to (ck + k − 1) a) ys) = SOME NONE`
        >- (rw[] >> qexists_tac `ck` >> simp[]) >>
        simp[get_atoms_SOME_NONE_eq] >> csimp[EL_MAP] >>
        imp_res_tac LIST_REL_LENGTH >> gvs[] >> goal_assum drule >>
        map_every (fn pat => qpat_x_assum pat mp_tac)
          [`∀e1. MEM e1 _ ⇒ _`, `n < _`,` ∀a. eval_wh_to _ _ ≠ _`,
           `∀m. m ≤ _ ⇒ _`, `EVERY _ _`, `EVERY _ _`, `LENGTH _ = _`] >>
        qid_spec_tac `n` >>
        qpat_x_assum `LIST_REL _ _ _` mp_tac >>
        map_every qid_spec_tac [`ys`,`xs`] >>
        ho_match_mp_tac LIST_REL_ind >> rw[] >>
        Cases_on `n` >> gvs[]
        >- (
          pop_assum (qspec_then `h1` mp_tac) >> simp[] >>
          disch_then drule_all >> strip_tac >>
          qexists_tac `ck` >>
          Cases_on `eval_wh_to (k - 1) h1` >> gvs[]
          ) >>
        rename1 `SUC n` >>
        last_x_assum (qspec_then `n` mp_tac) >> simp[] >> impl_tac
        >- (rw[] >> last_x_assum (qspec_then `SUC m` mp_tac) >> simp[]) >>
        strip_tac >>
        first_x_assum (qspec_then `h1` mp_tac) >> simp[] >>
        disch_then drule_all >> strip_tac >>
        qexists_tac `ck + ck'` >> rw[]
        >- (
          qpat_x_assum `∀a. _ ≠ wh_Atom a` (qspec_then `a` mp_tac) >>
          first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
          drule eval_wh_inc >>
          disch_then (qspec_then `ck + (ck' + k) - 1` assume_tac) >> gvs[]
          ) >>
        Cases_on `m` >> gvs[]
        >- (
          qspecl_then [`ck + (ck' + k) - 1`,`h2`,`ck' + k - 1`]
            assume_tac eval_wh_inc >>
          gvs[] >>
          full_case_tac >> gvs[] >>
          last_x_assum (qspec_then `0` assume_tac) >> gvs[]
          )
        >- (
          rename1 `m ≤ _` >>
          first_x_assum drule >> strip_tac >>
          drule eval_wh_inc >>
          disch_then (qspec_then `ck + (ck' + k) - 1` assume_tac) >> gvs[]
          )
        ) >>
      rename1 `SOME (SOME as)` >>
      qsuff_tac
        `∃ck. get_atoms (MAP (λa. eval_wh_to (ck + k − 1) a) ys) = SOME (SOME as)`
      >- (rw[] >> qexists_tac `ck` >> simp[] >> CASE_TAC >> gvs[]) >>
      gvs[get_atoms_SOME_SOME_eq, EVERY2_MAP] >>
      map_every (fn pat => qpat_x_assum pat mp_tac)
        [`∀e1. MEM e1 _ ⇒ _`, `LIST_REL _ _ _`, `EVERY _ _`, `EVERY _ _`] >>
      qid_spec_tac `as` >>
      qpat_x_assum `LIST_REL _ _ _` mp_tac >>
      map_every qid_spec_tac [`ys`,`xs`] >>
      ho_match_mp_tac LIST_REL_strongind >> rw[] >>
      rename1 `LIST_REL _ _ as` >>
      qsuff_tac
        `∃ck. LIST_REL (λa a'. eval_wh_to (ck + k − 1) a = wh_Atom a') ys as`
      >- (
        pop_assum (qspec_then `h1` mp_tac) >> simp[] >>
        disch_then drule_all >> rw[] >>
        qexists_tac `ck + ck'` >>
        qspecl_then [`ck + ck' + k - 1`,`h2`,`ck + k - 1`]
          assume_tac eval_wh_inc >>
        gvs[LIST_REL_EL_EQN] >> rw[] >>
        qspecl_then [`ck + ck' + k - 1`,`EL n ys`,`ck' + k - 1`]
          assume_tac eval_wh_inc >>
        gvs[]
        ) >>
      last_x_assum irule >> simp[]
      )
    >- (
      IF_CASES_TAC >> gvs[] >- (qexists_tac `0` >> gvs[]) >>
      IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
      )
    )
QED

Theorem Letrec_Lam:
  ∀apps xs ys e.
    apps_ok apps ∧
    lams_ok apps xs ys
  ⇒ Letrec xs e ≅ Letrec ys (subst apps e)
Proof
  rw[] >>
  once_rewrite_tac[exp_eq_open_bisimilarity_freevars] >>
  irule open_bisimilarity_suff >> rw[] >> gvs[apps_ok_freevars_subst] >>
  imp_res_tac lams_ok_imps >> imp_res_tac lams_ok_imp_freevars >> gvs[] >>
  rw[bind_def, subst_def] >>
  `FDIFF f (set (MAP FST ys)) = f` by (
    simp[FDIFF_def] >> irule disjoint_drestrict >>
    simp[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  DEP_REWRITE_TAC[subst_subst_DISJOINT_FUNION] >> conj_asm1_tac
  >- (
    rw[] >> drule_all apps_ok_FRANGE_freevars >> strip_tac >>
    gvs[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> metis_tac[]
    ) >>
  DEP_ONCE_REWRITE_TAC[FUNION_COMM] >> conj_asm1_tac
  >- (gvs[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  DEP_REWRITE_TAC[GSYM subst_subst_FUNION] >> simp[IN_FRANGE_FLOOKUP] >>
  irule letrec_lam_correct >> simp[GSYM CONJ_ASSOC] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
  simp[apps_ok_freevars_subst, EVERY_MAP] >> csimp[] >> conj_asm1_tac
  >- (
    simp[EVERY_MEM] >> rw[] >>
    rename1 `MEM ex _` >> PairCases_on `ex` >> gvs[] >>
    DEP_REWRITE_TAC[freevars_subst] >> simp[IN_FRANGE_FLOOKUP] >>
    simp[DIFF_SUBSET, DIFF_INTER] >>
    qsuff_tac `MEM (freevars ex1) (MAP (λ(fn,e). freevars e) xs)`
    >- (gvs[SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
    once_rewrite_tac[MEM_MAP] >> simp[EXISTS_PROD] >>
    goal_assum (drule_at Any) >> simp[]
    ) >>
  conj_asm1_tac
  >- (
    DEP_REWRITE_TAC[freevars_subst] >> simp[IN_FRANGE_FLOOKUP] >>
    simp[DIFF_SUBSET, DIFF_INTER] >> gvs[SUBSET_DEF, EXTENSION] >> metis_tac[]
    ) >>
  conj_asm1_tac
  >- (
    simp[EVERY_MEM] >> rw[] >>
    rename1 `MEM ey _` >> PairCases_on `ey` >> gvs[] >>
    DEP_REWRITE_TAC[freevars_subst] >> simp[IN_FRANGE_FLOOKUP] >>
    simp[DIFF_SUBSET, DIFF_INTER] >>
    qsuff_tac `MEM (freevars ey1) (MAP (λ(fn,e). freevars e) ys)`
    >- (gvs[SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
    once_rewrite_tac[MEM_MAP] >> simp[EXISTS_PROD] >>
    goal_assum (drule_at Any) >> simp[]
    ) >>
  simp[Once letrec_rel_cases] >>
  qexistsl_tac [`MAP (λ(p1,p2). (p1,subst f p2)) xs`,`subst f e`] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
  simp[LIST_REL_EL_EQN, letrec_rel_refl] >> disj1_tac >>
  simp[letrec_lam_cases] >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
  simp[EVERY_MAP] >>
  gvs[lams_ok_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >> simp[GSYM FST_THM] >>
  gvs[LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
  map_every qpat_abbrev_tac [`a = EL n xs`,`b = EL n ys`] >>
  map_every PairCases_on [`a`,`b`] >> gvs[] >>
  last_x_assum drule >> gvs[] >> strip_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  `subst apps (subst f a1) = subst f (subst apps a1)` by (
    once_rewrite_tac[EQ_SYM_EQ] >>
    DEP_ONCE_REWRITE_TAC[subst_subst_DISJOINT_FUNION] >> simp[] >>
    DEP_ONCE_REWRITE_TAC[FUNION_COMM] >> simp[] >>
    DEP_REWRITE_TAC[GSYM subst_subst_FUNION] >> simp[IN_FRANGE_FLOOKUP]) >>
  pop_assum SUBST_ALL_TAC >> gvs[] >>
  goal_assum (drule_at Any) >> simp[subst_def] >>
  irule_at Any (GSYM subst_fdomsub) >>
  simp[apps_ok_freevars_subst] >> gvs[EVERY_MEM] >>
  last_x_assum (qspec_then `EL n xs` assume_tac) >> gvs[EL_MEM] >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

(********************)

Theorem closed_cl_tm[simp]:
  closed (cl_tm)
Proof
  rw[cl_tm_def, closed_def]
QED

Theorem apps_ok_make_apps:
  ∀fns. apps_ok (make_apps fns)
Proof
  recInduct make_apps_ind >> simp[make_apps_def, apps_ok_def] >> rw[] >>
  Cases_on `e` >> gvs[FLOOKUP_UPDATE] >>
  EVERY_CASE_TAC >> gvs[FLOOKUP_DEF]
QED

Theorem FDOM_make_apps:
  ∀fns. FDOM (make_apps fns) ⊆ set (MAP FST fns)
Proof
  recInduct make_apps_ind >> simp[make_apps_def] >> rw[]
  >- (irule SUBSET_INSERT_RIGHT >> simp[]) >>
  Cases_on `e` >> gvs[FDOM_FUPDATE]
QED

Theorem lambdify_one_correct:
  ∀fns e. Letrec fns e ≅ lambdify_one fns e
Proof
  rw[lambdify_one_def] >>
  irule Letrec_Lam >> simp[apps_ok_make_apps] >>
  rw[lams_ok_def, LIST_REL_EL_EQN, EL_MAP, FDOM_make_apps] >>
  Cases_on `EL n fns` >> gvs[] >>
  IF_CASES_TAC >> gvs[] >>
  qmatch_goalsub_abbrev_tac `fresh_var x l` >>
  qspecl_then [`x`,`l`] assume_tac fresh_var_correctness >> unabbrev_all_tac >>
  gvs[] >> rename1 `¬MEM fresh _` >>
  gvs[MEM_FLAT, MEM_MAP, DISJ_EQ_IMP, PULL_EXISTS, FORALL_PROD] >>
  first_x_assum irule >> qexists_tac `q` >> metis_tac[EL_MEM]
QED

Theorem lambdify_all_correct:
  ∀e. e ≅ lambdify_all e
Proof
  recInduct freevars_ind >> rw[lambdify_all_def, exp_eq_refl]
  >- (
    irule exp_eq_Prim_cong >> rw[LIST_REL_EL_EQN, EL_MAP] >>
    first_x_assum irule >> simp[EL_MEM]
    )
  >- (irule exp_eq_App_cong >> simp[])
  >- (irule exp_eq_Lam_cong >> simp[])
  >- (
    irule exp_eq_trans >> qexists_tac `Letrec lcs (lambdify_all e)` >>
    irule_at Any exp_eq_Letrec_cong >> simp[LIST_REL_EL_EQN, exp_eq_refl] >>
    simp[lambdify_one_correct]
    )
QED

val _ = export_theory();

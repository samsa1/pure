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
      | Bind vname (α cexp) da_ctxt
      | RecBind ((vname # (α cexp)) list) da_ctxt
      | Unfold vname vname (vname list) da_ctxt
End

Definition adds_demands_def:
  (adds_demands a0 (m, e, fd) [] = e) ∧
  (adds_demands a0 (m, e, fd) (name::tl) =
     case lookup m (implode name) of
       | SOME () => Prim a0 Seq [Var a0 name; adds_demands a0 (m, e, fd) tl]
       | _ => adds_demands a0 (m, e, fd) tl)
End

Definition add_all_demands_def:
  add_all_demands a (m, e, _) = foldrWithKey (λ id () e. Prim a Seq [Var a (explode id); e] ) e m
End

Definition compute_ALL_DISTINCT_def:
  compute_ALL_DISTINCT [] m = T ∧
  compute_ALL_DISTINCT (v::tl) m =
              (mlmap$lookup m (mlstring$implode v) = NONE
               ∧ compute_ALL_DISTINCT tl (insert m (implode v) ()))
End

Definition UNZIP3_DEF:
  UNZIP3 [] = ([], [], []) ∧
  UNZIP3 ((h1, h2, h3)::tl) =
    let (l1, l2, l3) = UNZIP3 tl in
      (h1::l1, h2::l2, h3::l3)
End

Definition boolList_of_fdemands_def:
  boolList_of_fdemands m vl =
  let b = compute_ALL_DISTINCT vl (mlmap$empty mlstring$compare) in
    MAP (λv. b ∧ lookup m (mlstring$implode v) = SOME ()) vl
End

Definition handle_Apps_demands_def:
  handle_Apps_demands a [] args = ([], MAP (add_all_demands a) args, mlmap$empty mlstring$compare)  ∧
  handle_Apps_demands a bL [] = (bL, [], empty compare) ∧
  (handle_Apps_demands a (T::bL) ((m, e, fd)::args) =
    let (bL', eL', m') = handle_Apps_demands a bL args in
      (bL', e::eL', union m m')) ∧
  (handle_Apps_demands a (F::bL) (arg0::args) =
    let (bL', eL', m') = handle_Apps_demands a bL args in
      (bL', (add_all_demands a arg0)::eL', m'))
End

Definition demands_analysis_fun_def:
  (demands_analysis_fun c ((Var a0 a1): 'a cexp) fds =
     let fd = case mlmap$lookup fds (implode a1) of
            | SOME l => SOME (l, mlmap$empty mlstring$compare)
            | NONE => NONE
     in
       (mlmap$insert (mlmap$empty mlstring$compare) (implode a1) (), (Var a0 a1 : 'a cexp), fd)) ∧

  (demands_analysis_fun c (App a0 (f: 'a cexp) (argl: 'a cexp list)) fds =
     let (m1, f', fd) = demands_analysis_fun c f fds in
       let eL' = MAP (λe. demands_analysis_fun c e fds) argl in
         (case fd of
           | NONE =>
                  (let e' = MAP (λe. add_all_demands a0 e) eL' in
                    (m1, (App (a0: 'a) (f': 'a cexp) (e': 'a cexp list) : 'a cexp), NONE))
           | SOME (fdL, m2) =>
               (case handle_Apps_demands a0 fdL eL' of
                  | ([], eL'', m3) => (union m1 (union m2 m3), App a0 f' eL'', NONE)
                  | (fdL', eL'', m3) => (m1, App a0 f' eL'', SOME (fdL', union m2 m3))))) ∧

  (demands_analysis_fun c (Lam a0 vl e) fds =
   let (m, e', fd) = demands_analysis_fun (IsFree vl c) e
                                  (FOLDL (λf k. mlmap$delete f (mlstring$implode k)) fds vl) in
       (empty compare, Lam a0 vl e', SOME (boolList_of_fdemands m vl, empty compare))) ∧

  (demands_analysis_fun c (Let a0 name e1 e2) fds =
     let (m1, e1', fd1) = demands_analysis_fun c e1 fds in
       let (m2, e2', fd2) = demands_analysis_fun (Bind name e1 c) e2 (delete fds (implode name)) in
         (delete m2 (implode name),
          (case lookup m2 (implode name) of
             | NONE => Let a0 name e1' e2'
             | SOME () => Let a0 name e1' (Prim a0 Seq [Var a0 name; e2'])),
          case fd2 of
             | NONE => NONE
             | SOME (fdL, fd_map) => SOME (fdL, delete fd_map (implode name)))) ∧

  (demands_analysis_fun c (Prim a0 Seq [e1; e2]) fds =
     let (m1, e1', fd1) = demands_analysis_fun c e1 fds in
       let (m2, e2', fd2) = demands_analysis_fun c e2 fds in
         (union m1 m2, Prim a0 Seq [e1'; e2'], fd2)) ∧
  (demands_analysis_fun c (Prim a0 Seq _) fds =
   (empty compare, Prim a0 Seq [], NONE)) ∧

  (demands_analysis_fun c (Prim a0 (AtomOp op) el) fds =
     let outL = MAP (λe. demands_analysis_fun c e fds) el in
       let (mL, el', fdL) = UNZIP3 outL in
           let m = FOLDL union (empty compare) mL in
             (m, Prim a0 (AtomOp op) (el': 'a cexp list), NONE)) ∧

  (demands_analysis_fun c (Prim a0 (Cons s) el) fds =
     let el = MAP (λe. add_all_demands a0 (demands_analysis_fun c e fds)) el in
       (empty compare, Prim a0 (Cons s) el, NONE)) ∧

  (demands_analysis_fun c (Letrec a0 binds e) fds =
   let vL = MAP FST binds in
     if compute_ALL_DISTINCT vL (empty compare)
     then
       let (m, e2, fd) = demands_analysis_fun (RecBind binds c) e
                                              (FOLDL (λf k. delete f (implode k)) fds vL) in
         let outL = MAP (λ(v, e). demands_analysis_fun Nil e (empty compare)) binds in
           let (mL, eL', fdL) = UNZIP3 outL in
               let e3 = adds_demands a0 (m, e2, fd) vL in
                 (FOLDL (λf k. delete f (implode k)) m vL,
                  Letrec a0 (ZIP (vL, eL')) e3,
                  case fd of
                    | NONE => NONE
                    | SOME (bL, fd_map) => SOME (bL, FOLDL (λf k. delete f (implode k)) fd_map vL))
     else (empty compare, Letrec a0 binds e, NONE)) ∧

  (demands_analysis_fun c (Case a0 e n cases) fds =
   if MEM n (FLAT (MAP (FST o SND) cases))
   then
     (empty compare, Case a0 e n cases, NONE)
   else
     let (m, e', fd) = demands_analysis_fun c e fds in
       let cases' = MAP (λ(name,args,ce).
                           (name, args,
                            adds_demands a0
                                         (demands_analysis_fun
                                          (Unfold name n args (Bind n e c))
                                          ce
                                          (empty compare)) args)) cases in
             (empty compare, Case a0 e' n cases', NONE))
Termination
  WF_REL_TAC ‘measure $ (cexp_size (K 0)) o (FST o SND)’ \\ rw []
  \\ imp_res_tac cexp_size_lemma
  \\ fs []
End

(** Proof **)

Definition update_ctxt_def:
  (update_ctxt id n c [] = c) ∧
  (update_ctxt id n c ((i,p)::tl) =
   update_ctxt id n (Bind p (Proj id i (Var n)) c) tl)
End

Definition ctxt_trans_def:
  ctxt_trans (Nil: α da_ctxt) = Nil ∧
  ctxt_trans (IsFree l ctxt) = FOLDL (λc n. IsFree n (c:ctxt)) (ctxt_trans ctxt) l ∧
  ctxt_trans (Bind n e ctxt) = Bind n (exp_of e) (ctxt_trans ctxt) ∧
  ctxt_trans ((RecBind (binds: (vname # α cexp) list) ctxt): α da_ctxt) = (RecBind (MAP (λ(n,e). (n, exp_of e)) binds) (ctxt_trans ctxt) : ctxt) ∧
  ctxt_trans (Unfold id n names c) = update_ctxt id n (ctxt_trans c) (MAPi (λi v. (i, v)) names)
End

Definition demands_map_to_set_def:
  demands_map_to_set m = IMAGE (λx. (([]: (string # num) list), explode x)) (FDOM (to_fmap m))
End

Definition fd_to_set_def:
  fd_to_set NONE = NONE ∧
  fd_to_set (SOME (bL, m)) = SOME (bL, demands_map_to_set m)
End

Definition fdemands_map_to_set_def:
  fdemands_map_to_set fds = IMAGE (λx. (explode x, (to_fmap fds) ' x)) (FDOM (to_fmap fds))
End

Theorem demands_map_union:
  map_ok m1 ∧ map_ok m2 ∧ cmp_of m1 = cmp_of m2
  ⇒ demands_map_to_set (union m1 m2) = demands_map_to_set m1 ∪ demands_map_to_set m2
Proof
  rw [union_thm, demands_map_to_set_def]
QED

Theorem demands_map_empty:
  demands_map_to_set (empty cmp) = {}
Proof
  rw [empty_thm, demands_map_to_set_def]
QED

Theorem demands_map_insert:
  map_ok m ⇒ demands_map_to_set (insert m (implode n) ()) = demands_map_to_set m ∪ {[], n}
Proof
  rw [insert_thm, demands_map_to_set_def, Once INSERT_SING_UNION, UNION_COMM]
QED

Theorem demands_map_FOLDL:
  ∀l cmp m2. TotOrd cmp ∧ EVERY (λm. map_ok m ∧ cmp_of m = cmp) l ∧ map_ok m2 ∧ cmp_of m2 = cmp
             ⇒ demands_map_to_set (FOLDL union m2 l)
               = demands_map_to_set m2 ∪ BIGUNION (set (MAP demands_map_to_set l))
Proof
  Induct >> rw [] >>
  rename1 ‘union m2 h’ >>
  last_x_assum $ qspecl_then [‘cmp_of m2’, ‘union m2 h’] assume_tac >>
  gvs [union_thm, demands_map_union, UNION_ASSOC]
QED

Theorem FOLDL_delete_ok:
  ∀m v. map_ok m
        ⇒ map_ok (FOLDL (λm2 w. delete m2 (implode w)) m vL)
          ∧ cmp_of (FOLDL (λm2 w. delete m2 ((implode w) : mlstring)) m vL) = cmp_of m
Proof
  Induct_on ‘LENGTH vL’ >> rw [] >>
  rename1 ‘SUC _ = LENGTH vL’ >>
  qspecl_then [‘vL’] assume_tac last_exists >> gvs [FOLDL_APPEND, delete_thm]
QED

Theorem demands_map_delete:
  ∀m v. map_ok m ⇒ ∀ps. (ps, v) ∉ demands_map_to_set (delete m (implode v))
Proof
  rw [demands_map_to_set_def, delete_thm]
QED

Theorem demands_map_delete_subset:
  ∀m v. map_ok m ⇒
        demands_map_to_set (delete m (implode v)) ⊆ demands_map_to_set m
Proof
  rw [demands_map_to_set_def, delete_thm]
QED

Theorem demands_map_FOLDL_delete_subset:
  ∀vL m. map_ok m ⇒
        demands_map_to_set (FOLDL (λf k. delete f (implode k)) m vL) ⊆ demands_map_to_set m
Proof
  Induct >> rw [] >>
  irule SUBSET_TRANS >>
  last_x_assum $ irule_at (Pos hd) >>
  gvs [demands_map_delete_subset, delete_thm]
QED

Theorem demands_map_delete2:
  ∀m v w ps. map_ok m ∧ (ps, v) ∉ demands_map_to_set m
           ⇒ (ps, v) ∉ demands_map_to_set (delete m w)
Proof
  rw [demands_map_to_set_def, delete_thm]
QED

Theorem demands_map_FOLDL_delete:
  ∀m v.
    map_ok m ∧ MEM v vL
    ⇒ ∀ps. (ps, v) ∉ demands_map_to_set (FOLDL (λm2 w. delete m2 (implode w)) m vL)
Proof
  Induct_on ‘LENGTH vL’ >> rw [] >>
  rename1 ‘SUC _ = LENGTH vL’ >>
  qspecl_then [‘vL’] assume_tac last_exists >> gvs [FOLDL_APPEND]
  >- (irule demands_map_delete2 >>
      gvs [FOLDL_delete_ok]) >>
  irule demands_map_delete >>
  gvs [FOLDL_delete_ok]
QED

Theorem fdemands_map_to_set_soundness:
  ∀fds n x. map_ok fds ⇒
            (lookup fds (implode n) = SOME x ⇔ (n, x) ∈ fdemands_map_to_set fds)
Proof
  rw [lookup_thm, FLOOKUP_DEF, fdemands_map_to_set_def] >>
  eq_tac >> rw [] >> gvs [implode_explode] >>
  pop_assum $ irule_at Any >> gvs [explode_implode]
QED

Theorem fdemands_map_delete_subset:
  ∀v fds. map_ok fds
           ⇒ fdemands_map_to_set (delete fds v)
                                 ⊆ fdemands_map_to_set fds
Proof
  Induct >> gvs [fdemands_map_to_set_def, SUBSET_DEF, delete_thm] >>
  rw [DOMSUB_FAPPLY_NEQ]
QED

Theorem fdemands_map_FOLDL_delete_subset:
  ∀vL fds. map_ok fds
           ⇒ fdemands_map_to_set (FOLDL (λf k. delete f (implode k)) fds vL)
                                 ⊆ fdemands_map_to_set fds
Proof
  Induct >> rw [] >>
  irule SUBSET_TRANS >> last_x_assum $ irule_at $ Pos hd >>
  gvs [delete_thm, fdemands_map_delete_subset]
QED

Theorem fdemands_map_delete:
  ∀m v. map_ok m ⇒ ∀ps. (v, ps) ∉ fdemands_map_to_set (delete m (implode v))
Proof
  rw [fdemands_map_to_set_def, delete_thm]
QED

Theorem fdemands_map_delete2:
  ∀m w d. map_ok m ∧ d ∉ fdemands_map_to_set m
           ⇒ d ∉ fdemands_map_to_set (delete m w)
Proof
  gvs [FORALL_PROD] >>
  rw [fdemands_map_to_set_def, delete_thm] >>
  rename1 ‘x ∉ FDOM _ ∨ x = w’ >> pop_assum $ qspecl_then [‘x’] assume_tac >>
  Cases_on ‘x = w’ >>
  gvs [DOMSUB_FAPPLY_NEQ]
QED

Theorem fdemands_map_FOLDL_delete:
  ∀m v.
    map_ok m ∧ MEM v vL
    ⇒ ∀ps. (v, ps) ∉ fdemands_map_to_set (FOLDL (λm2 w. delete m2 (implode w)) m vL)
Proof
  Induct_on ‘LENGTH vL’ >> rw [] >>
  rename1 ‘SUC _ = LENGTH vL’ >>
  qspecl_then [‘vL’] assume_tac last_exists >> gvs [FOLDL_APPEND]
  >- (irule fdemands_map_delete2 >>
      gvs [FOLDL_delete_ok]) >>
  irule fdemands_map_delete >>
  gvs [FOLDL_delete_ok]
QED

Theorem fdemands_map_delete_soundness:
  ∀v fds n ps. map_ok fds
               ∧ (n, ps) ∈ fdemands_map_to_set (delete fds (implode v))
               ⇒ n ≠ v ∧ (n, ps) ∈ fdemands_map_to_set fds
Proof
  rw [fdemands_map_to_set_def] >>
  gvs [delete_thm, DOMSUB_FAPPLY_NEQ]
  >- (strip_tac >> gvs [])
QED

Theorem demands_map_delete_soundness:
  ∀v m n ps. map_ok m
               ∧ (ps, n) ∈ demands_map_to_set (delete m (implode v))
               ⇒ n ≠ v ∧ (ps, n) ∈ demands_map_to_set m
Proof
  rw [demands_map_to_set_def] >>
  gvs [delete_thm, DOMSUB_FAPPLY_NEQ] >>
  strip_tac >> gvs []
QED

Theorem demands_map_FOLDL_delete_soundness:
  ∀vL m n ps. (ps, n) ∈ demands_map_to_set (FOLDL (λm v. delete m (implode v)) m vL) ∧ map_ok m
               ⇒ ¬MEM n vL ∧ (ps, n) ∈ demands_map_to_set m
Proof
  Induct >> rw [] >>
  last_x_assum $ dxrule_then assume_tac >>
  gvs [delete_thm] >>
  dxrule_then (dxrule_then assume_tac) demands_map_delete_soundness >> gvs []
QED

Theorem compute_ALL_DISTINCT_soundness_lemma:
  ∀l m. compute_ALL_DISTINCT l m ∧ map_ok m ⇒
        ALL_DISTINCT l ∧ (∀v. MEM v l ⇒ lookup m (implode v) = NONE)
Proof
  Induct >> rw [compute_ALL_DISTINCT_def] >>
  last_x_assum $ dxrule_then assume_tac >>
  gvs [insert_thm, lookup_thm, FLOOKUP_UPDATE]
  >- (strip_tac >> first_x_assum $ dxrule_then assume_tac >>
      gvs []) >>
  first_x_assum $ dxrule_then assume_tac >>
  FULL_CASE_TAC >> fs []
QED

Theorem compute_ALL_DISTINCT_soundness:
  ∀l. compute_ALL_DISTINCT l (empty compare) ⇒ ALL_DISTINCT l
Proof
  rw [] >> dxrule_then assume_tac compute_ALL_DISTINCT_soundness_lemma >>
  gvs [empty_thm, TotOrd_compare]
QED

Theorem FOLDL_union_map_ok:
  ∀l cmp m. TotOrd cmp ∧ EVERY (λm. map_ok m ∧ cmp_of m = cmp) l ∧ map_ok m ∧ cmp_of m = cmp ⇒
          map_ok (FOLDL union m l)
Proof
  Induct
  \\ fs [empty_thm]
  \\ rw [union_thm]
QED

Theorem FOLDL_union_cmp_of:
  ∀l cmp m. TotOrd cmp ∧ EVERY (λm. map_ok m ∧ cmp_of m = cmp) l ∧ map_ok m ∧ cmp_of m = cmp ⇒
          cmp_of (FOLDL union m l) = cmp
Proof
  Induct
  \\ fs [empty_thm]
  \\ rw [union_thm]
QED

Theorem adds_demands_soundness:
  ∀vl e e' m ds c ds a fds fd fd2.
    map_ok m ∧ find (exp_of e) c fds (demands_map_to_set m) (exp_of e') fd
    ⇒ find (exp_of e) c fds (demands_map_to_set m)
                             (exp_of (adds_demands a (m, e', fd2) vl)) fd
Proof
  Induct
  \\ rw [adds_demands_def]
  \\ rename1 ‘lookup m (implode h)’
  \\ Cases_on ‘lookup m (implode h)’
  \\ fs []
  \\ rw [exp_of_def, op_of_def]
  \\ irule find_Seq
  \\ gvs [demands_map_to_set_def, lookup_thm, FLOOKUP_DEF]
  \\ rpt $ first_x_assum $ irule_at Any
  \\ fs [explode_implode]
QED

Theorem add_all_demands_soundness_lemma:
  ∀m s cmp a e e' fds fd fd2 c.
    TotOrd cmp ∧
    find (exp_of e) c fds (s ∪ IMAGE (λx. ([], explode x)) (FDOM (to_fmap (Map cmp m)))) (exp_of e') fd
    ⇒ find (exp_of e) c fds (s ∪ IMAGE (λx. ([], explode x)) (FDOM (to_fmap (Map cmp m))))
           (exp_of (add_all_demands a (Map cmp m, e', fd2))) fd
Proof
  Induct
  \\ fs [add_all_demands_def, foldrWithKey_def, balanced_mapTheory.foldrWithKey_def, to_fmap_def]
  \\ rw [Once INSERT_SING_UNION]
  \\ rw [Once INSERT_SING_UNION]
  \\ rename1 ‘s ∪ ({([], explode k)} ∪ _)’
  \\ last_x_assum $ qspecl_then [‘s ∪ {([], explode k)} ∪ (IMAGE (λx. ([],explode x)) (FDOM (to_fmap (Map cmp m'))))’, ‘cmp’] assume_tac
  \\ qabbrev_tac ‘set1=IMAGE (λx. ([]:(string#num) list,explode x)) (FDOM (to_fmap (Map cmp m)))’
  \\ qabbrev_tac ‘set2=IMAGE (λx. ([]:(string#num) list,explode x)) (FDOM (to_fmap (Map cmp m')))’
  \\ ‘s ∪ ({([], explode k)} ∪ (set1 ∪ set2)) = (s ∪ {([], explode k)} ∪ set2) ∪ set1’
    by metis_tac [UNION_ASSOC, UNION_COMM]
  \\ rw []
  \\ first_x_assum irule
  \\ fs []
  \\ pop_assum kall_tac
  \\ ‘(s ∪ {([], explode k)} ∪ set2) ∪ set1 = (s ∪ {([], explode k)} ∪ set1) ∪ set2’
    by metis_tac [UNION_ASSOC, UNION_COMM]
  \\ rw [exp_of_def, op_of_def]
  \\ irule find_Seq
  \\ unabbrev_all_tac
  \\ first_x_assum $ irule_at Any
  \\ fs []
  \\ qexists_tac ‘[]’
  \\ fs []
QED

Theorem add_all_demands_soundness:
  ∀m a e e' fds fd fd2 c.
    TotOrd (cmp_of m) ∧
    find (exp_of e) c fds (demands_map_to_set m) (exp_of e') fd
    ⇒ find (exp_of e) c fds (demands_map_to_set m)
           (exp_of (add_all_demands a (m, e', fd2))) fd
Proof
  Cases >> rw [] >> rename1 ‘Map f b’ >>
  dxrule_then (qspecl_then [‘b’, ‘{}’] assume_tac) add_all_demands_soundness_lemma >>
  gvs [demands_map_to_set_def, cmp_of_def]
QED

Theorem update_ctxt_soundness:
  ∀l e e' n1 n2 c fds fd.
    EVERY (λv. ∀d. (v, d) ∉ fds) (MAP SND l)
    ∧ find e (update_ctxt n1 n2 c l) fds {} e' fd
    ⇒ find (lets_for n1 n2 l e) c fds {} (lets_for n1 n2 l e') NONE
Proof
  Induct
  \\ gvs [lets_for_def, update_ctxt_def]
  >- (rw [] \\ irule find_Drop_fd \\ pop_assum $ irule_at Any)
  \\ Cases
  \\ rw [lets_for_def, update_ctxt_def]
  \\ irule find_Let
  \\ fs [dest_fd_SND_def]
  \\ irule_at Any find_Bottom
  \\ irule_at Any find_Drop_fd
  \\ last_x_assum $ irule_at Any \\ pop_assum $ irule_at Any
  \\ gvs []
QED

Theorem find_rows_of:
  ∀l l' c s fds fd.
    LIST_REL (λ(a1, b1, e1) (a2, b2, e2).
                a1 = a2 ∧ b1 = b2
                ∧ find e1 (update_ctxt a1 s c (MAPi (λi v. (i, v)) b1)) {} {} e2 fd) l l'
         ⇒ find (rows_of s l) c fds {} (rows_of s l') NONE
Proof
  Induct
  \\ fs [rows_of_def, find_Bottom]
  \\ PairCases
  \\ rw []
  \\ rename1 ‘find _ _ _ _ (rows_of _ (y::ys))’
  \\ PairCases_on ‘y’
  \\ fs [rows_of_def]
  \\ irule find_Subset
  \\ irule_at Any find_If \\ rw []
  \\ rpt $ last_x_assum $ irule_at Any
  \\ irule_at Any find_Bottom
  \\ irule_at Any update_ctxt_soundness
  \\ pop_assum $ irule_at Any \\ fs []
QED

Theorem find_subset_aid:
  ∀d ps v. (ps, v) ∈ d ⇒ ∃ps'. (ps ++ ps', v) ∈ d
Proof
  rw [] >> qexists_tac ‘[]’ >> gvs []
QED

Theorem handle_Apps_demands_soundness:
  ∀bL argl bL' fds c m eL a.
    handle_Apps_demands a bL (MAP (λe. demands_analysis_fun c e fds) argl) = (bL', eL, m)
    ∧ EVERY (λ(dm, _, _). map_ok dm ∧ cmp_of dm = compare) (MAP (λe. demands_analysis_fun c e fds) argl)
    ⇒ (bL' = [] ⇔ LENGTH bL ≤ LENGTH argl)
      ∧ (LENGTH bL > LENGTH argl ⇒ ∃bL''. LENGTH bL'' = LENGTH argl ∧  bL = bL'' ++ bL')
      ∧ (∀p. p ∈ demands_map_to_set m
             ⇒ ∃i. i < LENGTH bL ∧ i < LENGTH argl ∧ EL i bL
                   ∧ p ∈ EL i (MAP (λe'. demands_map_to_set (FST e'))
                               (MAP (λe. demands_analysis_fun c e fds) argl)))
      ∧ LENGTH argl = LENGTH eL
      ∧ map_ok m ∧ cmp_of m = compare
      ∧ (LENGTH bL ≤ LENGTH argl
         ⇒ (∃argl1 argl2.
              argl1 ++ argl2 = argl ∧ LENGTH argl1 = LENGTH bL)
           ∧  (∃eL1 eL2.
                 eL1 ++ eL2 = eL ∧ LENGTH eL1 = LENGTH bL))
      ∧ (∀i. i < LENGTH argl ⇒ EL i eL = (if i < LENGTH bL ∧ EL i bL
                                         then FST (SND (demands_analysis_fun c (EL i argl) fds))
                                         else add_all_demands a (demands_analysis_fun c (EL i argl) fds)))
Proof
  Induct >> gvs [handle_Apps_demands_def, empty_thm, TotOrd_compare, demands_map_empty, EL_MAP] >>
  Cases >> Cases >> gvs [handle_Apps_demands_def, empty_thm, TotOrd_compare, demands_map_empty] >>
  rpt $ gen_tac
  >~[‘handle_Apps_demands a (T::bL) (demands_analysis_fun c ehd fds::MAP _ tl)’]
  >- (qabbrev_tac ‘hd = demands_analysis_fun c ehd fds’ >>
      PairCases_on ‘hd’ >> gvs [handle_Apps_demands_def] >>
      qabbrev_tac ‘hAd = handle_Apps_demands a bL (MAP (λe. demands_analysis_fun c e fds) tl)’ >>
      PairCases_on ‘hAd’ >>
      strip_tac >> gvs [] >>
      last_x_assum $ drule_then $ dxrule_then  assume_tac >>
      gvs [union_thm] >> rw []
      >- (qspecl_then [‘$=’] assume_tac LIST_REL_rules >> fs [])
      >- (gvs [demands_map_union]
          >- (qexists_tac ‘0’ >> gvs []) >>
          first_x_assum $ dxrule_then assume_tac >> gvs [] >>
          rename1 ‘EL i bL’ >> qexists_tac ‘SUC i’ >> gvs [EL_MAP])
      >> gvs []
      >>~[‘ehd::(argl1 ++ argl2)’]
      >- (qexists_tac ‘ehd::argl1’ >> qexists_tac ‘argl2’ >> gvs [])
      >- (qexists_tac ‘ehd::argl1’ >> qexists_tac ‘argl2’ >> gvs []) >>
      rename1 ‘EL i _’ >> Cases_on ‘i’ >> gvs []) >>
  rename1 ‘handle_Apps_demands a bL (MAP (λe. demands_analysis_fun c e fds) tl)’ >>
  qabbrev_tac ‘hAd = handle_Apps_demands a bL (MAP (λe. demands_analysis_fun c e fds) tl)’ >>
  PairCases_on ‘hAd’ >>
  strip_tac >> gvs [] >>
  last_x_assum $ drule_then $ dxrule_then assume_tac >>
  gvs [] >> rw []
  >- (qspecl_then [‘$=’] assume_tac LIST_REL_rules >> fs [])
  >- (first_x_assum $ dxrule_then assume_tac >> gvs [] >>
      rename1 ‘EL i bL’ >> qexists_tac ‘SUC i’ >> gvs [EL_MAP]) >>
  gvs []
  >>~[‘h::(argl1 ++ argl2)’]
  >- (qexists_tac ‘h::argl1’ >> qexists_tac ‘argl2’ >> gvs [])
  >- (qexists_tac ‘h::argl1’ >> qexists_tac ‘argl2’ >> gvs []) >>
  rename1 ‘EL i _’ >> Cases_on ‘i’ >> gvs []
QED

Theorem Apps_append:
  ∀eL1 eL2 f. Apps f (eL1 ++ eL2) = Apps (Apps f eL1) eL2
Proof
  Induct >> gvs [Apps_def]
QED

Theorem UNZIP3_LENGTH:
  ∀l v1 v2 v3. UNZIP3 l = (v1, v2, v3) ⇒ LENGTH v1 = LENGTH l ∧ LENGTH v2 = LENGTH l ∧ LENGTH v3 = LENGTH l
Proof
  Induct >> gvs [UNZIP3_DEF, FORALL_PROD] >>
  rename1 ‘UNZIP3 l’ >> qabbrev_tac ‘u3 = UNZIP3 l’ >> PairCases_on ‘u3’ >>
  gvs []
QED

Theorem UNZIP3_MAP:
  ∀l. UNZIP3 l = (MAP FST l, MAP (FST o SND) l, MAP (SND o SND) l)
Proof
  Induct >> gvs [FORALL_PROD, UNZIP3_DEF]
QED

Theorem demands_analysis_soundness_lemma:
  ∀(f: α -> num) (e: α cexp) c fds m e' fd.
    demands_analysis_fun c e fds = (m, e', fd) ∧ map_ok fds
    ⇒ find (exp_of e) (ctxt_trans c) (fdemands_map_to_set fds)
         (demands_map_to_set m) (exp_of e') (fd_to_set fd) ∧
      map_ok m ∧ cmp_of m = compare ∧
      (∀bL fd_map. SOME (bL, fd_map) = fd ⇒ map_ok fd_map ∧ cmp_of fd_map = compare)
Proof
  gen_tac
  \\ completeInduct_on ‘cexp_size f e’
  \\ gen_tac
  \\ Cases
  \\ rename1 ‘Size = cexp_size _ _’
  \\ strip_tac
  \\ simp [demands_analysis_fun_def, exp_of_def]
  \\ gvs [demands_map_empty, demands_map_insert, demands_map_union,
         TotOrd_compare, insert_thm, empty_thm]
  >~[‘Var a n’]
  >- (rw [] \\ rename1 ‘lookup fds (implode n)’
      \\ Cases_on ‘lookup fds (implode n)’
      \\ gvs [find_Var, fd_to_set_def, demands_map_empty,
              find_Var2, fdemands_map_to_set_soundness, empty_thm, TotOrd_compare])
  >~[‘Prim a op l’]
  >- (Cases_on ‘op’
      >~[‘Prim a Seq l’]
      >- (Cases_on ‘l’ >~[‘Prim a Seq []’]
          \\ gvs [demands_analysis_fun_def, op_of_def, fd_to_set_def, demands_map_empty,
                 exp_of_def, empty_thm, TotOrd_compare, find_Bottom]
          \\ rename1 ‘e1::t’
          \\ Cases_on ‘t’ >~[‘Prim a Seq [e]’]
          >- (rw [demands_analysis_fun_def, empty_thm, fd_to_set_def, demands_map_empty,
                 TotOrd_compare, exp_of_def, op_of_def]
              \\ irule find_Eq \\ irule_at Any find_Bottom
              \\ irule exp_eq_IMP_exp_eq_in_ctxt
              \\ fs [exp_of_def, op_of_def, eval_wh_IMP_exp_eq,
                     eval_wh_def, eval_wh_to_def, subst_def])
          \\ rename1 ‘e1::e2::t’
          \\ Cases_on ‘t’ >~ [‘Prim a Seq (e1::e2::e3::t)’]
          >- (rw [demands_analysis_fun_def, empty_thm, fd_to_set_def, demands_map_empty,
                 TotOrd_compare, exp_of_def, op_of_def]
              \\ irule find_Eq \\ irule_at Any find_Bottom
              \\ irule exp_eq_IMP_exp_eq_in_ctxt
              \\ fs [exp_of_def, op_of_def, eval_wh_IMP_exp_eq,
                     eval_wh_def, eval_wh_to_def, subst_def])
          \\ rw []
          \\ first_assum   $ qspecl_then [‘cexp_size f e1’] assume_tac
          \\ first_x_assum $ qspecl_then [‘cexp_size f e2’] assume_tac
          \\ fs [cexp_size_def, cexp_size_lemma]
          \\ pop_assum     $ qspecl_then [‘f’, ‘e2’] assume_tac
          \\ first_x_assum $ qspecl_then [‘f’, ‘e1’] assume_tac
          \\ fs [demands_analysis_fun_def]
          \\ rename1 ‘demands_analysis_fun c _ fds’
          \\ pop_assum     $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ first_x_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ qabbrev_tac ‘p1 = demands_analysis_fun c e1 fds’
          \\ qabbrev_tac ‘p2 = demands_analysis_fun c e2 fds’
          \\ PairCases_on ‘p1’
          \\ PairCases_on ‘p2’
          \\ gvs [exp_of_def, op_of_def, demands_map_union, union_thm]
          \\ dxrule_then (dxrule_then irule) find_Seq2)
      >~ [‘AtomOp op’]
      >- (rpt gen_tac \\ strip_tac
          \\ gvs [exp_of_def, op_of_def, demands_analysis_fun_def, UNZIP3_MAP,
                  MAP_MAP_o, combinTheory.o_DEF]
          \\ rename1 ‘demands_analysis_fun c _ fds’
          \\ irule_at Any FOLDL_union_cmp_of \\ irule_at Any FOLDL_union_map_ok
          \\ irule_at Any TotOrd_compare
          \\ gvs [empty_thm, TotOrd_compare]
          \\ conj_asm1_tac
          >- (rw [EVERY_EL] \\ rename1 ‘i < LENGTH l’
              \\ last_x_assum $ qspecl_then [‘cexp_size f (EL i l)’] assume_tac
              \\ ‘cexp_size f (EL i l) < cexp6_size f l’
                   by metis_tac [cexp_size_lemma, EL_MEM]
              \\ fs [cexp_size_def]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL i l’] assume_tac
              \\ fs []
              \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL i l) fds’
              \\ PairCases_on ‘p’
              \\ gvs [EL_MAP])
          \\ assume_tac TotOrd_compare
          \\ dxrule_then (drule_then assume_tac) demands_map_FOLDL
          \\ pop_assum $ qspecl_then [‘empty compare’] assume_tac
          \\ gvs [TotOrd_compare, empty_thm, demands_map_empty, EVERY_CONJ, fd_to_set_def]
          \\ irule find_Atom \\ fs [] \\ qexists_tac ‘NONE’
          \\ rw [LIST_REL_EL_EQN, EL_ZIP, EL_MAP]
          \\ rename1 ‘EL n l’
          \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n l)’] assume_tac
          \\ ‘cexp_size f (EL n l) < cexp6_size f l’
            by metis_tac [cexp_size_lemma, EL_MEM]
          \\ fs [cexp_size_def]
          \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘EL n l’] assume_tac
          \\ fs []
          \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n l) fds’
          \\ PairCases_on ‘p’ \\ gvs []
          \\ dxrule_then assume_tac find_Drop_fd \\ fs [])
      \\ rw [] (* Cons s *)
      \\ fs [empty_thm, TotOrd_compare, demands_analysis_fun_def, demands_map_empty]
      \\ rw [exp_of_def, op_of_def, fd_to_set_def]
      \\ irule_at Any find_Prim \\ rw []
      \\ rename1 ‘k < LENGTH l’
      \\ first_x_assum $ qspecl_then [‘cexp_size f (EL k l)’] assume_tac
      \\ ‘cexp_size f (EL k l) < cexp6_size f l’
        by metis_tac [cexp_size_lemma, MEM_EL]
      \\ fs [cexp_size_def]
      \\ pop_assum kall_tac
      \\ rename1 ‘demands_analysis_fun c _ fds’
      \\ pop_assum $ qspecl_then [‘f’, ‘EL k l’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun c (EL k l) fds’
      \\ PairCases_on ‘p’
      \\ fs [EL_MAP]
      \\ irule_at Any add_all_demands_soundness
      \\ gvs [cmp_of_def, TotOrd_compare]
      \\ first_x_assum $ irule_at Any)
  >~[‘App a fe argl’]
  >- (rpt gen_tac
      \\ rename1 ‘demands_analysis_fun c _ fds’
      \\ qabbrev_tac ‘p = demands_analysis_fun c fe fds’
      \\ PairCases_on ‘p’
      \\ first_assum $ qspecl_then [‘cexp_size f fe’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘fe’] assume_tac
      \\ fs []
      \\ pop_assum $ drule_then assume_tac \\ strip_tac
      \\ rename1 ‘demands_analysis_fun _ _ _ = (d_fe, fe', fd_fe)’
      \\ Cases_on ‘fd_fe’ \\ gvs [fd_to_set_def, exp_of_def]
      >- (irule find_Apps \\ first_x_assum $ irule_at Any
          \\ rw [LIST_REL_EL_EQN, EL_MAP]
          \\ rename1 ‘EL n argl’
          \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
          \\ ‘cexp_size f (EL n argl) < cexp6_size f argl’ by metis_tac [cexp_size_lemma, MEM_EL]
          \\ fs [cexp_size_def]
          \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl’] assume_tac
          \\ fs []
          \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
          \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl) fds’
          \\ PairCases_on ‘p’ \\ fs []
          \\ irule_at Any add_all_demands_soundness
          \\ gvs [TotOrd_compare] \\ first_x_assum $ irule_at Any)
      \\ FULL_CASE_TAC \\ gvs []
      \\ rename1 ‘handle_Apps_demands a fdL (MAP _ argl)’
      \\ qabbrev_tac ‘hAd = handle_Apps_demands a fdL (MAP (λe. demands_analysis_fun c e fds) argl)’
      \\ PairCases_on ‘hAd’ \\ fs []
      \\ drule_then assume_tac handle_Apps_demands_soundness
      \\ ‘EVERY (λ(dm, _, _). map_ok dm ∧ cmp_of dm = compare) (MAP (λe. demands_analysis_fun c e fds) argl)’
        by (rw [EVERY_EL, EL_MAP] \\ rename1 ‘EL n argl’
            \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
            \\ ‘cexp_size f (EL n argl) < cexp6_size f argl’ by metis_tac [cexp_size_lemma, MEM_EL]
            \\ fs [cexp_size_def]
            \\ pop_assum kall_tac
            \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl’] assume_tac
            \\ fs []
            \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
            \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl) fds’
            \\ PairCases_on ‘p’ \\ fs [])
      \\ first_x_assum $ dxrule_then assume_tac
      \\ gvs []
      \\ FULL_CASE_TAC \\ gvs [union_thm, fd_to_set_def, demands_map_union, exp_of_def]
      >- (rename1 ‘argl1 ++ argl2’
          \\ qabbrev_tac ‘hAd' = handle_Apps_demands a fdL (MAP (λe. demands_analysis_fun c e fds) argl1)’
          \\ PairCases_on ‘hAd'’ \\ gvs [Apps_append]
          \\ irule find_Apps
          \\ irule_at Any find_No_args
          \\ irule_at Any find_Apps_fd
          \\ gvs []
          \\ qpat_x_assum ‘find _ _ _ _ _ _’ $ irule_at Any
          \\ qexists_tac ‘MAP (λe. demands_map_to_set (FST (demands_analysis_fun c e fds))) argl1’
          \\ gvs [LIST_REL_EL_EQN, FORALL_PROD] \\ rw [] \\ gvs []
          >~[‘(ps, v) ∈ demands_map_to_set hAd'2’]
          >- (disj2_tac \\ last_x_assum $ dxrule_then assume_tac
              \\ gvs [] \\ first_assum $ irule_at Any \\ gvs [EL_MAP, EL_APPEND_EQN])
          >- (gvs [EL_ZIP, EL_MAP] \\ rename1 ‘n < LENGTH _’
              \\ first_x_assum $ qspecl_then [‘n’] assume_tac \\ gvs [EL_APPEND_EQN]
              \\ last_x_assum $ qspecl_then [‘cexp_size f (EL n (argl1 ++ argl2))’] assume_tac
              \\ ‘cexp_size f (EL n (argl1 ++ argl2)) < cexp6_size f (argl1 ++ argl2)’
                by (assume_tac cexp_size_lemma >> gvs [] >> first_x_assum irule >>
                    irule EL_MEM >> fs [])
              \\ fs [cexp_size_def]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl1’] assume_tac
              \\ gvs [EL_APPEND_EQN]
              \\ pop_assum $ qspecl_then [‘c’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl1) fds’
              \\ PairCases_on ‘p’ \\ fs []
              \\ first_x_assum $ drule_then assume_tac
              \\ FULL_CASE_TAC \\ gvs []
              >- first_assum $ irule_at Any
              >- (irule_at Any add_all_demands_soundness
                  \\ first_assum $ irule_at Any
                  \\ gvs [TotOrd_compare]))
          >- (gvs [EL_MAP] \\ rename1 ‘n < LENGTH _’
              \\ first_x_assum $ qspecl_then [‘n + LENGTH argl1’] assume_tac \\ gvs [EL_APPEND_EQN]
              \\ last_x_assum $ qspecl_then [‘cexp_size f (EL (n + LENGTH argl1) (argl1 ++ argl2))’] assume_tac
              \\ ‘cexp_size f (EL (n + LENGTH argl1) (argl1 ++ argl2)) < cexp6_size f (argl1 ++ argl2)’
                by (assume_tac cexp_size_lemma >> gvs [] >> first_x_assum irule >>
                    irule EL_MEM >> fs [])
              \\ fs [cexp_size_def]
              \\ pop_assum kall_tac
              \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl2’] assume_tac
              \\ gvs [EL_APPEND_EQN]
              \\ pop_assum $ qspecl_then [‘c’] assume_tac
              \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl2) fds’
              \\ PairCases_on ‘p’ \\ fs []
              \\ first_x_assum $ drule_then assume_tac
              \\ irule_at Any add_all_demands_soundness
              \\ gvs [TotOrd_compare]
              \\ first_x_assum $ irule_at Any))
      \\ irule find_Apps_fd
      \\ rename1 ‘bL2 ++ [h] ++ t’ \\ qexists_tac ‘bL2’
      \\ ‘bL2 ++ h::t = bL2 ++ [h] ++ t’ by gvs [] \\ rw []
      \\ pop_assum kall_tac \\ first_x_assum $ irule_at $ Pos last
      \\ qexists_tac ‘MAP (λe. demands_map_to_set (FST (demands_analysis_fun c e fds))) argl’
      \\ rw [LIST_REL_EL_EQN] \\ gvs []
      >- (disj2_tac \\ last_x_assum $ dxrule_then assume_tac
          \\ gvs [] \\ first_assum $ irule_at Any
          \\ gvs [EL_MAP, EL_APPEND_EQN])
      \\ first_x_assum $ drule_then assume_tac
      \\ gvs [EL_ZIP, EL_MAP]
      \\ rename1 ‘EL n _’
      \\ first_x_assum $ qspecl_then [‘cexp_size f (EL n argl)’] assume_tac
      \\ ‘cexp_size f (EL n argl) < cexp6_size f argl’ by metis_tac [cexp_size_lemma, MEM_EL]
      \\ fs [cexp_size_def]
      \\ pop_assum kall_tac
      \\ pop_assum $ qspecl_then [‘f’, ‘EL n argl’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’] assume_tac
      \\ qabbrev_tac ‘p = demands_analysis_fun c (EL n argl) fds’
      \\ PairCases_on ‘p’ \\ fs []
      \\ first_x_assum $ drule_then assume_tac \\ gvs []
      \\ FULL_CASE_TAC
      >- first_assum $ irule_at Any
      \\ irule_at Any add_all_demands_soundness
      \\ first_x_assum $ irule_at Any
      \\ gvs [TotOrd_compare])
  >~ [‘Lam a namel e’]
  >- (rw []
      \\ first_assum $ qspecl_then [‘cexp_size f e’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘e’] assume_tac
      \\ rename1 ‘demands_analysis_fun (IsFree namel c) _ (FOLDL _ fds _)’
      \\ qabbrev_tac ‘p = demands_analysis_fun (IsFree namel c) e
                                               (FOLDL (λf k. delete f (implode k)) fds namel)’
      \\ PairCases_on ‘p’ \\ fs [empty_thm, TotOrd_compare]
      \\ first_x_assum $ drule_then assume_tac
      \\ gvs [exp_of_def, fd_to_set_def, demands_map_empty, ctxt_trans_def,
              FOLDL_delete_ok]
      \\ irule find_Subset
      \\ irule_at Any find_Lams_fd
      \\ irule_at Any find_Drop_fd
      \\ first_x_assum $ irule_at Any
      \\ gvs [fdemands_map_FOLDL_delete_subset, boolList_of_fdemands_def, EVERY_MEM,
              fdemands_map_FOLDL_delete]
      \\ rw [LIST_REL_EL_EQN, EL_MAP, compute_ALL_DISTINCT_soundness]
      \\ gvs [lookup_thm, FLOOKUP_DEF, demands_map_to_set_def]
      \\ pop_assum $ irule_at Any
      \\ gvs [explode_implode])
  >~ [‘Let a vname e2 e1’]
  >- (rpt gen_tac \\ strip_tac
      \\ rename1 ‘demands_analysis_fun (Bind _ _ c) _ (delete fds _)’
      \\ first_assum $ qspecl_then [‘cexp_size f e1’] assume_tac
      \\ first_x_assum $ qspecl_then [‘cexp_size f e2’] assume_tac
      \\ fs [cexp_size_def]
      \\ first_x_assum $ qspecl_then [‘f’, ‘e2’] assume_tac
      \\ first_x_assum $ qspecl_then [‘f’, ‘e1’] assume_tac
      \\ qabbrev_tac ‘p1 = demands_analysis_fun (Bind vname e2 c) e1 (delete fds (implode vname))’
      \\ qabbrev_tac ‘p2 = demands_analysis_fun c e2 fds’
      \\ PairCases_on ‘p1’ \\ PairCases_on ‘p2’ \\ fs []
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ gvs [demands_map_empty, delete_thm]
      \\ irule_at Any find_Subset
      \\ fs [ctxt_trans_def]
      \\ rename1 ‘find _ (Bind _ _ _) _ (demands_map_to_set p10) _ (fd_to_set p12)’
      \\ Cases_on ‘FLOOKUP (to_fmap p10) (implode vname)’ \\ Cases_on ‘p12’
      \\ fs [ctxt_trans_def, fd_to_set_def, lookup_thm, exp_of_def, op_of_def]
      >>~[‘FLOOKUP _ _ = NONE’]
      >- (irule_at Any find_Let \\ first_x_assum $ irule_at Any
          \\ first_x_assum $ irule_at Any
          \\ gvs [demands_map_delete, FLOOKUP_DEF, dest_fd_SND_def, demands_map_to_set_def]
          \\ rw [] \\ gvs [implode_explode, delete_thm]
          \\ last_x_assum $ assume_tac
          \\ dxrule_then (dxrule_then assume_tac) fdemands_map_delete_soundness
          \\ fs [])
      >- (FULL_CASE_TAC \\ fs [fd_to_set_def]
          \\ irule_at Any find_Let \\ first_x_assum $ irule_at (Pos hd)
          \\ irule_at Any find_smaller_fd \\ first_x_assum $ irule_at Any
          \\ gvs [demands_map_delete, dest_fd_SND_def, demands_map_to_set_def, FLOOKUP_DEF]
          \\ rw [] \\ gvs [implode_explode, delete_thm]
          \\ last_x_assum $ assume_tac
          \\ dxrule_then (dxrule_then assume_tac) fdemands_map_delete_soundness
          \\ fs [])
      >- (irule_at Any find_Let2 \\ irule_at Any find_Seq
          \\ first_x_assum $ irule_at Any \\ first_x_assum $ irule_at Any
          \\ gvs [dest_fd_SND_def, FLOOKUP_DEF]
          \\ qexists_tac ‘[]’ \\ qexists_tac ‘[]’
          \\ rename1 ‘demands_map_to_set (delete p10 (implode vname))’
          \\ qexists_tac ‘demands_map_to_set (delete p10 (implode vname))’
          \\ conj_asm1_tac
          >- (gvs [demands_map_to_set_def] \\ pop_assum $ irule_at Any
              \\ gvs [])
          \\ rw [find_subset_aid]
          >- (dxrule_then (dxrule_then assume_tac) demands_map_delete_soundness
              \\ gvs [])
          \\ last_x_assum $ assume_tac
          \\ dxrule_then (dxrule_then assume_tac) fdemands_map_delete_soundness
          \\ fs [])
      >- (irule_at Any find_Let2 \\ irule_at Any find_Seq
          \\ FULL_CASE_TAC \\ fs [fd_to_set_def]
          \\ first_x_assum $ irule_at Any
          \\ irule_at Any find_smaller_fd \\ first_x_assum $ irule_at Any
          \\ gvs [delete_thm, demands_map_delete_subset, dest_fd_SND_def, demands_map_delete]
          \\ qexists_tac ‘[]’ \\ qexists_tac ‘[]’
          \\ rename1 ‘demands_map_to_set (delete p10 (implode vname))’
          \\ qexists_tac ‘demands_map_to_set (delete p10 (implode vname))’
          \\ conj_asm1_tac
          >- (gvs [demands_map_to_set_def, FLOOKUP_DEF] \\ irule_at Any $ GSYM explode_implode
              \\ gvs [])
          \\ rw [find_subset_aid]
          >- (dxrule_then (dxrule_then assume_tac) demands_map_delete_soundness
              \\ gvs [])
          \\ last_x_assum $ assume_tac
          \\ dxrule_then (dxrule_then assume_tac) fdemands_map_delete_soundness
          \\ fs []))
  >~ [‘Letrec a binds exp’]
  >- (rpt gen_tac
      \\ IF_CASES_TAC
      >- (dxrule_then assume_tac compute_ALL_DISTINCT_soundness
          \\ rename1 ‘demands_analysis_fun (RecBind binds c) _ (FOLDL _ fds (MAP FST binds))’
          \\ qabbrev_tac ‘e = demands_analysis_fun (RecBind binds c) exp
                                                   (FOLDL (λf k. delete f (implode k)) fds (MAP FST binds))’
          \\ PairCases_on ‘e’ \\ gvs [fd_to_set_def, UNZIP3_MAP] \\ strip_tac
          \\ gvs [exp_of_def]
          \\ first_assum $ qspecl_then [‘cexp_size f exp’] assume_tac
          \\ fs [cexp_size_def]
          \\ pop_assum $ qspecl_then [‘f’, ‘exp’] assume_tac
          \\ fs [] \\ pop_assum $ drule_then assume_tac
          \\ gvs [FOLDL_delete_ok, ctxt_trans_def]
          \\ irule_at Any find_Subset
          \\ qexists_tac ‘fdemands_map_to_set (FOLDL (λf k. delete f (implode k)) fds (MAP FST binds))’
          \\ irule_at Any find_Letrec
          \\ irule_at Any adds_demands_soundness
          \\ rpt $ FULL_CASE_TAC
          \\ gvs [EL_MAP, EL_ZIP, MAP_MAP_o, LAMBDA_PROD, combinTheory.o_DEF, ALL_DISTINCT_FST_MAP, EVERY_EL,
                  fdemands_map_FOLDL_delete_subset, FOLDL_delete_ok, fd_to_set_def, dest_fd_SND_def]
          \\ TRY $ irule_at Any find_smaller_fd
          \\ first_x_assum $ irule_at $ Pos hd
          \\ gvs [demands_map_FOLDL_delete_subset]
          \\ rpt $ irule_at Any $ GSYM LENGTH_MAP
          \\ qexists_tac ‘λ(v, e). demands_map_to_set (FST (demands_analysis_fun Nil e (empty compare)))’
          \\ qexists_tac ‘λ(v, e). fd_to_set (SND (SND (demands_analysis_fun Nil e (empty compare))))’
          \\ rename1 ‘demands_analysis_fun _ _ _ = (e0, _, _)’
          \\ qexists_tac ‘demands_map_to_set (FOLDL (λf k. delete f (implode k)) e0 (MAP FST binds))’
          \\ rw [EL_MAP]
                >>~[‘_ ∉ fdemands_map_to_set _’]
          >- (irule fdemands_map_FOLDL_delete \\ gvs [MEM_EL]
              \\ first_assum $ irule_at Any \\ gvs [EL_MAP]
              \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
          >-  (irule fdemands_map_FOLDL_delete \\ gvs [MEM_EL]
               \\ first_assum $ irule_at Any \\ gvs [EL_MAP]
               \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
              >>~[‘FST p = FST _’]
          >- (PairCases_on ‘p’ \\ gvs [])
          >- (PairCases_on ‘p’ \\ gvs [])
          >~[‘_ ∉ demands_map_to_set _’]
          >- (irule demands_map_FOLDL_delete \\ gvs [MEM_EL]
              \\ first_assum $ irule_at Any \\ gvs [EL_MAP]
              \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
             >>~[‘¬MEM _ _’]
          >- (dxrule_then assume_tac demands_map_FOLDL_delete_soundness
              \\ gvs [] \\ strip_tac \\ first_x_assum irule
              \\ gvs [MEM_MAP] \\ first_x_assum $ irule_at Any
              \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
          >- (dxrule_then assume_tac demands_map_FOLDL_delete_soundness
              \\ gvs [] \\ strip_tac \\ first_x_assum irule
              \\ gvs [MEM_MAP] \\ first_x_assum $ irule_at Any
              \\ rename1 ‘_ = FST p’ \\ PairCases_on ‘p’ \\ gvs [])
             >>~[‘(_ ++ _, _) ∈ demands_map_to_set _’]
          >- (qexists_tac ‘[]’ \\ gvs [])
          >- (qexists_tac ‘[]’ \\ gvs [])
             >>~[‘_ ∈ demands_map_to_set _’]
          >- (dxrule_then assume_tac demands_map_FOLDL_delete_soundness \\ gvs [])
          >- (dxrule_then assume_tac demands_map_FOLDL_delete_soundness \\ gvs [])
          \\ rename1 ‘EL i _’
          \\ last_x_assum $ qspecl_then [‘cexp_size f (SND (EL i binds))’] assume_tac
          \\ ‘cexp_size f (SND (EL i binds)) < cexp4_size f binds’
            by (assume_tac cexp_size_lemma \\ gvs [] \\ first_x_assum irule
                \\ gvs [MEM_EL] \\ first_assum $ irule_at Any
                \\ irule_at Any $ PAIR)
          \\ gvs [] \\ pop_assum kall_tac
          \\ pop_assum $ qspecl_then [‘f’, ‘SND (EL i binds)’] assume_tac \\ gvs []
          \\ qabbrev_tac ‘p = demands_analysis_fun Nil (SND (EL i binds)) (empty compare)’
          \\ PairCases_on ‘p’ \\ fs [] \\ first_x_assum $ drule_then assume_tac
          \\ gvs [empty_thm, TotOrd_compare]
          \\ qabbrev_tac ‘expr = EL i binds’ \\ PairCases_on ‘expr’
          \\ gvs [fdemands_map_to_set_def, empty_thm, ctxt_trans_def])
      \\ rw [empty_thm, TotOrd_compare, fd_to_set_def, demands_map_empty]
      \\ gvs [exp_of_def, find_Bottom])
  >~ [‘Case a case_exp s l’]
  >- (gen_tac \\ gen_tac
      \\ rename1 ‘Bind _ _ c’
      \\ first_assum $ qspecl_then [‘cexp_size f case_exp’] assume_tac
      \\ gvs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘case_exp’] assume_tac
      \\ fs []
      \\ pop_assum $ qspecl_then [‘c’, ‘fds’] assume_tac
      \\ qabbrev_tac ‘cexp = demands_analysis_fun c case_exp fds’
      \\ PairCases_on ‘cexp’ \\ gvs []
      \\ rw [empty_thm, TotOrd_compare, demands_map_empty, find_Bottom,
             exp_of_def, MAP_MAP_o, fd_to_set_def]
      \\ gvs [exp_of_def, find_Bottom, combinTheory.o_DEF, LAMBDA_PROD, MAP_MAP_o]
      \\ rename1 ‘Let s _ _’
      \\ irule find_Let
      \\ first_x_assum $ irule_at Any
      \\ irule_at Any find_rows_of
      \\ qexists_tac ‘{}’ \\ qexists_tac ‘NONE’
      \\ rw [LIST_REL_EL_EQN, EL_MAP, dest_fd_SND_def]
      \\ rename1 ‘EL n l’
      \\ qabbrev_tac ‘e = EL n l’
      \\ PairCases_on ‘e’
      \\ fs []
      \\ irule find_Subset
      \\ rename1 ‘demands_analysis_fun (Unfold names s args (Bind s case_exp c)) e'’
      \\ qabbrev_tac ‘p = demands_analysis_fun (Unfold names s args (Bind s case_exp c)) e' (empty compare)’
      \\ PairCases_on ‘p’
      \\ irule_at Any adds_demands_soundness
      \\ first_x_assum $ qspecl_then [‘cexp_size f e'’] assume_tac
      \\ ‘cexp_size f e' < cexp1_size f l’ by metis_tac [cexp_size_lemma, EL_MEM]
      \\ fs []
      \\ pop_assum kall_tac
      \\ pop_assum $ qspecl_then [‘f’, ‘e' ’] assume_tac
      \\ fs [] \\ pop_assum $ dxrule_then assume_tac
      \\ irule_at Any find_Drop_fd
      \\ fs [ctxt_trans_def, TotOrd_compare, fdemands_map_to_set_def, empty_thm]
      \\ last_x_assum $ irule_at Any)
QED

Theorem demands_analysis_fun_soundness:
  ∀(e : α cexp). exp_of e ≈ exp_of (FST (SND (demands_analysis_fun Nil e (empty compare))))
Proof
  rpt gen_tac
  \\ qspecl_then [‘(K 0) : α -> num’, ‘e’, ‘Nil’, ‘empty compare’]
                 assume_tac demands_analysis_soundness_lemma
  \\ qabbrev_tac ‘e' = demands_analysis_fun Nil e (empty compare)’
  \\ PairCases_on ‘e'’
  \\ gvs [fdemands_map_to_set_def, empty_thm, ctxt_trans_def, TotOrd_compare]
  \\ drule find_soundness \\ fs []
QED


val _ = export_theory();

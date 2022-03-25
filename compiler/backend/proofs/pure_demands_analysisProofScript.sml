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
     pure_cexpTheory pure_demandTheory pure_exp_eq_in_ctxtTheory;

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

Definition boolList_of_fdemands_def:
  boolList_of_fdemands m vl = MAP (λv. lookup m (mlstring$implode v) = SOME ()) vl
End

Definition demands_analysis_fun_def:
  (demands_analysis_fun c ((Var a0 a1): 'a cexp) fds =
     let fd = case lookup fds (implode a1) of
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
                  (let ds = FOLDL2 (λm1 (m2, e, _) b. if b then union m1 m2 else m1) m2 eL' fdL in
                     let eL3 = MAP (add_all_demands a0) eL' in
                       if LENGTH fdL ≤ LENGTH argl
                       then (union m1 ds, App a0 f' eL3, NONE)
                       else (m1, App a0 f' eL3, NONE)))) ∧
  (demands_analysis_fun c (Lam a0 vl e) fds =
     let (m, e', fd) = demands_analysis_fun (IsFree vl c) e (empty compare) in
       (empty compare, Lam a0 vl e', SOME (boolList_of_fdemands m vl, empty compare))) ∧
  (demands_analysis_fun c (Let a0 name e1 e2) fds =
     let (m1, e1', fd1) = demands_analysis_fun c e1 fds in
       let (m2, e2', fd2) = demands_analysis_fun (Bind name e1 c) e2 (empty compare) in
         case fd2 of
           | NONE => (empty compare, Let a0 name e1' e2', NONE)
           | SOME (fdL, _) => (empty compare, Let a0 name e1' e2', SOME (fdL, empty compare))) ∧
  (demands_analysis_fun c (Prim a0 Seq [e1; e2]) fds =
     let (m1, e1', fd1) = demands_analysis_fun c e1 fds in
       let (m2, e2', fd2) = demands_analysis_fun c e2 fds in
         (union m1 m2, Prim a0 Seq [e1'; e2'], fd2)) ∧
  (demands_analysis_fun c (Prim a0 Seq _) fds =
   (empty compare, Prim a0 Seq [], NONE)) ∧
  (demands_analysis_fun c (Prim a0 (AtomOp op) el) fds =
     let outL = MAP (λe. demands_analysis_fun c e fds) el in
       let (mL, el1) = UNZIP outL in
         let (el', fdL) = UNZIP el1 in
           let m = FOLDL union (empty compare) mL in
             (m, Prim a0 (AtomOp op) (el': 'a cexp list), NONE)) ∧
  (demands_analysis_fun c (Prim a0 (Cons s) el) fds =
     let el = MAP (λe. add_all_demands a0 (demands_analysis_fun c e fds)) el in
       (empty compare, Prim a0 (Cons s) el, NONE)) ∧
  (demands_analysis_fun c (Letrec a0 binds e) fds =
     let e' = add_all_demands a0 (demands_analysis_fun (RecBind binds c) e (empty compare)) in
       (empty compare, Letrec a0 binds e', NONE)) ∧
  (demands_analysis_fun c (Case a0 e n cases) fds =
   if MEM n (FLAT (MAP (FST o SND) cases))
   then
     (empty compare, Case a0 e n cases, NONE)
   else
     let (m, e', fd) = demands_analysis_fun c e fds in
       let cases' = MAP (λ(name,args,ce). (name, args,
                                           adds_demands a0 (demands_analysis_fun
                                                (Unfold name n args (Bind n e c)) ce (empty compare)) args)) cases in
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
  \\ fs []
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

Theorem fdemands_map_to_set_soundness:
  ∀fds n x. map_ok fds ⇒
            (lookup fds (implode n) = SOME x ⇔ (n, x) ∈ fdemands_map_to_set fds)
Proof
  rw [lookup_thm, FLOOKUP_DEF, fdemands_map_to_set_def] >>
  eq_tac >> rw [] >> gvs [implode_explode] >>
  pop_assum $ irule_at Any >> gvs [explode_implode]
QED
        
Theorem demands_analysis_soundness_lemma:
  ∀(f: α -> num) (e: α cexp) c fds m e' fd.
    demands_analysis_fun c e fds = (m, e', fd) ∧ map_ok fds
    ⇒ find (exp_of e) (ctxt_trans c) (fdemands_map_to_set fds)
         (demands_map_to_set m) (exp_of e') (fd_to_set fd) ∧
            map_ok m ∧ cmp_of m = compare
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
              find_Var2, fdemands_map_to_set_soundness])
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
              \\ irule find_Eq \\ irule exp_eq_IMP_exp_eq_in_ctxt
              \\ fs [exp_of_def, op_of_def, eval_wh_IMP_exp_eq,
                     eval_wh_def, eval_wh_to_def, subst_def])
          \\ rename1 ‘e1::e2::t’
          \\ Cases_on ‘t’ >~ [‘Prim a Seq (e1::e2::e3::t)’]
          >- (rw [demands_analysis_fun_def, empty_thm, fd_to_set_def, demands_map_empty,
                 TotOrd_compare, exp_of_def, op_of_def]
              \\ irule find_Eq \\ irule exp_eq_IMP_exp_eq_in_ctxt
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
          \\ gvs [exp_of_def, op_of_def, demands_analysis_fun_def, UNZIP_MAP,
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
      \\ cheat
      \\ irule find_Apps
      \\ fs []
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
      \\ Cases_on ‘p0’
      \\ irule_at Any add_all_demands_soundness
      \\ fs [cmp_of_def, TotOrd_compare]
      \\ qexists_tac ‘{}’
      \\ fs [])
  >~ [‘Lam a namel e’]
  >- (rw []
      \\ first_assum $ qspecl_then [‘cexp_size f e’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘e’] assume_tac
      \\ rename1 ‘demands_analysis_fun (IsFree namel c) _’
      \\ qabbrev_tac ‘p = demands_analysis_fun (IsFree namel c) e (empty compare)’
      \\ PairCases_on ‘p’ \\ fs [empty_thm, TotOrd_compare]
      \\ first_x_assum $ drule_then assume_tac
      \\ gvs [exp_of_def]
      \\ cheat
      \\ irule find_Lams
      \\ irule_at Any add_all_demands_soundness
      \\ fs [TotOrd_compare, ctxt_trans_def])
  >~ [‘Let a vname e2 e1’]
  >- (rw []
      \\ rename1 ‘demands_analysis_fun (Bind _ _ c) _’
      \\ first_assum $ qspecl_then [‘cexp_size f e1’] assume_tac
      \\ first_x_assum $ qspecl_then [‘cexp_size f e2’] assume_tac
      \\ fs [cexp_size_def]
      \\ first_x_assum $ qspecl_then [‘f’, ‘e2’] assume_tac
      \\ first_x_assum $ qspecl_then [‘f’, ‘e1’] assume_tac
      \\ qabbrev_tac ‘p1 = demands_analysis_fun (Bind vname e2 c) e1 (empty compare)’
      \\ qabbrev_tac ‘p2 = demands_analysis_fun c e2 fds’
      \\ PairCases_on ‘p1’ \\ rename1 ‘(p10, p11, p12)’ \\ Cases_on ‘p12’
      \\ TRY (rename1 ‘(_, _, SOME p12)’ \\ PairCases_on ‘p12’)
      \\ PairCases_on ‘p2’ \\ fs []
      \\ last_x_assum $ drule_then assume_tac
      \\ last_x_assum $ drule_then assume_tac
      \\ gvs [demands_map_empty, empty_thm, TotOrd_compare]
      \\ irule find_Subset
      \\ rw [exp_of_def, fd_to_set_def]
      \\ Cases_on ‘FLOOKUP (to_fmap p10) (implode vname)’
      \\ fs [] >>~[‘FLOOKUP _ _ = NONE’]
      >- (irule_at Any find_Let \\ first_x_assum $ irule_at Any
          \\ fs [ctxt_trans_def] \\ first_x_assum $ irule_at Any
          \\ gvs [fdemands_map_to_set_def, empty_thm, demands_map_to_set_def, FLOOKUP_DEF]
          \\ rw [] \\ gvs [implode_explode])
      >- (irule_at Any find_smaller_fd \\ cheat)
      >- (irule_at Any find_Let2 \\ fs [ctxt_trans_def]
          \\ first_x_assum $ irule_at Any \\ first_x_assum $ irule_at Any
          \\ gvs [fdemands_map_to_set_def, empty_thm]
          \\ qexists_tac ‘[]’ \\ qexists_tac ‘{}’
          \\ gvs [demands_map_to_set_def, FLOOKUP_DEF]
          \\ pop_assum $ irule_at Any \\ gvs [implode_explode])
      >- (irule_at Any find_smaller_fd \\ cheat)
  >~ [‘Letrec a binds exp’]
  >- (rpt gen_tac \\ rename1 ‘demands_analysis_fun (RecBind binds c) _ _’
      \\ qabbrev_tac ‘e = demands_analysis_fun (RecBind binds c) exp (empty compare)’
      \\ PairCases_on ‘e’ \\ fs [fd_to_set_def]
      \\ irule find_Subset
      \\ irule_at Any find_Letrec
      \\ first_x_assum $ qspecl_then [‘cexp_size f exp’] assume_tac
      \\ fs [cexp_size_def]
      \\ pop_assum $ qspecl_then [‘f’, ‘exp’] assume_tac
      \\ fs [] \\ pop_assum $ drule_then assume_tac
      \\ fs [ctxt_trans_def]
      \\ rename1 ‘(e0, e1, e2)’ \\ Cases_on ‘e0’
      \\ irule_at Any add_all_demands_soundness
      \\ qexists_tac ‘{}’
      \\ fs [demands_map_to_set_def, cmp_of_def, TotOrd_compare,
             fdemands_map_to_set_def, empty_thm]
      \\ first_x_assum $ irule_at Any \\ gvs []
      \\ rename1 ‘LIST_REL _ l’ \\ qexists_tac ‘l’
      \\ rw [LIST_REL_EL_EQN]
      \\ rename1 ‘_ p _’ \\ PairCases_on ‘p’ \\ gvs [exp_eq_refl])
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
(*      \\ pop_assum $ qspecl_then [‘λnames args ce. adds_demands a (demands_analysis_fun (Unfold names s args (Bind s case_exp c)) ce) args’] assume_tac
 *)   \\ irule find_Let
      \\ first_x_assum $ irule_at Any
      \\ irule_at Any find_rows_of
      \\ qexists_tac ‘{}’ \\ qexists_tac ‘NONE’
      \\ rw [LIST_REL_EL_EQN, EL_MAP]
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
      \\ fs [ctxt_trans_def, demands_map_to_set_def, fdemands_map_to_set_def, empty_thm]
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
  \\ gvs [fdemands_map_to_set_def, empty_thm, ctxt_trans_def]
  \\ drule find_soundness \\ fs []
QED


val _ = export_theory();

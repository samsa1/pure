structure exp_eqSimps =
struct


open simpLib boolSimps boolLib pure_congruenceTheory
structure Parse =
struct
  open Parse
  val (Type,Term) = parse_from_grammars pure_congruence_grammars
end

val intro_cong = Q.prove(
  ‘a1 ≅ a2 ⇒ b1 ≅ b2 ⇒ (a1 ≅ b1 ⇔ a2 ≅ b2)’,
  metisLib.METIS_TAC[exp_eq_sym, exp_eq_trans]);

val impi = REWRITE_RULE [GSYM AND_IMP_INTRO]

val PAIR_REL_REFL' = Q.prove(
  ‘(∀x. R1 x x) ∧ (∀y. R2 y y) ⇒ ∀p. (R1 ### R2) p p’,
  rpt strip_tac >> Cases_on ‘p’ >> simp[quotient_pairTheory.PAIR_REL]);

val PAIR_REL_TRANS' = Q.prove(
  ‘(∀x y z. R1 x y ∧ R1 y z ⇒ R1 x z) ∧ (∀a b c. R2 a b ∧ R2 b c ⇒ R2 a c) ⇒
   ∀p1 p2 p3. (R1 ### R2) p1 p2 ∧ (R1 ### R2) p2 p3 ⇒ (R1 ### R2) p1 p3’,
  rpt strip_tac >> map_every Cases_on [‘p1’, ‘p2’, ‘p3’] >>
  gs[quotient_pairTheory.PAIR_REL] >> metis_tac[]);

val PAIR_REL_SYM' = Q.prove(
  ‘(∀x y. R1 x y ⇒ R1 y x) ∧ (∀a b. R2 a b ⇒ R2 b a) ⇒
   ∀p1 p2. (R1 ### R2) p1 p2 ⇒ (R1 ### R2) p2 p1’,
  rpt strip_tac >> map_every Cases_on [‘p1’, ‘p2’] >>
  gs[quotient_pairTheory.PAIR_REL]);


Overload lrt = “LIST_REL ($= ### $≅) : (string # exp) list -> (string # exp) list -> bool”

Theorem LIST_REL_PAIR_REL_E:
  LIST_REL (R1 ### R2) l1 l2 ⇒
  LIST_REL R1 (MAP FST l1) (MAP FST l2) ∧
  LIST_REL R2 (MAP SND l1) (MAP SND l2)
Proof
  Induct_on ‘LIST_REL’ >>
  simp[pairTheory.FORALL_PROD, quotient_pairTheory.PAIR_REL]
QED

Theorem letrec_cong':
  e1 ≅ e2 ⇒ lrt bs1 bs2 ⇒ Letrec bs1 e1 ≅ Letrec bs2 e2
Proof
  rpt strip_tac >> drule LIST_REL_PAIR_REL_E >> simp[exp_eq_Letrec_cong]
QED

val EXPEQ_ss = let
  val rsd = {refl = exp_eq_refl, trans = exp_eq_trans,
             weakenings = [intro_cong],
             subsets = [],
             rewrs = [beta_equality, exp_eq_Add]}
  val frag1 = relsimp_ss rsd
  val congs = SSFRAG {dprocs = [], ac = [], rewrs = [], name = NONE,
                      congs = [exp_eq_Lam_cong, impi exp_eq_App_cong,
                               letrec_cong'],
                      convs = [],
                      filter = NONE}
in
  merge_ss [frag1, congs] |> name_ss "EXPEQ_ss"
end


val lreq_refl = Q.prove(
  ‘lrt xs xs’,
  simp[listTheory.EVERY2_refl,PAIR_REL_REFL',exp_eq_refl]);
val lreq_trans = Q.prove(
  ‘lrt x y ∧ lrt y z ⇒ lrt x z’,
  MATCH_MP_TAC pure_miscTheory.LIST_REL_TRANS >>
  MATCH_MP_TAC PAIR_REL_TRANS' >> simp[] >>
  ACCEPT_TAC exp_eq_trans);
val lreq_sym = Q.prove(
  ‘lrt x y ⇒ lrt y x’,
  MATCH_MP_TAC $ iffLR LIST_REL_SYM >>
  simp[EQ_IMP_THM, FORALL_AND_THM, SF CONJ_ss] >> rpt gen_tac >>
  MATCH_MP_TAC PAIR_REL_SYM' >> simp[exp_eq_sym]);
val lrintro_cong = Q.prove(
  ‘lrt a1 a2 ∧ lrt b1 b2 ⇒ (lrt a1 b1 ⇔ lrt a2 b2)’,
  metisLib.METIS_TAC[lreq_sym, lreq_trans]);

val lr_cons_cong = Q.prove(
  ‘k1 = k2 ⇒ x ≅ y ⇒ lrt xs ys ⇒ lrt ((k1,x)::xs) ((k2,y)::ys)’,
  rpt strip_tac >>
  simp[listTheory.LIST_REL_CONS1, quotient_pairTheory.PAIR_REL]);

val LREXPEQ_ss = let
  val rsd = {refl = lreq_refl, trans = lreq_trans,
             weakenings = [lrintro_cong],
             subsets = [],
             rewrs = []}
  val frag1 = relsimp_ss rsd
  val congs = SSFRAG {dprocs = [], ac = [], rewrs = [], name = NONE,
                      congs = [lr_cons_cong],
                      convs = [],
                      filter = NONE}
in
  merge_ss [frag1, congs] |> name_ss "LREXPEQ_ss"
end


val doeswork =
  SIMP_CONV (srw_ss() ++ EXPEQ_ss)
    [pure_expTheory.closed_def, pure_expTheory.freevars_def,
     pure_exp_lemmasTheory.subst1_def]
    “X ≅ Let x (Lit (Int 3)) (Prim (AtomOp Add) [Var x; Lit (Int 4)])”;

  (* sadly doesn't work
SIMP_CONV (srw_ss() ++ EXPEQ_ss ++ LREXPEQ_ss)
  [pure_expTheory.closed_def, pure_expTheory.freevars_def,
   pure_exp_lemmasTheory.subst1_def]
  “Y ≅ Letrec [(f, Prim (AtomOp Add) [Lit (Int 4); Lit(Int 7)])] (Var x)”
*)


end (* struct *)

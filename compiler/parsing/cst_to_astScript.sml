open HolKernel Parse boolLib bossLib;

open pureNTTheory pureASTTheory tokenUtilsTheory grammarTheory
local open precparserTheory in end

val _ = new_theory "cst_to_ast";

Overload lift[local] = “option$OPTION_MAP”
Overload "'"[local] = “λf a. OPTION_BIND a f”

Definition tokcheck_def:
  tokcheck pt tok <=> destTOK ' (destLf pt) = SOME tok
End

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"
Overload monad_bind = “λa f. OPTION_BIND a f”

Overload ptsize = “parsetree_size (K 0) (K 0) (K 0)”;
Overload ptlsize = “parsetree1_size (K 0) (K 0) (K 0)”;

Definition mkFunTy_def:
  mkFunTy [] = tyOp "Bool" [] ∧ (* bogus but should never occur *)
  mkFunTy [ty] = ty ∧
  mkFunTy (ty::rest) = tyOp "Fun" [ty; mkFunTy rest]
End

Definition grab_def:
  grab f [] = SOME ([], []) ∧
  grab f (h::t) =
  do
    v <- f h;
    (vs, tail) <- grab f t;
    SOME (v::vs, tail)
  od ++ SOME([], h::t)
End

Theorem grab_EQ_SOME_APPEND:
  ∀xs res xs'. grab f xs = SOME (res, xs') ⇒
               ∃px. xs = px ++ xs'
Proof
  Induct_on ‘xs’ >>
  simp[grab_def, miscTheory.option_eq_some, DISJ_IMP_THM, PULL_EXISTS,
       pairTheory.FORALL_PROD] >> rpt strip_tac >>
  first_x_assum $ drule_then strip_assume_tac >> rw[]
QED

Theorem grab_cong[defncong]:
  ∀l1 l2 f1 f2. l1 = l2 ∧ (∀e. MEM e l2 ⇒ f1 e = f2 e) ⇒
                grab f1 l1 = grab f2 l2
Proof
  simp[] >> Induct >>
  simp[grab_def, DISJ_IMP_THM, FORALL_AND_THM, miscTheory.option_eq_some]>>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Definition grabPairs_def[simp]:
  grabPairs vf opf A [] = SOME (REVERSE A) ∧
  grabPairs vf opf A [_] = NONE ∧
  grabPairs vf opf A (pt1 :: pt2 :: rest) =
  do
    opv <- opf pt1 ;
    v <- vf pt2 ;
    grabPairs vf opf (INR v :: INL opv :: A) rest
  od
End

Theorem grabPairs_cong[defncong]:
  ∀opf1 opf2 l1 l2 vf1 vf2 A1 A2 .
    opf1 = opf2 ∧ l1 = l2 ∧ (∀e. MEM e l2 ⇒ vf1 e = vf2 e) ∧ A1 = A2 ⇒
    grabPairs vf1 opf1 A1 l1 = grabPairs vf2 opf2 A2 l2
Proof
  simp[] >> qx_genl_tac [‘opf2’, ‘l2’, ‘vf1’, ‘vf2’] >>
  completeInduct_on ‘LENGTH l2’ >>
  gs[SF DNF_ss] >> Cases_on ‘l2’ >> simp[DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >> gvs[] >> rename [‘grabPairs _ _ _ (h::t)’] >>
  Cases_on ‘t’ >> simp[]
QED

Definition astType_def:
  astType nt (Lf _) = NONE ∧
  (astType nt1 (Nd nt2 args) =
   if FST nt2 ≠ INL nt1 then NONE
   else if nt1 = nTyBase then
     case args of
     | [] => NONE
     | [pt] =>
         do
           s <- destAlphaT ' (destTOK ' (destLf pt));
           c1 <- oHD s;
           if isUpper c1 then SOME $ tyOp s []
           else SOME $ tyVar s
         od
     | [ld; rd] => do assert(tokcheck ld LparT ∧ tokcheck rd RparT) ;
                      SOME (tyTup [])
                   od
     | [ld; typt; rd] =>
         do
           t <- destTOK ' (destLf ld);
           ty <- astType nTy typt;
           if t = LparT then
             do
               assert(tokcheck rd RparT);
               SOME ty
             od
           else if t = LbrackT then
             do
               assert(tokcheck rd RbrackT);
               SOME $ tyOp "List" [ty]
             od
           else NONE
         od
     | (ld :: pt1 :: rest) =>
         do
           assert(tokcheck ld LparT);
           ty1 <- astType nTy pt1;
           (tys, rest') <- astSepType CommaT nTy rest;
           assert(LIST_REL tokcheck rest' [RparT]);
           SOME $ tyTup (ty1::tys)
         od
   else if nt1 = nTy then
     case args of
       [] => NONE
     | pt::rest =>
         do
           ty1 <- astType nTyApp pt ;
           (tys, rest') <- astSepType ArrowT nTyApp rest;
           SOME $ mkFunTy (ty1::tys)
         od
   else if nt1 = nTyApp then
     case args of
     | [] => NONE
     | [pt] => astType nTyBase pt
     | op_pt :: rest =>
         do
           opnm <- destAlphaT ' (destTOK ' (destLf op_pt)) ;
           ty_args <- astTypeBaseL rest ;
           SOME $ tyOp opnm ty_args
         od
   else
     NONE) ∧
  (astSepType sept nt [] = SOME ([], [])) ∧
  (astSepType sept nt [pt] = SOME ([], [pt])) ∧
  (astSepType sept nt (pt1::pt2::rest) =
       do
         assert(tokcheck pt1 sept);
         r <- astType nt pt2 ;
         (rs, pts) <- astSepType sept nt rest;
         SOME (r::rs, pts)
       od ++ SOME ([], pt1::pt2::rest)) ∧
  (astTypeBaseL [] = SOME []) ∧
  (astTypeBaseL (pt::rest) = do
     ty1 <- astType nTyBase pt ;
     tys <- astTypeBaseL rest ;
     SOME (ty1 :: tys)
   od)
Termination
  WF_REL_TAC ‘measure (λs. case s of
                             INL (_, pt) => ptsize pt
                           | INR (INL (_, _, pts)) => ptlsize pts
                           | INR (INR pts) => ptlsize pts)’ >> rw[]
End


Definition astLit_def:
  astLit (Lf _) = NONE ∧
  astLit (Nd nt args) =
  if FST nt ≠ INL nLit then NONE
  else
    case args of
      [] => NONE
    | [pt] => lift litInt $ destIntT ' (destTOK ' (destLf pt))
    | _ => NONE
End

Definition astOp_def:
  astOp pt = do
               t <- destTOK ' (destLf pt) ;
               destSymbolT t ++ (if t = StarT then SOME "*"
                                 else if t = ColonT then SOME ":"
                                 else NONE)
             od
End

Theorem SUM_MAP_EL_lemma:
  ∀xs i. i < LENGTH xs ⇒ f (EL i xs) ≤ SUM (MAP f xs)
Proof
  Induct >> simp[] >> Cases_on ‘i’ >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Definition astPat_def:
  astPat _ (Lf _) = NONE ∧
  (astPat nt1 (Nd nt2 args) =
   if INL nt1 ≠ FST nt2 then NONE
   else if nt1 = nAPat then
     case args of
       [pt] => do
                vnm <- destAlphaT ' (destTOK ' (destLf pt));
                SOME $ patVar vnm
              od ++ (lift patLit $ astLit pt)
     | _ => NONE
   else NONE)
End

Datatype: associativity = Left | Right | NonAssoc
End

(* Table 4.1 from
     https://www.haskell.org/onlinereport/haskell2010/haskellch4.html
   omitting alpha-ids in backquotes
*)
val tabinfo = [
  (".", (9, “Right”)),
  ("^", (8, “Right”)),
  ("^^", (8, “Right”)),
  ("**", (8, “Right”)),
  ("*", (7, “Left”)),
  ("/", (7, “Left”)),
  ("+", (6, “Left”)),
  ("-", (6, “Left”)),
  (":", (5, “Right”)),
  ("++", (5, “Right”)),
  ("==", (4, “NonAssoc”)),
  ("/=", (4, “NonAssoc”)),
  ("<", (4, “NonAssoc”)),
  ("<=", (4, “NonAssoc”)),
  (">", (4, “NonAssoc”)),
  (">=", (4, “NonAssoc”)),
  ("&&", (3, “Right”)),
  ("||", (2, “Right”)),
  (">>", (1, “Left”)),
  (">>=", (1, “Left”)),
  ("$", (0, “Right”)),
  ("$!", (0, “Right”))
]
val s = mk_var("s", “:string”)
val def = List.foldr (fn ((t,(i,tm)), A) =>
              mk_cond(mk_eq(s,stringSyntax.fromMLstring t),
                      optionSyntax.mk_some
                         (pairSyntax.mk_pair(
                           numSyntax.mk_numeral (Arbnum.fromInt i), tm)),
                      A))
            “NONE : (num # associativity) option”
            tabinfo
Definition tokprec_def:
tokprec s = ^def
End

Definition tok_action_def:
  tok_action (INL stktok, INL inptok) =
  do (stkprec, stka) <- tokprec stktok ;
     (inpprec, inpa) <- tokprec inptok ;
     if inpprec < stkprec then SOME Reduce
     else if stkprec < inpprec then SOME Shift
     else if stka ≠ inpa ∨ stka = NonAssoc then NONE
     else if stka = Left then SOME Reduce
     else SOME Shift
  od ∧
  tok_action _ = NONE
End

Definition mkSym_def:
  mkSym s = THE (do
                  c1 <- oHD s ;
                  if isUpper c1 then SOME $ expCon s []
                  else if isAlpha c1 ∨ c1 ≠ #":" then SOME $ expVar s
                  else SOME $ expCon s []
                od ++ SOME (expVar s))
End

Definition mkApp_def:
  mkApp f args =
  case f of
    expCon s args0 => expCon s (args0 ++ args)
  | _ => FOLDL expApp f args
End

Definition handlePrecs_def:
  handlePrecs sumlist =
  precparser$precparse
  <| rules := tok_action ;
     reduce :=
       (λa1 op a2. SOME $ mkApp (mkSym $ OUTL op) [a1; a2]);
     lift := OUTR ;
     isOp := ISL;
     mkApp := (λa b. SOME $ expApp a b) (* won't get called *)
  |> ([], sumlist)
End


Theorem list_size_MAP_SUM:
  list_size f l = LENGTH l + SUM (MAP f l)
Proof
  Induct_on‘l’ >> simp[listTheory.list_size_def]
QED

Theorem ptsize_nonzero[simp]:
  0 < ptsize a
Proof
  Cases_on ‘a’ >> simp[parsetree_size_def]
QED

Definition astExp_def:
  (astExp _ (Lf _) = NONE) ∧
  (astExp nt1 (Nd nt2 args) =
   if INL nt1 ≠ FST nt2 then NONE
   else if nt1 = nAExp then
     case args of
       [] => NONE
     | [pt] =>
         do
           vnm <- destAlphaT ' (destTOK ' (destLf pt)) ;
           SOME $ mkSym vnm
         od ++ (lift expLit $ astLit pt)
     | [lp;rp] =>
         do
           assert (tokcheck lp LparT ∧ tokcheck rp RparT);
           SOME $ expTup []
         od ++
         do assert (tokcheck lp LbrackT ∧ tokcheck rp RbrackT);
            SOME $ pNIL
         od
     | ld :: pt1 :: rest =>
         do rd <- (do assert (tokcheck ld LparT); SOME RparT; od) ++
                  (do assert (tokcheck ld LbrackT); SOME RbrackT; od) ;
            ast1 <- astExp nExp pt1;
            asts <- astSepExp rd rest ;
            if rd = RparT then
              if NULL asts then SOME ast1
              else SOME $ expTup (ast1::asts)
            else SOME (FOLDR pCONS pNIL (ast1::asts))
         od
   else if nt1 = nExp then
     case args of
       [pt] => astExp nIExp pt
     | pt1::rest =>
         do
           assert (tokcheck pt1 IfT ∧ LENGTH rest = 5 ∧
                   LIST_REL (λP pt. P pt) [K T; flip tokcheck ThenT; K T;
                                           flip tokcheck ElseT; K T]
                            rest);
           gd_e <- astExp nExp ' (oEL 0 rest);
           then_e <- astExp nExp ' (oEL 2 rest);
           else_e <- astExp nExp ' (oEL 4 rest);
           SOME $ expIf gd_e then_e else_e;
         od ++
         do
           assert (tokcheck pt1 (SymbolT "\\"));
           (pats,tail) <- grab (astPat nAPat) rest;
           assert (LIST_REL (λP pt. P pt) [flip tokcheck ArrowT; K T] tail);
           body_e <- astExp nExp ' (oEL 1 tail);
           SOME $ FOLDR expAbs body_e pats
         od
     | _ => NONE
   else if nt1 = nIExp then
     case args of
     | [] => NONE
     | pt :: rest => do
                      v <- astExp nFExp pt ;
                      preclist <- grabPairs (astExp nFExp2) astOp [INR v] rest ;
                      handlePrecs preclist
                    od
   else if nt1 = nFExp2 then
     case args of
     | [] => NONE
     | [pt] => astExp nExp pt ++ astExp nFExp pt
     | _ => NONE
   else if nt1 = nFExp then
     case args of
       [] => NONE
     | fpt :: rest =>
         do
           f_e <- astExp nAExp fpt;
           (aes, tail) <- grab (astExp nAExp) rest;
           assert (NULL tail);
           SOME $ mkApp f_e aes
         od
   else
     NONE) ∧
  (astSepExp rd [] = NONE) ∧
  (astSepExp rd [pt] = do assert (tokcheck pt rd); SOME [] od) ∧
  (astSepExp rd (pt1 :: pt2 :: rest) =
   do
     assert (tokcheck pt1 CommaT);
     ast <- astExp nExp pt2 ;
     asts <- astSepExp rd rest ;
     SOME (ast :: asts)
   od)
Termination
  WF_REL_TAC ‘measure (λs. case s of
                             INL (_, pt) => ptsize pt
                           | INR (_, pts) => 1 + SUM (MAP ptsize pts))’ >>
  simp[miscTheory.LLOOKUP_EQ_EL, parsetree_size_eq, list_size_MAP_SUM] >>
  rpt strip_tac >> simp[arithmeticTheory.ZERO_LESS_ADD] >>
  TRY (drule_then strip_assume_tac grab_EQ_SOME_APPEND >>
       pop_assum (assume_tac o Q.AP_TERM ‘SUM o MAP ptsize’) >>
       gs[listTheory.SUM_APPEND]) >>
  qmatch_goalsub_abbrev_tac ‘ptsize (EL i ptl)’ >>
  ‘ptsize (EL i ptl) ≤ SUM (MAP ptsize ptl)’
    suffices_by simp[Abbr‘i’] >>
  simp[Abbr‘i’, Abbr‘ptl’, SUM_MAP_EL_lemma]
End

val _ = export_theory();

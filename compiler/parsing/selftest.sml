open HolKernel Parse boolLib bossLib
open cst_to_astTheory purePEGTheory testutils

val errcount = ref 0
val _ = diemode := Remember errcount

val _ = computeLib.add_funs [lexer_funTheory.get_token_def,
                             listTheory.LIST_REL_def,
                             ASCIInumbersTheory.s2n_compute,
                             numposrepTheory.l2n_def]

val gencst = “λn s. ispeg_exec purePEG (nt (INL n) I lrOK) (lexer_fun s)
                             lpTOP [] NONE [] done failed”

val fullparse =
    “λn s f. case ispeg_exec purePEG (nt (INL n) I lrOK) (lexer_fun s)
                             lpTOP [] NONE [] done failed
            of
               Result (Success [] [pt] _ _) => f pt
             | _ => (NONE : α option)”;

fun KNL s = String.translate (fn #"\n" => "\\n" | c => str c) s
fun checkrand t =
    rand t handle HOL_ERR _ =>
    raise mk_HOL_ERR "" "" "Got NONE"
fun fptest (nt, s, cf, exp) =
    (tprint ("Parsing (" ^ term_to_string nt ^ ") \"" ^ KNL s ^ "\"");
     require_msg (check_result (aconv exp)) term_to_string
                 (checkrand o rhs o concl o EVAL)
                 (list_mk_icomb(fullparse,
                                [nt,stringSyntax.fromMLstring s,
                                 inst [alpha |-> “:locs”] cf])))

val threetimesfour = “expApp (expApp (expVar "*") (expLit (litInt 3)))
                             (expLit (litInt 4))”
val _ = temp_overload_on("𝕀", “λi. expLit (litInt i)”);
val _ = app fptest [
  (“nTy”, "[Int]", “astType nTy”, “listTy intTy”),
  (“nTy”, "a -> B", “astType nTy”, “funTy (tyVar "a") (tyOp "B" [])”),
  (“nTy”, "(Tree a, B)", “astType nTy”, “tyTup [tyOp "Tree" [tyVar "a"];
                                                tyOp "B" []]”),
  (“nTy”, "[Int -> ()]", “astType nTy”, “listTy (funTy intTy $ tyTup [])”),
  (“nExp”, "f 2 x", “astExp nExp”, “‹f› ⬝ 𝕀 2 ⬝ ‹x›”),
  (“nExp”, "\\x y -> y x", “astExp nExp”,
   “expAbs (patVar "x") (expAbs (patVar "y") (‹y› ⬝ ‹x›))”),
  (“nExp”, " if p x \nthen 1 else 2", “astExp nExp”,
   “expIf (expApp (expVar "p") (expVar "x")) (𝕀 1) (𝕀 2)”),
  (“nExp”, "z + if p x \nthen 1 else 2", “astExp nExp”,
   “‹+› ⬝ ‹z› ⬝ expIf (expApp (expVar "p") (expVar "x")) (𝕀 1) (𝕀 2)”),
  (“nExp”, "3 * 4 + 6", “astExp nExp”, “‹+› ⬝ (‹*› ⬝ 𝕀 3 ⬝ 𝕀 4) ⬝ 𝕀 6”),
  (“nExp”, "6 + 3 * 4", “astExp nExp”, “‹+› ⬝ 𝕀 6 ⬝ (‹*› ⬝ 𝕀 3 ⬝ 𝕀 4)”),
  (“nExp”, "(6 + 3) * 4", “astExp nExp”, “‹*› ⬝ (‹+› ⬝ 𝕀 6 ⬝ 𝕀 3) ⬝ 𝕀 4”),
  (“nExp”, "h1:h2:t", “astExp nExp”, “‹h1› ::ₚ ‹h2› ::ₚ ‹t›”),
  (“nExp”, "1+3:t", “astExp nExp”, “(‹+› ⬝ 𝕀 1 ⬝ 𝕀 3) ::ₚ ‹t›”),
  (“nExp”, "C () 3", “astExp nExp”, “expCon "C" [expTup []; 𝕀 3]”),
  (“nExp”, "C (x+y) 3", “astExp nExp”, “expCon "C" [‹+› ⬝ ‹x› ⬝ ‹y›; 𝕀 3]”),
  (“nExp”, "C (x,y) 3", “astExp nExp”, “expCon "C" [expTup [‹x›; ‹y›]; 𝕀 3]”),
  (“nExp”, "D [] 3", “astExp nExp”, “expCon "D" [pNIL; 𝕀 3]”),
  (“nExp”, "f [x,y] 3", “astExp nExp”,
   “‹f› ⬝ (‹x› ::ₚ ‹y› ::ₚ pNIL) ⬝ 𝕀 3”)
]

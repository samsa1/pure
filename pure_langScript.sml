
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory bagTheory;


val _ = new_theory "pure_lang";


(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)
Type fname = “:string”  (* function name *)


(*configuration record for the parametric atoms.

   parAtomOp:
     It takes an element of type 'a (from AtomOp) and returns a
     function that takes a "'b list" element and SOME b if the
     number of arguments is correct, NONE otherwise

*)
Datatype:
  conf = <| parAtomOp  : 'a -> 'b list -> 'b option; |>
End

Datatype:
  op = If               (* if-expression                            *)
     | Cons string      (* datatype constructor                     *)
     | IsEq string num  (* compare cons tag and num of args         *)
     | Proj string num  (* reading a field of a constructor         *)
     | AtomOp 'a        (* primitive parametric operator over Atoms *)
     | Lit 'b           (* parametric literal Atom                  *)
End

Datatype:
  exp = Var vname                     (* variable                   *)
      | Prim (('a,'b) op) (exp list)  (* primitive operations       *)
      | App exp exp                   (* function application       *)
      | Lam vname exp                 (* lambda                     *)
      | Letrec ((fname # vname # exp) list) exp   (* mut. rec. funs *)
      | Case exp vname ((vname # vname list # exp) list) (*case pat.*)
End

(* some abbreviations *)
Overload Let  = “λs x y. App (Lam s y) x”      (* let-expression    *)
Overload If   = “λx y z. Prim If [x; y; z]”    (* If   at exp level *)
Overload Lit  = “λa. Prim (Lit a) []”           (* Lit at exp level *)
Overload Cons = “λs. Prim (Cons s)”            (* Cons at exp level *)
Overload IsEq = “λs n x. Prim (IsEq s n) [x]”  (* IsEq at exp level *)
Overload Proj = “λs i x. Prim (Proj s i) [x]”  (* Proj at exp level *)
Overload Fail = “Prim (Lit ARB) [Prim (Lit ARB)[]]” (* causes Error *)


(* a call-by-name semantics in a denotational semantics style *)

(* would like to have:
Codatatype:
  ('a,'b) v = Atom 'b
          | Constructor string (('a,'b) v) list)
          | Closure vname ('a exp)
          | Diverge
          | Error
End
*)

Datatype:
  v_prefix = Atom' 'b
           | Constructor' string
           | Closure' vname (('a,'b) exp)
           | Diverge'
           | Error'
End

Type v = “:(('a,'b) v_prefix) ltree”;

Overload Atom = “λb. Branch (Atom' b) LNIL”;
Overload Constructor = “λs ts. Branch (Constructor' s) ts”;
Overload Constructor = “λs ts. Branch (Constructor' s) (fromList ts)”;
Overload Closure = “λs x. Branch (Closure' s x) LNIL”;
Overload Diverge = “Branch Diverge' LNIL”;
Overload Error = “Branch Error' LNIL”;
Overload True  = “Branch (Constructor' "True" ) LNIL”;
Overload False = “Branch (Constructor' "False") LNIL”;

Definition dest_Closure_def:
  dest_Closure x =
    case x of Closure s x => SOME (s,x) | _ => NONE
End

Theorem dest_Closure_Closure[simp]:
  dest_Closure (Closure s x) = SOME (s,x)
Proof
  fs [dest_Closure_def]
QED

Theorem dest_Closure_Closure_IMP:
  dest_Closure v = SOME (s,x) ⇒ v = Closure s x
Proof
  rw [] \\ Cases_on ‘v’ \\ Cases_on ‘a’ \\ Cases_on ‘ts’ \\ gs[dest_Closure_def]
QED

Triviality exp_size_lemma:
  (∀xs     a. MEM      a  xs ⇒ exp_size (K 0) (K 0) a < exp7_size (K 0) (K 0) xs) ∧
  (∀xs x y a. MEM (x,y,a) xs ⇒ exp_size (K 0) (K 0) a < exp3_size (K 0) (K 0) xs) ∧
  (∀xs x y a. MEM (x,y,a) xs ⇒ exp_size (K 0) (K 0) a < exp1_size (K 0) (K 0) xs)
Proof
  conj_tac \\ TRY conj_tac \\ Induct \\ rw [] \\ res_tac \\ fs [fetch "-" "exp_size_def"]
QED

Definition subst_def:
  subst name v (Var s) = (if name = s then v else Var s) ∧
  subst name v (Prim op xs) = Prim op (MAP (subst name v) xs) ∧
  subst name v (App x y) = App (subst name v x) (subst name v y) ∧
  subst name v (Lam s x) = Lam s (if s = name then x else subst name v x) ∧
  subst name v (Letrec f x) =
    (if MEM name (MAP FST f) then Letrec f x else
      Letrec (MAP (λ(g,m,z). (g,m, if name = m then z else subst name v z )) f)
             (subst name v x)) ∧
  subst name v (Case e vn css) =
    (Case (subst name v e)
          vn
          (MAP (λ(cn,ans, cb).
                 (cn,ans, if ¬MEM name (vn::ans) then subst name v cb else cb))
               css))
Termination
  WF_REL_TAC `measure (λ(n,v,x). exp_size (K 0) (K 0) x)` \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

Definition freevars_def[simp]:
  freevars (Var n)     = [n]                               ∧
  freevars (Prim _ es) = (FLAT (MAP freevars es))          ∧
  freevars (App e1 e2) = (freevars e1 ⧺ freevars e2)       ∧
  freevars (Lam n e)   = (FILTER ($≠ n) (freevars e))      ∧
  freevars (Letrec lcs e) =
    FILTER (\n. ¬ MEM n (MAP FST lcs))
           (freevars e ⧺
            FLAT (MAP (λ(fn,vn,e). FILTER (λ n.n ≠ vn) (freevars e)) lcs))  ∧
  freevars (Case exp nm css) =
    (freevars exp ⧺ FLAT (MAP (λ(_,vs,cs).FILTER (λ n. ¬MEM n (nm::vs)) (freevars cs))
                              css))
Termination
  WF_REL_TAC ‘measure (exp_size (K 0) (K 0))’ \\ fs[]
  \\ conj_tac \\ TRY conj_tac
  \\ TRY (Induct_on ‘lcs’)
  \\ TRY (Induct_on ‘css’)
  \\ TRY (Induct_on ‘es’)
    \\ rw [] \\ fs [fetch "-" "exp_size_def"] \\ res_tac \\ fs[]
    \\ pop_assum (assume_tac o SPEC_ALL) \\ fs[]
End

Definition closed_def:
  closed e = (freevars e = [])
End

(*projection: given the constructor name s, and the index i,
  access the object x and retrieve the i-th element
  if present, otherwise returns Error. *)
Definition el_def:
  el s i x =
    if x = Diverge then Diverge else
      case x of
      | Constructor t xs =>
          if s = t then
            (case LNTH i xs of NONE => Error | SOME x => x)
          else Error
      | _ => Error
End

Definition is_eq_def:
  is_eq c s n x =
    if x = Diverge then Diverge else
      case x of
      | Constructor t (xs:(('a,'b) v) llist) =>
                      (case LLENGTH xs of
                         | NONE   => Error
                         | (SOME n') => (if (n = n')
                                          then (if s = t then True else False)
                                          else Error)
                      )
      | _ => Error
End

Definition getAtom_def:
  getAtom (Atom b) = SOME b ∧
  getAtom _        = NONE
End

Definition getAtoms_def:
  getAtoms [] = SOME [] ∧
  getAtoms (x::xs) = case (getAtom x,getAtoms xs) of
                     | (SOME n,SOME ns) => SOME (n::ns)
                     | _ => NONE
End

Definition eval_op_def:
  (eval_op c (Cons s) xs = Constructor s xs) ∧
  (eval_op c If [x1;x2;x3] =
    if x1 = Diverge then Diverge else
    if x1 = True  then x2 else
    if x1 = False then x3 else Error ) ∧
  (eval_op c (IsEq s n) [x] = is_eq c s n x) ∧
  (eval_op c (Proj s i) [x] = el s i x) ∧
  (eval_op c (AtomOp a) xs =
     if MEM Diverge xs then Diverge else
       case OPTION_BIND (getAtoms xs) (c.parAtomOp a) of
        | (SOME b) => Atom b
        | _        => Error )  ∧
  (eval_op c (Lit b) [] = Atom b) ∧
  (eval_op _ _ _ = Error)
End

Definition bind_def:
  bind [] x = x ∧
  bind ((s,v)::ys) x =
    if closed v then subst s v (bind ys x) else Fail
End

Definition subst_funs_def:
  subst_funs f = bind (MAP (λ(g,n,x). (g,Lam n (Letrec f x))) f)
End

Definition expandLets_def:
   expandLets i cn nm ([]) cs = cs ∧
   expandLets i cn nm (v::vs) cs = Let v (Proj cn i (Var nm))
                                         (expandLets (i+1) cn nm vs cs)
End

Definition expandRows_def:
   expandRows nm [] = Fail ∧
   expandRows nm ((cn,vs,cs)::css) = If (IsEq cn (LENGTH vs) (Var nm))
                                        (expandLets 0 cn nm vs cs)
                                        (expandRows nm css)
End

Definition expandCases_def:
   expandCases x nm css = (Let nm x (expandRows nm css))
End

(*EVAL “expandCases ARB "a" [("Nil",[],c1);("Cons",["x";"xs"],c2)] ”*)

Definition eval_to_def:
  eval_to c k (Var s) = Error ∧
  eval_to c k (Prim op xs) = eval_op c op (MAP (eval_to c k) xs) ∧
  eval_to c k (Lam s x) = Closure s x ∧
  eval_to c k (App x y) =
    (let v = eval_to c k x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) =>
             if k = 0 then Diverge else
               eval_to c (k-1) (bind [(s,y)] body)) ∧
  eval_to c k (Letrec f y) =
    (if k = 0 then Diverge else
      eval_to c (k-1) (subst_funs f y)) ∧
  eval_to c k (Case x nm css) =
    (if k = 0 then Diverge else
       eval_to c (k-1) (expandCases x nm css))
Termination
  WF_REL_TAC `inv_image ($< LEX $< LEX $<) (λ(_,k,x).(0,k,(exp_size (K 0) (K 0) x)))`
  \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

(*
  limit (div,div,div,div,div,...) d = div

  limit (div,div,div,div,div,4,4,4,4,4,4,4,4,4,4,4,4,...) d = 4

  limit (1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,...) d = d

  limit is used to define eval in terms of ‘∀ k . eval_to k’
  eval_to is deterministic, hence, we wouldn't need "d" in
  limit (k -> v) d. But is convenient for the proofs.
*)

Definition limit_def:
  limit (f:num->'a) default =
    (* if there is a value x that forever repeats from some
       index k onwards in sequence f, then return that x;
       in the other case we return the default value *)
    case (some x. ∃k. ∀n. k ≤ n ⇒ f n = x) of
    | SOME x => x
    | NONE => default
End

(*v_lookup takes a list of indexes and an ltree, goes trough
  the tree following the indexes in the list until list = [],
  then it returns the value at the given node, together with the
  number of children at that node *)

(*LLENGTH returns the length of the lazy list llist, when it is
  finite (SOME n), otherwise NONE. supposedly, (a,LLENGTH ts) refers
  to the constructor/literal together with its cardinality.

  LNTH = "Lazy n-th element"                                        *)

Definition v_lookup_def:
  v_lookup [] x =
    (case x of Branch a ts => (a,LLENGTH ts)) ∧
  v_lookup (n::path) x =
    (case x of Branch a ts =>
       case LNTH n ts of
       | NONE => (Diverge',SOME 0)
       | SOME y => v_lookup path y)
End

 (*
   v_seq: num -> v_prefix ltree
   given a certain path, v_limit tries to look into a rose tree (v_seq k)
   with k any num.
  *)
Definition v_limit_def:
  v_limit v_seq path =
    limit (λk. v_lookup path (v_seq k)) (Error', NONE)
End

(*
   given an expression x, eval returns the denotational
   value associated to it. Since eval might produce
   infinite values as result, the resulting value needs
   to be "wrapped" into a lazy datatype. This is the role
   of gen_ltree. gen_ltree takes a function that, given
   any path over the resulting ltree, the function returns
   the values in that specific branch.
   In fact, eval has type : exp -> v_prefix ltree, instead
   of exp -> v_prefix. Also, a value is defined
   as an object of type :v_prefix ltree
*)

Definition eval_def:
  eval c x =
    gen_ltree (λpath. v_limit (λk. eval_to c k x) path)
End


(**** LEMMAS for limit/v_limit algebra *****)

Theorem limit_const[simp]:
  limit (λk. x) d = x
Proof
  fs [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  THEN1 (first_x_assum (qspec_then ‘k’ mp_tac) \\ fs [])
  \\ first_x_assum (qspec_then ‘x’ mp_tac) \\ fs []
QED

Theorem limit_eq_add:
  ∀k p x f.
    limit (λn. f (n + k)) p = x ⇒
    limit f p = x
Proof
  rw [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  THEN1
   (first_x_assum (qspec_then ‘k'+k''’ mp_tac)
    \\ first_x_assum (qspec_then ‘k+k'+k''’ mp_tac)
    \\ fs [])
  THEN1
   (first_x_assum (qspecl_then [‘f (k+k')’,‘k'’] strip_assume_tac)
    \\ first_assum (qspecl_then [‘k+k'’] strip_assume_tac) \\ fs []
    \\ first_x_assum (qspecl_then [‘n+k’] strip_assume_tac)
    \\ rfs [] \\ rw [] \\ fs [])
  THEN1
   (last_x_assum (qspecl_then [‘x’,‘k+k'’] strip_assume_tac)
    \\ first_x_assum (qspecl_then [‘n-k’] strip_assume_tac) \\ fs []
    \\ rfs [])
QED

Theorem limit_if:
  ∀x y d. limit (λk. if k = 0 then x else y (k − 1)) d = limit y d
Proof
  rw [] \\ match_mp_tac limit_eq_add
  \\ qexists_tac ‘1’ \\ fs []
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
QED

Theorem v_limit_eq_add:
  ∀k p x f.
    v_limit (λn. f (n + k)) p = x ⇒
    v_limit f p = x
Proof
  rw [v_limit_def,FUN_EQ_THM]
  \\ match_mp_tac limit_eq_add
  \\ qexists_tac ‘k’ \\ fs []
QED



Theorem v_limit_if:
  v_limit (λk. if k = 0 then a else b (k − 1)) = v_limit b
Proof
  rw [v_limit_def,FUN_EQ_THM]
  \\ qspecl_then [‘v_lookup x a’,‘λk. v_lookup x (b k)’,‘(Error',NONE)’] mp_tac
       (GSYM limit_if)
  \\ fs [] \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM] \\ rw []
QED

Theorem v_limit_SOME:
  v_limit f [] = (r,SOME m) ⇔ ∃k. ∀n. k ≤ n ⇒ v_lookup [] (f n) = (r,SOME m)
Proof
  fs [v_limit_def,limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw [v_lookup_def]
  \\ PairCases_on ‘x’ \\ fs []
  \\ eq_tac \\ rw []
  THEN1 metis_tac []
  \\ first_x_assum (qspec_then ‘k+k'’ mp_tac)
  \\ first_x_assum (qspec_then ‘k+k'’ mp_tac) \\ fs []
QED

Theorem v_limit_not_Error:
  v_limit f [] = (r,l) ∧ r ≠ Error' ⇒
  ∃k. ∀n. k ≤ n ⇒ v_lookup [] (f n) = (r,l)
Proof
  fs [v_limit_def,limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw [v_lookup_def]
  \\ metis_tac []
QED

Theorem limit_not_default:
  limit f d = x ∧ x ≠ d ⇒ ∃k. ∀n. k ≤ n ⇒ f n = x
Proof
  fs [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  \\ qexists_tac ‘k’ \\ fs []
QED

Theorem limit_eq_imp:
  limit f d = x ∧ (∀n. k ≤ n ⇒ f n = y) ⇒ x = y
Proof
  rw [] \\ fs [limit_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw []
  THEN1 (rpt (first_x_assum (qspec_then ‘k+k'’ mp_tac)) \\ fs [])
  \\ first_x_assum (qspecl_then [‘y’,‘k’] mp_tac) \\ rw []
  \\ res_tac
QED

(***********************************)

(***********getNum lemmas***********)

Theorem getAtom_NONE:
  (getAtom x = NONE) = ∀n. x ≠ Atom n
Proof
  Cases_on ‘x’
  \\ Cases_on ‘a’ \\ Cases_on ‘ts’ \\ fs [getAtom_def]
QED

Theorem getAtom_SOME:
  getAtom x = SOME n ⇔ x = Atom n
Proof
  Cases_on ‘x’
  \\ Cases_on ‘a’ \\ Cases_on ‘ts’ \\ fs [getAtom_def]
QED

Theorem getAtom_eq_same_length_args:
  ∀ ts ts' . LLENGTH ts = LLENGTH ts'
             ⇒ getAtom (Branch q ts) = getAtom (Branch q ts')
Proof
  Cases_on ‘q’ \\ Cases_on ‘ts’ \\ Cases_on ‘ts'’ \\ rw [getAtom_def]
QED

Theorem getAtoms_SOME:
  getAtoms xs = SOME ns ⇒ (∀x.∃n. MEM x xs ⇒ x = Atom n)
Proof
  qspec_tac (‘ns’,‘ns’)
  \\ Induct_on ‘xs’ THEN1 (fs [])
  \\ strip_tac \\ strip_tac
  \\ disch_tac \\ rename [‘getAtoms (x::xs) = _’]
  \\ strip_tac
  \\ Cases_on ‘¬ (MEM x' (x::xs))’ THEN1 (fs [])
  \\ fs[getAtoms_def]
  \\ Cases_on ‘getAtom x’ \\ fs []
  \\ Cases_on ‘getAtoms xs’ \\ fs [] \\ rename [‘x::xs = xx’]
  THEN1 (fs[getAtom_SOME])
  \\ last_assum (qspec_then ‘x''’ strip_assume_tac) \\ fs[]
QED

Theorem getAtoms_NOT_SOME_NONE:
  getAtoms xs = NONE ⇔ ∀ l. getAtoms xs ≠ SOME l
Proof
  eq_tac \\ fs[getAtoms_def]
  \\ disch_tac \\ CCONTR_TAC
  \\ Cases_on ‘getAtoms xs’ \\ fs[]
QED

Theorem getAtoms_NOT_NONE_SOME:
  getAtoms xs ≠ NONE ⇔ ∃ l. getAtoms xs = SOME l
Proof
  eq_tac \\ fs[getAtoms_def,getAtoms_NOT_SOME_NONE]
  \\ disch_tac \\ fs []
QED

Theorem getAtoms_SOME_isFinite:
  ∀xs. getAtoms xs = SOME l ⇒
      ∀x. MEM x xs ⇒ (x ≠ Diverge ∧ ∃ a. x = Branch a LNIL)
Proof
  strip_tac \\ disch_tac
  \\ imp_res_tac getAtoms_SOME
  \\ strip_tac
  \\ last_x_assum (qspecl_then [‘x’] assume_tac) \\ fs[]
QED
(***********************************)

(* x and y : v_prefix ltree, v_cmp checks whether x and y are equal
   for the given path. If x or y diverge, then they ARE equal.
   v_cmp is a relation used to prove some lemmas over eval_to,
   ultimately, used to prove eval_thm
*)
Definition v_cmp_def:
  v_cmp path x y ⇔
    (v_lookup path x ≠ (Diverge',SOME 0) ⇒
     v_lookup path y = v_lookup path x)
End

Triviality v_cmp_refl[simp]:
  v_cmp path x x
Proof
  fs [v_cmp_def]
QED

Triviality LIST_REL_v_cmp_refl[simp]:
  ∀ xs. LIST_REL (λ x y.∀ path.v_cmp path x y) xs xs
Proof
  Induct \\ fs[]
QED

Triviality v_cmp_Diverge[simp]:
  ∀path x. v_cmp path Diverge x
Proof
  Induct \\ fs [v_cmp_def,v_lookup_def]
QED

Theorem v_cmp_Diverge2[simp]:
  (∀path. v_cmp path x y) ∧ x ≠ Diverge ⇒ y ≠ Diverge
Proof
  rw [] \\ CCONTR_TAC \\ fs []
  \\ first_x_assum (qspec_then ‘[]’ mp_tac)
  \\ fs [v_cmp_def,v_lookup_def]
  \\ Cases_on ‘x’ \\ fs []
QED

Theorem v_cmp_LNIL_IMP:
  ∀x y.
    x ≠ Diverge' ⇒
    ((∀path. v_cmp path (Branch x LNIL) y) ⇔ y = Branch x LNIL)
Proof
  rw [] \\ eq_tac \\ rw []
  \\ first_x_assum (qspec_then ‘[]’ mp_tac)
  \\ fs [v_cmp_def,v_lookup_def]
  \\ Cases_on ‘y’ \\ fs []
QED

Theorem v_cmp_LNIL_IMP2:
  ∀x y.
    x ≠ Diverge ∧ x = Branch a LNIL ⇒
    ((∀path. v_cmp path x y) ⇔ y = x)
Proof
  fs [v_cmp_LNIL_IMP]
QED

(*TODO: this might be used in order to simplify v_cmp_LNIL_IMP2 and
  the associated LIST_REL version*)
Definition isFinite_def:
  isFinite x = case x of
                | Branch Diverge' _ => F
                | Branch _     LNIL => T
                | _ => F
End

Theorem v_cmp_isFinite_IMP:
  ∀x y.
    (isFinite x ∧ (∀path. v_cmp path x y)) ⇒ y = x
Proof
  rw[] \\ Cases_on ‘x’
  \\ Cases_on ‘a’ \\ Cases_on ‘ts’ \\ fs [isFinite_def,v_cmp_LNIL_IMP2]
QED

Theorem LIST_REL_v_cmp_LNIL_IMP2:
  ∀xs ys.
    (∀x. MEM x xs ⇒ (x ≠ Diverge ∧ ∃ a. x = Branch a LNIL)) ⇒
    (LIST_REL (λx y.∀path. v_cmp path x y) xs ys ⇔ ys = xs)
Proof
  rw[] \\ eq_tac \\ fs [LIST_REL_def]
  \\ qspec_tac (‘ys’,‘yss’)
  \\ Induct_on ‘xs’ \\ fs[]
  \\ rpt (strip_tac \\ disch_tac) \\ fs []
  \\ last_x_assum kall_tac
  \\ last_x_assum (qspec_then ‘h’ strip_assume_tac) \\ fs []
  \\ imp_res_tac v_cmp_LNIL_IMP2 \\ rw []
QED

Theorem LIST_REL_not_diverge:
  ∀ xs ys.
  ¬MEM Diverge xs ∧
  LIST_REL (λx y. ∀path. v_cmp path x y) xs ys
  ⇒ ¬MEM Diverge ys
Proof
  Induct_on ‘xs’ \\ fs []
  \\ strip_tac
  \\ strip_tac
  \\ disch_tac
  \\ fs []
  \\ imp_res_tac v_cmp_Diverge2
QED

Theorem v_cmp_getAtom_eq:
  ∀x y.
    x ≠ Diverge ∧ y ≠ Diverge ⇒
    ((∀path. v_cmp path x y) ⇒ (getAtom x) = (getAtom y))
Proof
  rw []
  \\ first_x_assum (qspec_then ‘[]’ assume_tac)
  \\ Cases_on ‘x’
  \\ fs [v_cmp_def,v_lookup_def,ltree_CASE]
  \\ first_assum imp_res_tac
  \\ Cases_on ‘y’
  \\ fs [ltree_CASE]
  \\ rw []
  \\ imp_res_tac getAtom_eq_same_length_args
  \\ rw []
QED

Theorem LIST_REL_v_cmp_getAtom_eq:
  ∀xs ys.
    ¬MEM Diverge xs ∧ ¬MEM Diverge ys ∧
    (LIST_REL (λx y. ∀path. v_cmp path x y) xs ys)
    ⇒ getAtoms xs = getAtoms ys
Proof
  Induct \\ fs []
  \\ rpt strip_tac
  \\ Induct_on ‘ys’ \\ fs[]
  \\ rpt strip_tac
  \\ fs[getAtoms_def]
  \\ imp_res_tac v_cmp_getAtom_eq \\ fs []
  \\ last_x_assum (qspec_then ‘ys’ imp_res_tac)
  \\ fs []
QED

Theorem eval_op_div:
  ∀c op xs ys path.
    LIST_REL (λx y. ∀path. v_cmp path x y) xs ys ⇒
    v_cmp path (eval_op c op xs) (eval_op c op ys)
Proof
  ho_match_mp_tac eval_op_ind \\ rw []
  \\ TRY (fs [eval_op_def] \\ rw [] \\ fs [v_cmp_refl] \\ NO_TAC)
  THEN1 (*op = Cons s *)
   (fs [eval_op_def] \\ fs [v_cmp_def]
    \\ Cases_on ‘path’ \\ fs [v_lookup_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs [LNTH_fromList]
    \\ rw [] \\ fs [LIST_REL_EL_EQN])
  THEN1 (*op = If *)
   (fs [eval_op_def]
    \\ Cases_on ‘x1 = Diverge’ \\ fs []
    \\ ‘y ≠ Diverge’ by (imp_res_tac v_cmp_Diverge2) \\ fs[]
    \\ IF_CASES_TAC
    THEN1
     (Cases_on ‘x1’
      \\ Cases_on ‘y’
      \\ imp_res_tac v_cmp_LNIL_IMP2 \\ gs[])
    \\ IF_CASES_TAC
    THEN1
     (Cases_on ‘x1’
      \\ Cases_on ‘y’
      \\ imp_res_tac v_cmp_LNIL_IMP2 \\ gs[])
    \\ Cases_on ‘y = True’
    THEN1
     (last_x_assum (qspec_then ‘[]’ mp_tac)
      \\ fs[]
      \\ Cases_on ‘x1’ \\ strip_tac \\ gs[v_cmp_def,v_lookup_def])
    \\ Cases_on ‘y = False’
    THEN1
     (last_x_assum (qspec_then ‘[]’ mp_tac)
      \\ fs[]
      \\ Cases_on ‘x1’ \\ strip_tac \\ gs[v_cmp_def,v_lookup_def])
    \\ fs[])
  THEN1 (*op = IsEq s *)
   (fs [eval_op_def]
    \\ Cases_on ‘x = Diverge’ \\ fs[is_eq_def]
    \\ Cases_on ‘y = Diverge’ \\ fs[is_eq_def] \\ imp_res_tac v_cmp_Diverge2 \\ fs[is_eq_def]
    \\ TRY (first_assum (qspec_then ‘[]’ mp_tac) \\ disch_tac)
    \\ Cases_on ‘path’ \\ fs [v_cmp_def,v_lookup_def,is_eq_def]
    \\ rw [] \\ fs [] \\ fs [ltree_CASE_eq]
    \\ Cases_on ‘x’
    \\ Cases_on ‘y’ \\ fs []
    \\ Cases_on ‘a’ \\ fs []
    \\ Cases_on ‘a'’ \\ fs []
    \\ Cases_on ‘s=s''’ \\ fs[] \\ rw[]
    \\ Cases_on ‘LLENGTH ts'’ \\ fs[] \\ rw[])
  THEN1 (*op = Proj s i*)
   (fs [eval_op_def,el_def]
    \\ Cases_on ‘x = Diverge’ \\ fs []
    \\ imp_res_tac v_cmp_Diverge2 \\ fs []
    \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ simp []
    \\ ‘a' = a ∧ LLENGTH ts' = LLENGTH ts’ by
      (first_x_assum (qspec_then ‘[]’ mp_tac)
       \\ fs [v_cmp_def,v_lookup_def])
    \\ pop_assum mp_tac \\ simp []
    \\ pop_assum mp_tac \\ simp []
    \\ Cases_on ‘a’ \\ simp []
    \\ strip_tac \\ strip_tac
    \\ first_x_assum (qspec_then ‘i::path’ mp_tac)
    \\ simp [v_lookup_def,v_cmp_def]
    \\ pop_assum mp_tac \\ simp []
    \\ rpt (pop_assum kall_tac)
    \\ qspec_then ‘ts’ mp_tac fromList_fromSeq
    \\ qspec_then ‘ts'’ mp_tac fromList_fromSeq
    \\ rw [] \\ fs [LNTH_fromList]
    \\ rfs [] \\ rw [] \\ fs []   )
  THEN1 (*op = PrimOp*)
   (Cases_on ‘MEM Diverge xs’ THEN1 (fs [eval_op_def])
    \\ ‘¬(MEM Diverge ys)’ by (imp_res_tac LIST_REL_not_diverge)
    \\ fs [eval_op_def]
    \\ Cases_on ‘∃l. getAtoms xs = SOME l’ THEN1(
       fs [] \\ imp_res_tac getAtoms_SOME_isFinite
       \\ qspecl_then [‘xs’,‘ys’] strip_assume_tac LIST_REL_v_cmp_LNIL_IMP2
       \\ fs[])
    \\ fs [] \\ imp_res_tac getAtoms_NOT_SOME_NONE \\ simp []
    \\ ‘getAtoms ys = NONE’ by
      (CCONTR_TAC
       \\ ‘∃ l. getAtoms ys = SOME l’ by (fs[getAtoms_NOT_NONE_SOME])
       \\ first_x_assum (qspec_then ‘l’ assume_tac)
       \\ imp_res_tac LIST_REL_v_cmp_getAtom_eq \\ fs [])
    \\ fs [])
QED

Theorem eval_to_res_mono_lemma:
  ∀ c k x n path. v_cmp path (eval_to c k x) (eval_to c (k+n) x)
Proof
  ho_match_mp_tac eval_to_ind \\ rpt conj_tac
  \\ rpt gen_tac
  \\ TRY (fs [eval_to_def] \\ rw [v_cmp_refl] \\ NO_TAC)
  THEN1
   (fs [eval_to_def] \\ strip_tac
    \\ rpt gen_tac
    \\ match_mp_tac eval_op_div
    \\ Induct_on ‘xs’ \\ fs [])
  \\ strip_tac
  \\ fs [eval_to_def]
  \\ Cases_on ‘eval_to c k x = Diverge’ \\ fs []
  \\ fs [] \\ rpt strip_tac
  \\ ‘eval_to c (k + n) x ≠ Diverge’ by
   (CCONTR_TAC
    \\ first_x_assum (qspecl_then [‘n’,‘[]’] mp_tac)
    \\ pop_assum mp_tac \\ simp []
    \\ fs [v_cmp_def] \\ fs [v_lookup_def]
    \\ Cases_on ‘eval_to c k x’ \\ fs [])
  \\ fs []
  \\ ‘dest_Closure (eval_to c (k + n) x) = dest_Closure (eval_to c k x)’ by
   (Cases_on ‘eval_to c k x’ \\ simp []
    \\ Cases_on ‘eval_to c (k+n) x’ \\ simp []
    \\ first_x_assum (qspecl_then [‘n’,‘[]’] mp_tac)
    \\ simp [v_cmp_def] \\ simp [v_lookup_def]
    \\ simp [dest_Closure_def] \\ fs []
    \\ Cases_on ‘a’ \\ simp []
    \\ Cases_on ‘ts’ \\ Cases_on ‘ts'’ \\ simp []) \\ fs []
  \\ Cases_on ‘dest_Closure (eval_to c k x)’ \\ fs [v_cmp_refl]
  \\ PairCases_on ‘x'’ \\ simp []
  \\ last_x_assum mp_tac \\ simp []
  \\ Cases_on ‘k = 0’ \\ simp []
QED

Theorem eval_to_res_mono:
  eval_to c k x ≠ Diverge ∧
  eval_to c k x = Branch a ts ∧
  eval_to c k1 x = Branch a1 ts1 ∧
  k ≤ k1 ⇒
    a1 = a ∧ LLENGTH ts1 = LLENGTH ts
Proof
  fs [LESS_EQ_EXISTS] \\ strip_tac
  \\ BasicProvers.var_eq_tac
  \\ qspecl_then [‘c’,‘k’,‘x’,‘p’,‘[]’] mp_tac eval_to_res_mono_lemma
  \\ simp [v_cmp_def,v_lookup_def] \\ fs []
QED

Theorem eval_to_res_mono_LNIL:
  eval_to c k x = Branch a LNIL ∧
  eval_to c k x ≠ Diverge ∧
  k ≤ k1 ⇒
    eval_to c k1 x = eval_to c k x
Proof
  rw []
  \\ drule eval_to_res_mono
  \\ disch_then drule
  \\ Cases_on ‘eval_to c k1 x’
  \\ disch_then drule
  \\ fs []
QED

Theorem eval_to_simple_mono:
  eval_to c k1 x = Branch a LNIL ∧
  eval_to c k x ≠ Diverge ∧
  k ≤ k1 ⇒
    eval_to c k1 x = eval_to c k x
Proof
  rw []
  \\ drule eval_to_res_mono
  \\ Cases_on ‘eval_to c k x’
  \\ simp []
  \\ last_x_assum assume_tac
  \\ disch_then drule
  \\ fs []
QED

Theorem eval_to_div:
  eval_to c k1 x = Diverge ∧ k ≤ k1 ⇒ eval_to c k x = Diverge
Proof
  rw [] \\ CCONTR_TAC
  \\ drule eval_to_simple_mono
  \\ disch_then drule \\ fs []
QED

Theorem eval_to_not_diverge_mono:
  ∀ k' k x . (k ≤ k' ∧ eval_to c k x ≠ Diverge) ⇒ eval_to c k' x ≠ Diverge
Proof
  rw []
  \\ Cases_on ‘eval_to c k x’ \\ Cases_on ‘eval_to c k' x’
  \\ qspecl_then
        [‘x’,‘ts'’,‘ts’,‘k'’,‘k’,‘c’,‘a'’,‘a’]
        assume_tac (GEN_ALL eval_to_res_mono) \\ fs []
  \\ first_assum imp_res_tac \\ rw []
  \\ ‘eval_to c k x ≠ Diverge’ by (fs [])
  \\ ‘a' = a ∧ LLENGTH ts' = LLENGTH ts’ by (fs [])
  \\ Cases_on ‘a’ \\ Cases_on ‘ts’ \\ Cases_on ‘ts'’ \\ fs []
QED

Theorem eval_to_not_diverge_not_eq_mono:
  ∀ k' k x a. (k ≤ k' ∧ eval_to c k x ≠ Diverge ∧ eval_to c k x ≠ Branch a LNIL)
              ⇒ eval_to c k' x ≠ Branch a LNIL
Proof
  rw[]
  \\ CCONTR_TAC \\ fs[]
  \\ imp_res_tac eval_to_simple_mono \\ fs[]
QED

Theorem LIST_MAP_eval_to_not_diverge_mono:
  ∀ k' k. (k ≤ k' ∧ ¬MEM Diverge (MAP (λa. eval_to c k a) es))
                  ⇒ ¬MEM Diverge (MAP (λa. eval_to c k' a) es)
Proof
  rw[] \\ Induct_on ‘es’ \\ fs[]
  \\ strip_tac \\ disch_tac \\ fs[]
  \\imp_res_tac eval_to_not_diverge_mono
QED

Theorem dest_Closure_eval_IMP:
  dest_Closure (eval c x) = NONE ⇒
  dest_Closure (eval_to c k x) = NONE
Proof
  rw []
  \\ simp [AllCaseEqs(),dest_Closure_def]
  \\ CCONTR_TAC \\ fs []
  \\ Cases_on ‘eval_to c k x’ \\ fs []
  \\ Cases_on ‘a’ \\ fs []
  \\ Cases_on ‘ts’ \\ fs []
  \\ rename [‘Closure x1 x2’]
  \\ qsuff_tac ‘eval c x = Closure x1 x2’
  THEN1 (strip_tac \\ fs [dest_Closure_def])
  \\ fs [eval_def,gen_ltree_LNIL,v_limit_SOME]
  \\ drule eval_to_res_mono_LNIL \\ fs [] \\ rw []
  \\ qexists_tac ‘k’ \\ fs [v_lookup_def]
QED

Theorem v_lookup_eq_SOME_0[simp]:
  v_lookup [] t = (h,SOME 0) ⇔ t = Branch h LNIL
Proof
  fs [v_lookup_def]
  \\ Cases_on ‘t’ \\ fs []
QED

Theorem eval_Var:
  eval c (Var s) = Error (* free variables are not allowed *)
Proof
  fs [eval_def,eval_to_def,Once gen_ltree]
  \\ fs [v_limit_def,v_lookup_def]
QED

Theorem eval_Lam:
  eval c (Lam s x) = Closure s x
Proof
  fs [eval_def,eval_to_def,Once gen_ltree]
  \\ fs [v_limit_def,v_lookup_def]
QED

Theorem eval_Letrec:
  eval c (Letrec f x) = eval c (subst_funs f x)
Proof
  fs [eval_def,eval_to_def]
  \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ match_mp_tac v_limit_eq_add
  \\ fs [] \\ qexists_tac ‘1’ \\ fs []
QED

Theorem eval_App:
  eval c (App x y) =
    let v = eval c x in
      if v = Diverge then Diverge else
        case dest_Closure v of
        | NONE => Error
        | SOME (s,body) => eval c (bind [(s,y)] body)
Proof
  fs [eval_def,eval_to_def]
  \\ IF_CASES_TAC \\ fs [gen_ltree_LNIL]
  THEN1 (fs [v_limit_SOME] \\ qexists_tac ‘k’ \\ fs [])
  \\ CASE_TAC
  THEN1
   (fs [v_limit_SOME]
    \\ fs [GSYM eval_def]
    \\ imp_res_tac dest_Closure_eval_IMP \\ fs []
    \\ fs [gen_ltree_LNIL]
    \\ fs [v_limit_SOME]
    \\ last_x_assum (qspec_then ‘0’ strip_assume_tac) \\ fs []
    \\ qexists_tac ‘k'’ \\ fs [] \\ rpt strip_tac
    \\ rw [] \\ imp_res_tac eval_to_div)
  \\ rename [‘_ = SOME y’] \\ PairCases_on ‘y’ \\ fs []
  \\ fs [dest_Closure_def,AllCaseEqs()]
  \\ fs [gen_ltree_LNIL]
  \\ fs [v_limit_SOME]
  \\ AP_TERM_TAC \\ fs [FUN_EQ_THM] \\ rw []
  \\ match_mp_tac v_limit_eq_add
  \\ fs [] \\ qexists_tac ‘k+1’ \\ fs []
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ match_mp_tac v_limit_eq_add
  \\ fs [] \\ qexists_tac ‘k’ \\ fs []
QED

Theorem eval_Let:
  eval c (Let s x y) = eval c (bind [(s,x)] y)
Proof
  fs [eval_App,eval_Lam,dest_Closure_def,bind_def]
QED

Theorem eval_Cons:
  eval c (Cons s xs) = Constructor s (MAP (eval c) xs)
Proof
  fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
  \\ fs [v_limit_def,v_lookup_def,LGENLIST_EQ_fromList,LNTH_fromList]
  \\ fs [LIST_EQ_REWRITE]
  \\ fs [EL_MAP,eval_def,v_limit_def]
QED

Theorem eval_Case:
  eval c (Case x nm css) = eval c (expandCases x nm css)
Proof
  fs[expandCases_def,eval_Let,bind_def]
  \\ IF_CASES_TAC
  \\ fs[eval_def,eval_to_def]
  \\ fs [v_limit_if]
  \\ fs [expandCases_def,bind_def,eval_to_def]
  \\ fs [eval_to_def]
  \\ fs [v_limit_if]
  \\ fs [bind_def]
QED

Theorem eval_op_finite_branch:
  ∀ c op xs.
     (∀ x. MEM x xs ⇒ ltree_finite x) ⇒ ltree_finite (eval_op c op xs)
Proof
  ho_match_mp_tac eval_op_ind
  \\ rw[] \\ fs[eval_op_def,ltree_finite]
  THEN1 (
    Induct_on ‘xs’ \\ fs[]
    \\ rpt strip_tac \\ fs[ltree_finite]
  )
  THEN1 (ntac 3 (IF_CASES_TAC \\ fs[ltree_finite]))
  THEN1 (
    fs[is_eq_def] \\ IF_CASES_TAC \\ fs[]
    \\ Cases_on ‘x’ \\ fs[ltree_finite]
    \\ Cases_on ‘a’ \\ fs[ltree_finite]
    \\ fs[LLENGTH] \\ rpt (IF_CASES_TAC \\ fs[ltree_finite])
  )
  THEN1 (
    fs[el_def] \\ IF_CASES_TAC \\ fs[]
    \\ Cases_on ‘x’ \\ fs[ltree_finite]
    \\ Cases_on ‘a’ \\ fs[ltree_finite]
    \\ rpt (IF_CASES_TAC \\ fs[ltree_finite])
    \\ rw[] \\ fs[IN_DEF]
    \\ Cases_on ‘LNTH i ts’ \\ fs[ltree_finite]
    \\ imp_res_tac LSET_def \\ fs[ltree_finite]
  )
  THEN1 (
    IF_CASES_TAC \\ fs[ltree_finite]
    \\ Cases_on ‘ OPTION_BIND (getAtoms xs) (c.parAtomOp a)’ \\ fs[ltree_finite]
  )
QED

Theorem eval_to_finite_branch:
  ∀ c k e. ltree_finite (eval_to c k e)
Proof
  ho_match_mp_tac eval_to_ind
  \\ rw[]
  \\ fs[eval_to_def,eval_op_def,ltree_finite]
  THEN1 (
    qsuff_tac ‘∀ x. MEM x (MAP (λa. eval_to c k a) xs) ⇒ ltree_finite x’
    THEN1 (fs[ltree_finite,eval_op_finite_branch])
    \\ rpt strip_tac
    \\ Induct_on ‘xs’ \\ fs[]
    \\ rpt strip_tac \\ fs[]
  )
  THEN1 (
    IF_CASES_TAC \\ fs[ltree_finite]
    \\ Cases_on ‘dest_Closure (eval_to c k e)’ \\ fs[ltree_finite]
    \\ Cases_on ‘x’ \\ fs[ltree_finite]
    \\ IF_CASES_TAC \\ fs[ltree_finite]
  )
  THEN1 (IF_CASES_TAC \\ fs[ltree_finite])
  THEN1 (IF_CASES_TAC \\ fs[ltree_finite])
QED

Theorem gen_ltree_not_Error:
  gen_ltree (λpath. v_limit (λk. eval_to c k x) path) = Branch a ts ∧
  a ≠ Error' ⇒
  ∃k. ∀n. k ≤ n ⇒ ∃ts. eval_to c n x = Branch a ts
Proof
  once_rewrite_tac [gen_ltree] \\ fs [pairTheory.UNCURRY] \\ rw []
  \\ Cases_on ‘v_limit (λk. eval_to c k x) []’
  \\ fs [v_limit_def]
  \\ drule limit_not_default \\ fs []
  \\ rpt strip_tac \\ qexists_tac ‘k’ \\ fs []
  \\ rpt strip_tac \\ first_x_assum drule
  \\ fs [] \\ Cases_on ‘eval_to c n x’ \\ fs []
  \\ fs [v_lookup_def]
QED

Theorem gen_ltree_not_Error_LFINITE:
  gen_ltree (λpath. v_limit (λk. eval_to c k x) path) = Branch a ts ∧
  a ≠ Error' ⇒
  ∃k. ∀n. k ≤ n ⇒ ∃ts'. eval_to c n x = Branch a ts'
                        ∧ LFINITE ts' ∧ LLENGTH ts = LLENGTH ts'
Proof
  once_rewrite_tac [gen_ltree] \\ fs [pairTheory.UNCURRY] \\ rw []
  \\ Cases_on ‘v_limit (λk. eval_to c k x) []’
  \\ fs [v_limit_def]
  \\ drule limit_not_default \\ fs []
  \\ rpt strip_tac \\ qexists_tac ‘k’ \\ fs []
  \\ rpt strip_tac \\ first_x_assum drule
  \\ fs [] \\ Cases_on ‘eval_to c n x’ \\ fs []
  \\ fs [v_lookup_def]
  \\ rpt strip_tac
  \\ Cases_on ‘r’ \\ fs[LLENGTH]
  \\ qspecl_then [‘c’,‘n’,‘x’] assume_tac eval_to_finite_branch
  \\ Cases_on ‘eval_to c n x’ \\ fs[ltree_finite] \\ rw[] \\ fs[]
QED

(*
Theorem llength_rel_fromList:
  ∀l n. llength_rel (fromList l) n ⇔ n = LENGTH l
Proof
  Induct \\ fs []
  \\ simp [Once llength_rel_cases]
QED

Triviality llength_rel_fromList_lemma:
  (@n. llength_rel (fromList l) n) = LENGTH l
Proof
  fs [llength_rel_fromList]
QED
*)

Theorem eval_IsEq:
  eval c (IsEq s n x) = is_eq c s n (eval c x)
Proof
  fs [eval_def,eval_to_def,eval_op_def,is_eq_def]
  \\ IF_CASES_TAC \\ fs [gen_ltree_LNIL]
  THEN1 (fs [v_limit_SOME] \\ qexists_tac ‘k’ \\ fs [])
  \\ fs [GSYM eval_def]
  \\ Cases_on ‘eval c x’ \\ fs [eval_def]
  \\ Cases_on ‘a = Error'’
  THEN1 (
    fs[]
    \\ Cases_on ‘ts’
    THEN1 (
       fs[v_limit_SOME,gen_ltree_LNIL]
       \\ first_x_assum (qspec_then ‘k’ assume_tac) \\ fs[]
       \\ qexists_tac ‘k’
       \\ rpt strip_tac
       \\ ‘eval_to c k'' x = Error’ by (
          Cases_on ‘eval_to c k x’
          \\ Cases_on ‘eval_to c k'' x’
          \\ ‘eval_to c k x ≠ Diverge’ by fs[]
          \\ drule eval_to_res_mono \\ strip_tac
          \\ rfs[] \\ res_tac \\ fs[])
       \\ fs[]
    )
    \\ fs[v_limit_SOME,gen_ltree_LNIL]
    \\ rw []
    \\ first_x_assum (qspec_then ‘0’ strip_assume_tac) \\ fs []
    \\ qexists_tac ‘k'’ \\ fs [] \\ rw []
    THEN1 (strip_tac \\ imp_res_tac eval_to_div)
    \\ Cases_on ‘eval_to c k'' x’ \\ simp []
    \\ Cases_on ‘a’ \\ simp [] \\ fs []
    \\ Cases_on ‘LLENGTH ts’ \\ fs[]
    \\ pop_assum kall_tac
    \\ IF_CASES_TAC \\ fs[]
    \\ pop_assum kall_tac
    \\ last_x_assum mp_tac \\ simp []
    \\ once_rewrite_tac [gen_ltree]
    \\ fs [] \\ Cases_on ‘v_limit (λk. eval_to c k x) []’ \\ fs []
    \\ CCONTR_TAC \\ fs [] \\ rw []
    \\ ‘eval_to c k'' x ≠ Diverge’ by fs []
    \\ drule eval_to_res_mono \\ strip_tac \\ rfs []
    \\ first_x_assum drule \\ strip_tac
    \\ rfs [v_limit_def,v_lookup_def]
    \\ drule limit_eq_imp
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ disch_then (qspecl_then [‘Constructor' s',LLENGTH ts’,‘k''’] mp_tac)
    \\ impl_tac \\ fs []
    \\ fs [AllCaseEqs()]
    \\ ‘eval_to c k'' x ≠ Diverge’ by fs []
    \\ drule eval_to_res_mono \\ strip_tac \\ rfs [] \\ rw []
    \\ Cases_on ‘eval_to c n x’ \\ fs []
    \\ first_x_assum drule \\ fs []
    \\ rw[]
  )
  \\ fs[v_limit_SOME]
  \\ drule gen_ltree_not_Error_LFINITE \\ fs[] \\ strip_tac
  \\ last_x_assum (qspec_then ‘k’ assume_tac) \\ fs[]
  \\ first_x_assum (qspec_then ‘k'’ assume_tac) \\ fs[] \\ res_tac
  \\ qspecl_then [‘c’,‘k'’,‘x’] assume_tac eval_to_finite_branch
  \\ Cases_on ‘eval_to c k' x’ \\ rw[]
  \\ fs[ltree_finite] \\ fs[LLENGTH] \\ rw[]
  \\ Cases_on ‘a’ \\ fs[]
  \\ TRY IF_CASES_TAC \\ fs[]
  \\ TRY IF_CASES_TAC \\ fs[]
  \\ fs[gen_ltree_LNIL,v_limit_SOME]
  \\ qexists_tac ‘k'’ \\ rpt strip_tac
  \\ rfs[]
  \\ imp_res_tac eval_to_not_diverge_mono \\ fs[]
  \\ Cases_on ‘eval_to c k''' x’ \\ fs[] \\ res_tac
  \\ ‘eval_to c k' x ≠ Diverge’ by fs[]
  \\ qspecl_then [‘x’,‘ts''’,‘ts'’,‘k'''’,‘k'’,‘c’] assume_tac (GEN_ALL eval_to_res_mono)
  \\ first_x_assum (drule)
  \\ simp[]
  \\ fs[LLENGTH]
QED

Theorem eval_Proj:
  eval c (Proj s i x) = el s i (eval c x)
Proof
  fs [eval_def,eval_to_def,eval_op_def,el_def]
  \\ IF_CASES_TAC \\ fs [gen_ltree_LNIL]
  THEN1 (fs [v_limit_SOME] \\ qexists_tac ‘k’ \\ fs [])
  \\ fs [GSYM eval_def]
  \\ Cases_on ‘eval c x’ \\ fs [eval_def]
  \\ Cases_on ‘ts’
  THEN1
   (Cases_on ‘a’ \\ fs []
    \\ fs [v_limit_SOME,gen_ltree_LNIL]
    \\ qexists_tac ‘k’ \\ fs [])
  \\ Cases_on ‘a’ \\ fs []
  \\ fs [v_limit_SOME,gen_ltree_LNIL]
  \\ pop_assum mp_tac
  THEN1
   (rw [] \\ drule gen_ltree_not_Error \\ fs []
    \\ strip_tac \\ qexists_tac ‘k’ \\ fs []
    \\ rpt strip_tac \\ res_tac \\ fs [])
  THEN1
   (simp [Once gen_ltree,pairTheory.UNCURRY]
    \\ reverse (Cases_on ‘s=s'’) \\ fs []
    \\ Cases_on ‘v_limit (λk. eval_to c k x) []’ \\ fs [] \\ rw []
    \\ pop_assum (assume_tac o GSYM) \\ fs [LNTH_LGENLIST]
    \\ drule v_limit_not_Error
    \\ fs [] \\ strip_tac
    THEN1
     (fs [gen_ltree_LNIL]
      \\ match_mp_tac v_limit_eq_add
      \\ fs [v_limit_SOME]
      \\ qexists_tac ‘k’ \\ fs []
      \\ qexists_tac ‘0’ \\ fs []
      \\ fs [v_lookup_def] \\ gen_tac
      \\ fs [ltree_CASE_eq]
      \\ first_x_assum (qspec_then ‘k+n’ strip_assume_tac) \\ fs [])
    \\ Cases_on ‘r’ \\ fs []
    THEN1
     (AP_TERM_TAC \\ fs [FUN_EQ_THM]
      \\ rw [] \\ fs [v_lookup_def]
      \\ match_mp_tac v_limit_eq_add
      \\ qexists_tac ‘k’ \\ fs []
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ match_mp_tac v_limit_eq_add
      \\ qexists_tac ‘k’ \\ fs []
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ fs [v_limit_def,v_lookup_def]
      \\ AP_THM_TAC \\ AP_TERM_TAC
      \\ fs [FUN_EQ_THM] \\ rpt strip_tac
      \\ first_x_assum (qspec_then ‘k+n’ mp_tac) \\ fs []
      \\ Cases_on ‘eval_to c (k + n) x’ \\ fs [] \\ rw []
      \\ qspec_then ‘ts’ mp_tac fromList_fromSeq \\ rw [] \\ fs [])
    \\ reverse IF_CASES_TAC \\ fs []
    THEN1
     (fs [gen_ltree_LNIL,v_limit_SOME]
      \\ qexists_tac ‘k’ \\ fs [] \\ rpt strip_tac
      \\ first_x_assum drule \\ fs [v_lookup_def]
      \\ rename [‘eval_to c k3 x = Diverge’]
      \\ Cases_on ‘eval_to c k3 x’ \\ fs []
      \\ qspec_then ‘ts’ mp_tac fromList_fromSeq \\ rw [] \\ fs []
      \\ rw [] \\ fs [LNTH_fromList])
    \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
    \\ rw [] \\ fs [v_lookup_def]
    \\ match_mp_tac v_limit_eq_add
    \\ qexists_tac ‘k’ \\ fs []
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ match_mp_tac v_limit_eq_add
    \\ qexists_tac ‘k’ \\ fs []
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ fs [v_limit_def,v_lookup_def]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ fs [FUN_EQ_THM] \\ rpt strip_tac
    \\ first_x_assum (qspec_then ‘k+n’ mp_tac) \\ fs []
    \\ Cases_on ‘eval_to c (k + n) x’ \\ fs [] \\ rw []
    \\ qspec_then ‘ts’ mp_tac fromList_fromSeq \\ rw [] \\ fs []
    \\ rw [] \\ fs [LNTH_fromList])
  THEN1
   (rw [] \\ drule gen_ltree_not_Error \\ fs []
    \\ strip_tac \\ qexists_tac ‘k’ \\ fs []
    \\ rpt strip_tac \\ res_tac \\ fs [])
  THEN1
   (rw [] \\ drule gen_ltree_not_Error \\ fs []
    \\ strip_tac \\ last_assum (qspec_then ‘k’ mp_tac)
    \\ strip_tac
    \\ qexists_tac ‘k'’ \\ fs []
    \\ rpt strip_tac \\ ‘k ≤ k''’ by fs []
    \\ first_x_assum drule \\ strip_tac
    \\ fs [] \\ rw []
    \\ drule eval_to_div
    \\ disch_then (qspec_then ‘k'’ assume_tac)
    \\ rfs [])
  \\ rw []
  \\ first_x_assum (qspec_then ‘0’ strip_assume_tac) \\ fs []
  \\ qexists_tac ‘k'’ \\ fs [] \\ rw []
  THEN1 (strip_tac \\ imp_res_tac eval_to_div)
  \\ Cases_on ‘eval_to c k'' x’ \\ fs []
  \\ Cases_on ‘a’ \\ fs []
  \\ Cases_on ‘LNTH i ts’ \\ fs [] \\ rw []
  \\ last_x_assum mp_tac
  \\ once_rewrite_tac [gen_ltree]
  \\ fs [] \\ Cases_on ‘v_limit (λk. eval_to c k x) []’ \\ fs []
  \\ ‘eval_to c k'' x ≠ Diverge’ by fs []
  \\ drule eval_to_res_mono \\ fs []
  \\ rpt strip_tac
  \\ fs [v_limit_def,v_lookup_def]
  \\ drule limit_eq_imp
  \\ disch_then (qspecl_then [‘Constructor' s,LLENGTH ts’,‘k''’] mp_tac)
  \\ impl_tac \\ fs []
  \\ rw [] \\ fs []
  \\ res_tac \\ fs []
  \\ Cases_on ‘eval_to c n x’ \\ fs []
QED

(************ getAtom NONE/SOME over eval/eval_to lemmas*********)

(*if eval_to does not diverge and is not equal to Num for some k, then
  eval_to is not equal to Num forall k                                *)
Theorem eval_to_not_div_not_eq_mono:
  ∀ n.(( eval_to c k (x:('a,'b) exp) ≠ Diverge ∧ eval_to c k x ≠ Atom n)
       ⇒ ∀ k'. eval_to c k' x ≠ Atom n)
Proof
  rw[] \\ Cases_on ‘k≤k'’
  THEN1
   (imp_res_tac eval_to_not_diverge_mono
    \\ Cases_on ‘eval_to c k x’ \\ Cases_on ‘eval_to c k' x’ (*unboxing  branch*)
    \\ ‘eval_to c k x ≠ Diverge’ by (fs[])
    \\ qspecl_then [‘a'’,‘ts'’,‘k'’] assume_tac
           (Q.GENL [‘a1’,‘ts1’,‘k1’] eval_to_res_mono)
    \\ first_x_assum imp_res_tac \\ CCONTR_TAC \\ fs[])
  THEN1
   (first_x_assum (fn t => ‘k' ≤ k’ by fs [t])
    \\ rename [‘k≤k'’]
    \\ CCONTR_TAC \\ fs[]
    \\ Cases_on ‘eval_to c k x’
    \\ Cases_on ‘ts’ \\ fs[]
    \\ ‘eval_to c k x ≠ Diverge’ by (fs[])
    \\ qspecl_then [‘k'’] assume_tac $ Q.GENL [‘k1’] eval_to_res_mono_LNIL
    \\ res_tac
    \\ first_x_assum imp_res_tac \\ fs [])
QED

Theorem getAtom_eval_NONE:
  getAtom (eval c x) = NONE ⇒ (∀ k. ∃k'. k ≤ k' ∧ getAtom (eval_to c k' x) = NONE)
Proof
  rw[]
  \\ fs[getAtom_NONE]
  \\ fs[eval_def,eval_to_def,gen_ltree_LNIL,v_limit_SOME]
  (*like SWAP_FORALL_THM...*)
  \\ ‘∀k n. ∃k'. k ≤ k' ∧ eval_to c k' x ≠ Atom n’ by (fs[])
  \\ first_x_assum (qspec_then ‘k’ assume_tac)
  \\ qexists_tac ‘k’ \\ fs[] \\ strip_tac
  \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ fs[]
  \\ Cases_on ‘eval_to c k' x = Diverge’
  THEN1 (imp_res_tac eval_to_div \\ fs[])
  \\ imp_res_tac eval_to_not_div_not_eq_mono
  \\ first_x_assum (qspec_then ‘k’ assume_tac) \\ fs[]
QED

(*************eval/eval_to over exp list lemmas ***************)

Theorem eval_Diverge_IFF_eval_to_Diverge:
  MEM Diverge (MAP (eval c) es) ⇔ ∀ k. MEM Diverge (MAP (λa. eval_to c k a) es)
Proof
  Cases_on ‘MEM Diverge (MAP (eval c) es)’ \\ fs []
  THEN1 (
    rw [] \\ Induct_on ‘es’ \\ fs[]
    \\ rpt strip_tac \\ fs []
    \\ fs[eval_def,eval_to_def,gen_ltree_LNIL,v_limit_SOME]
    \\ CCONTR_TAC \\ fs[]
    \\ first_assum (qspec_then ‘k’ assume_tac) \\ fs[]
    \\ Cases_on ‘k'≤k’ \\ fs[]
    \\ ‘k≤k'’ by (fs[])
    \\ first_assum (qspec_then ‘k'’ assume_tac) \\ fs[]
    \\ imp_res_tac eval_to_div \\ fs [])
  THEN1 (
    Induct_on ‘es’ \\ fs[]
    \\ strip_tac \\ disch_tac \\ fs[MEM]
    \\ fs[eval_def,eval_to_def,gen_ltree_LNIL,v_limit_SOME]
    \\ first_assum (qspec_then ‘k’ assume_tac) \\ fs[]
    \\ qexists_tac ‘k'’ \\ fs []
    \\ imp_res_tac LIST_MAP_eval_to_not_diverge_mono)
QED

Triviality eval_to_atom_mono_res:
  eval_to c k x = Atom n ⇒
    k ≤ k1 ⇒ eval_to c k1 x = eval_to c k x
Proof
  rpt strip_tac
  \\ Cases_on ‘eval_to c k x’
  \\ Cases_on ‘ts’ \\ fs []
  \\ ‘eval_to c k x ≠ Diverge’ by (fs[])
  \\ imp_res_tac eval_to_res_mono_LNIL \\ fs[]
  \\ Cases_on ‘eval_to c k' x = ’
QED

Theorem getAtoms_eval_to_NONE:
   (getAtoms (MAP (eval c) es) = NONE ∧ ¬MEM Diverge (MAP (λa. eval_to c k a) es))
   ⇒  getAtoms (MAP (λa. eval_to c k a) es) = NONE
Proof
  rw[] \\ Induct_on ‘es’ \\ fs[]
  \\ rpt strip_tac
  \\ simp[getAtoms_def]
  \\ Cases_on ‘getAtoms (MAP (eval c) es)’ \\ fs[]
  \\ Cases_on ‘getAtom (eval_to c k h)’ \\ fs[]
  \\ fs[getAtoms_def]
  \\ Cases_on ‘getAtom (eval c h)’ \\ fs[]
  \\ fs [getAtom_NONE,getAtom_SOME,getAtom_def]
  \\ first_x_assum (qspec_then ‘x'’ assume_tac)
  \\ fs [eval_def,eval_to_def,eval_op_def,gen_ltree_LNIL,v_limit_SOME] \\ fs[]
  \\ first_x_assum (qspec_then ‘k’ assume_tac)
  \\ fs[]
  \\ imp_res_tac eval_to_atom_mono_res \\ fs[]
QED

Theorem getAtoms_eval_to_SOME:
   (getAtoms (MAP (eval c) es) = SOME l
   ∧ ¬MEM Diverge (MAP (λa. eval_to c k a) es))
   ⇒  getAtoms (MAP (λa. eval_to c k a) es) = SOME l
Proof
  qspec_tac (‘l’,‘l’)
  \\ Induct_on ‘es’ \\ fs[]
  \\ rpt strip_tac \\ fs[getAtoms_def]
  \\ ‘getAtom (eval_to c k h) = getAtom (eval c h)’ by (
     Cases_on ‘getAtom (eval c h)’ THEN1 (fs [getAtom_NONE])
     \\ fs [getAtom_SOME]
     \\ CCONTR_TAC
     \\ fs [eval_def,eval_to_def,eval_op_def,gen_ltree_LNIL,v_limit_SOME]
     \\ first_x_assum (qspec_then ‘k'’ assume_tac) \\ fs[]
     \\ qspec_then ‘h’ imp_res_tac (Q.GEN ‘x’ eval_to_not_div_not_eq_mono)
  ) \\ fs[]
  \\ Cases_on ‘getAtom (eval c h)’ THEN1 (fs[getAtom_NONE]) \\ fs[]
  \\ Cases_on ‘getAtoms (MAP (eval c) es)’ THEN1 (fs[])
  \\ last_x_assum (qspec_then ‘x'’ assume_tac) \\ fs[]
QED

(*****************************************************)

Theorem eval_If:
  eval c (If x y z) = (
    if eval c x = Diverge then Diverge  else
    if eval c x = True    then eval c y else
    if eval c x = False   then eval c z else Error)
Proof
  IF_CASES_TAC
  THEN1 (
    fs[eval_def,eval_to_def,gen_ltree_LNIL,v_limit_SOME]
    \\ qexists_tac ‘k’ \\ fs [eval_op_def])
  \\ ntac 2
   (IF_CASES_TAC
    THEN1
     (fs [eval_def,eval_to_def,gen_ltree_LNIL,v_limit_SOME]
      \\ fs[eval_op_def]
      \\ AP_TERM_TAC
      \\ fs [FUN_EQ_THM] \\ rw []
      \\ match_mp_tac v_limit_eq_add
      \\ qexists_tac ‘k’ \\ fs []
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ match_mp_tac v_limit_eq_add
      \\ qexists_tac ‘k’ \\ fs []))
  \\ fs [eval_def,eval_to_def,gen_ltree_LNIL,v_limit_SOME]
  \\ fs[eval_op_def]
  \\ last_x_assum (qspec_then ‘0’ assume_tac) \\ fs[]
  \\ rename [‘eval_to c k x ≠ Diverge’]
  \\ last_x_assum (qspec_then ‘k’ assume_tac) \\ fs[]
  \\ last_x_assum (qspec_then ‘k’ assume_tac) \\ fs[]
  \\ qexists_tac ‘MAX k'' k'’ \\ rpt strip_tac
  \\ fs[]
  \\ ‘k ≤ k'''’ by (fs[])
  \\ ‘eval_to c k''' x ≠ Diverge’ by (imp_res_tac eval_to_not_diverge_mono) \\ fs[]
  \\ imp_res_tac eval_to_not_diverge_not_eq_mono \\ fs[]
QED

Theorem eval_PrimOp:
  eval c (Prim (AtomOp (a:'a)) es) =
  (let xs = MAP (eval c) es in
   if MEM Diverge xs then Diverge else
      case OPTION_BIND (getAtoms xs) (c.parAtomOp a) of
       | (SOME n) => Atom n
       | _        => Error)
Proof
  fs[] \\ IF_CASES_TAC THEN1 (
       fs[eval_def,eval_to_def,gen_ltree_LNIL,v_limit_SOME]
    \\ qexists_tac ‘k’ \\ rpt strip_tac
    \\ fs [eval_op_def]
    \\ assume_tac eval_Diverge_IFF_eval_to_Diverge \\ fs []
  ) (*∀ e ∈ es ⇒ eval_to c k e does not diverge*)
  \\ ‘∃ k. ¬MEM Diverge (MAP (λa. eval_to c k a) es)’
    by ( assume_tac eval_Diverge_IFF_eval_to_Diverge \\ fs[] \\ qexists_tac ‘k’ \\ fs[])
  \\ Cases_on ‘ OPTION_BIND (getAtoms (MAP (eval c) es)) (c.parAtomOp a)’
    \\ fs[eval_def,eval_to_def,gen_ltree_LNIL,v_limit_SOME]
    \\ qexists_tac ‘k’ \\ rpt strip_tac
    \\ fs[eval_op_def]
    (*eval_to does not diverge for all k' k≤k'*)
    \\ qspecl_then [‘k''’,‘k’] imp_res_tac LIST_MAP_eval_to_not_diverge_mono \\ fs[]
  \\ imp_res_tac getAtoms_eval_to_NONE \\ fs[]
  \\ imp_res_tac getAtoms_eval_to_SOME \\ fs[]
QED

Theorem eval_Lit:
  eval c (Prim (Lit b) []) = Atom b ∧
  eval c (Prim (Lit b) (x::xs)) = Error
Proof
  rw [] \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
  \\ fs [v_limit_def,v_lookup_def]
QED

Theorem eval_Fail:
  eval c Fail = Error
Proof
  rw [] \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
  \\ fs [v_limit_def,v_lookup_def]
QED

Theorem eval_Prim:
  eval c (Prim op xs) = eval_op c op (MAP (eval c) xs)
Proof
  Cases_on ‘∃s. op = Cons s’
  THEN1 fs [eval_Cons,eval_op_def]
  \\ Cases_on ‘op = If’
  THEN1
   (Cases_on ‘∃x1 x2 x3. xs = [x1;x2;x3]’
    THEN1 (rw [] \\ fs [eval_If,eval_op_def] \\ rw [] \\ fs [])
    \\ fs []
    \\ rpt
       (rename [‘xs ≠ _’] \\ Cases_on ‘xs’ \\ fs [] THEN1
         (fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
          \\ fs [v_limit_def,v_lookup_def])))
  \\ Cases_on ‘∃s n. op = IsEq s n’
  THEN1
   (Cases_on ‘xs’ \\ fs [eval_op_def]
    \\ TRY (Cases_on ‘t’) \\ fs [eval_op_def,eval_IsEq]
    \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
    \\ fs [v_limit_def,v_lookup_def])
  \\ Cases_on ‘∃s i. op = Proj s i’
  THEN1
   (Cases_on ‘xs’ \\ fs [eval_op_def]
    THEN1
      (fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
       \\ fs [v_limit_def,v_lookup_def])
    \\ Cases_on ‘t’ \\ fs [eval_Proj,eval_op_def]
    \\ fs [eval_def,eval_to_def,Once gen_ltree,eval_op_def]
    \\ fs [v_limit_def,v_lookup_def])
  \\ Cases_on ‘op’ \\ fs []
  THEN1(fs [eval_PrimOp,eval_op_def])
  \\ Cases_on ‘xs’ \\ fs[eval_PrimOp,eval_op_def,eval_Lit]
QED

Theorem eval_core:
  eval c (Var s) = Error (* free variables are not allowed *) ∧
  eval c (Prim op xs) = eval_op c op (MAP (eval c) xs) ∧
  eval c (Lam s x) = Closure s x ∧
  eval c (Letrec f x) = eval c (subst_funs f x) ∧
  eval c (App x y) =
    (let v = eval c x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) => eval c (bind [(s,y)] body)) ∧
  eval c (Case x nm css) = eval c (expandCases x nm css)
Proof
  fs [eval_Var,eval_Prim,eval_Lam,eval_Letrec,eval_App,eval_Case]
QED

(*like eval_core, but extended with exp Overloads*)
Theorem eval_thm:
  eval c (Fail)  = Error ∧
  eval c (Var s) = Error (* free variables are not allowed *) ∧
  eval c (Cons s xs) = Constructor s (MAP (eval c) xs) ∧
  eval c (IsEq s n x) = is_eq c s n (eval c x) ∧
  eval c (Proj s i x) = el s i (eval c x) ∧
  eval c (Let s x y) = eval c (bind [(s,x)] y) ∧
  eval c (If x y z) = (
         if eval c x = Diverge then Diverge  else
         if eval c x = True    then eval c y else
         if eval c x = False   then eval c z else Error) ∧
  eval c (Lam s x) = Closure s x ∧
  eval c (Letrec f x) = eval c (subst_funs f x) ∧
  eval c (App x y) =
    (let v = eval c x in
       if v = Diverge then Diverge else
         case dest_Closure v of
         | NONE => Error
         | SOME (s,body) => eval c (bind [(s,y)] body)) ∧
  eval c (Case x nm css) = eval c (expandCases x nm css)
Proof
  fs [eval_Fail,eval_Var,eval_Cons,eval_App,eval_Lam,eval_If,eval_Proj,
      eval_IsEq,bind_def,eval_Letrec,eval_Case]
QED

(* prove that bottom diverges.

   bot x = bot x;
   eval bot (λx.x);
*)

Definition bottom_def:
  bottom =
    Letrec [("bot","n",App (Var "bot") (Lam "x" (Var "x")))]
      (App (Var "bot") (Lam "x" (Var "x")))
End

Triviality subst_id_fun:
  (subst n v (Lam "x" (Var "x"))) = (Lam "x" (Var "x"))
Proof
  Cases_on ‘n’ \\ Cases_on ‘v’
  \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
  \\ IF_CASES_TAC
  \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
QED

Theorem eval_bottom:
  ∀c. eval c bottom = Diverge
Proof
  strip_tac
  \\ qsuff_tac ‘∀k. eval_to c k bottom = Diverge’
  THEN1 fs [eval_def,v_limit_def,v_lookup_def,gen_ltree_LNIL]
  \\ strip_tac
  \\ fs [bottom_def,eval_to_def]
  \\ completeInduct_on ‘k’
  \\ Cases_on ‘k’
  \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
  \\ Cases_on ‘n’ THEN1 fs[eval_to_def]
  \\ first_assum (qspec_then ‘SUC n'’ assume_tac) \\ fs[]
  \\ simp[eval_to_def]
  \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
  \\ simp[eval_to_def]
  \\ fs [subst_def,subst_funs_def,bind_def,closed_def]
QED

(* example producing infinite list of λx.x*)

Definition zeros_def:
  zeros =
    Letrec [("z","n",Cons "cons" [Var "n"; App (Var "z") (Var "n")])]
      (App (Var "z") (Lam "x" (Var "x")))
End

Theorem eval_zeros:
  ∀ c. eval c zeros = Constructor "cons" [Closure "x" (Var "x"); eval c zeros]
Proof
  strip_tac
  \\ fs [Once zeros_def]
  \\ ntac 6 (simp [Once eval_thm,dest_Closure_def,subst_def,bind_def,
                   subst_funs_def,closed_def])
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ rewrite_tac [zeros_def]
  \\ ntac 2 (simp [Once eval_thm,dest_Closure_def,subst_def,bind_def,
                   subst_funs_def,closed_def])
QED


(* value and exp relation -- clocked *)

(*TODO, there might not be the need to parametrize v_rel' over c*)
Definition v_rel'_def:
  (v_rel' c 0 v1 v2 ⇔ T) ∧
  (v_rel' c (SUC n) v1 v2 ⇔
     (v1 = v2) ∨
     (∃m xs ys.
        v1 = Constructor m xs ∧
        v2 = Constructor m ys ∧
        LIST_REL (v_rel' c n) xs ys) ∨
     (∃s1 x1 s2 x2.
        v1 = Closure s1 x1 ∧
        v2 = Closure s2 x2 ∧
        ∀z. v_rel' c n (eval c (bind [(s1,z)] x1))
                       (eval c (bind [(s2,z)] x2))))
End

Definition v_rel_def:
  v_rel c x y = ∀n. v_rel' c n x y
End

Definition exp_rel_def:
  exp_rel c x y ⇔ v_rel c (eval c x) (eval c y)
End

Theorem v_rel_Closure:
  (∀x y. exp_rel c x y ⇒ exp_rel c (bind [m,x] b) (bind [n,y] d)) ⇒
  v_rel c (Closure m b) (Closure n d)
Proof
  rw [PULL_FORALL,exp_rel_def,v_rel_def] \\ fs []
  \\ rewrite_tac [eval_thm]
  \\ Cases_on ‘n'’
  \\ once_rewrite_tac [v_rel'_def] \\ fs [] \\ disj2_tac
  \\ rw [] \\ fs []
  \\ first_x_assum match_mp_tac
  \\ Cases \\ fs [v_rel'_def]
QED

Triviality LIST_REL_SYM:
  (∀x y. R x y ⇔ R y x) ⇒
  ∀xs ys. LIST_REL R xs ys ⇔ LIST_REL R ys xs
Proof
  strip_tac \\ Induct
  \\ fs [] \\ rw [] \\ eq_tac \\ rw [] \\ fs [] \\ metis_tac []
QED

Triviality LIST_REL_TRANS:
  (∀x y z. R x y ∧ R y z ⇒ R x z) ⇒
  ∀xs ys zs. LIST_REL R xs ys ∧ LIST_REL R ys zs ⇒ LIST_REL R xs zs
Proof
  strip_tac \\ Induct
  \\ fs [] \\ rw [] \\ fs [] \\ rw [] \\ fs [] \\ metis_tac []
QED

Triviality v_rel'_refl:
  ∀x n. v_rel' c n x x
Proof
  Cases_on ‘n’ \\ fs [v_rel'_def]
QED

Triviality v_rel'_sym:
  ∀n x y. v_rel' c n x y ⇔ v_rel' c n y x
Proof
  Induct_on ‘n’ \\ fs [v_rel'_def]
  \\ drule LIST_REL_SYM
  \\ metis_tac []
QED

Triviality v_rel'_trans:
  ∀n x y z. v_rel' c n x y ∧ v_rel' c n y z ⇒ v_rel' c n x z
Proof
  Induct_on ‘n’ \\ fs [v_rel'_def]
  \\ drule LIST_REL_TRANS
  \\ strip_tac \\ rw []
  THEN1 (res_tac \\ fs [])
  \\ disj2_tac \\ rw []
  \\ metis_tac [v_rel'_def]
QED

Theorem v_rel_refl:
  ∀x. v_rel c x x
Proof
  metis_tac [v_rel'_refl,v_rel_def]
QED

Theorem v_rel_sym:
  ∀x y. v_rel c x y ⇔ v_rel c y x
Proof
  metis_tac [v_rel'_sym,v_rel_def]
QED

Theorem v_rel_trans:
  ∀x y z. v_rel c x y ∧ v_rel c y z ⇒ v_rel c x z
Proof
  metis_tac [v_rel'_trans,v_rel_def]
QED

Definition isClos_def:
  isClos (Closure _ _) = T ∧ isClos _ = F
End

Theorem isClos_Lam[simp]:
  isClos (eval c (Lam v x))
Proof
  fs [eval_thm,isClos_def]
QED

Theorem isClos_thm:
  isClos x = ∃n e. x = Closure n e
Proof
  Cases_on ‘x’ \\ fs [isClos_def]
  \\ Cases_on ‘a’ \\ fs [isClos_def]
  \\ Cases_on ‘ts’ \\ fs [isClos_def]
QED

Theorem exp_rel_extend:
  ∀c x y z.
    isClos (eval c x) ∧ isClos (eval c y) ⇒
    (exp_rel c x y ⇔ ∀a. exp_rel c (App x a) (App y a))
Proof
  rw [exp_rel_def,eval_App]
  \\ Cases_on ‘~isClos (eval c y)’ \\ fs []
  \\ fs [isClos_thm]
  \\ fs [v_rel_def]
  \\ eq_tac \\ rw []
  THEN1
   (rename [‘v_rel' _ k’]
    \\ first_x_assum (qspec_then ‘SUC k’ mp_tac)
    \\ fs [v_rel'_def] \\ rw [] \\ fs []
    THEN1 (Cases_on ‘k’ \\ fs [v_rel'_def])
    \\ fs [])
  \\ rename [‘v_rel' _ k’]
  \\ Cases_on ‘k’ \\ fs [v_rel'_def]
QED

Theorem exp_rel_Cons:
  exp_rel c (Cons n xs) (Cons m ys) ⇔
  n = m ∧ LIST_REL (exp_rel c) xs ys
Proof
  fs [exp_rel_def,eval_Cons,v_rel_def,LIST_REL_EL_EQN]
  \\ eq_tac \\ rw []
  THEN1 (first_x_assum (qspec_then ‘SUC 0’ mp_tac) \\ fs [v_rel'_def] \\ rw [])
  THEN1
   (first_x_assum (qspec_then ‘SUC 0’ mp_tac) \\ fs [v_rel'_def]
    \\ fs [LIST_REL_EL_EQN] \\ rw [] \\ fs [MAP_EQ_EVERY2])
  THEN1
   (rename [‘v_rel' _ k’]
    \\ first_x_assum (qspec_then ‘SUC k’ mp_tac)
    \\ fs [v_rel'_def,MAP_EQ_EVERY2]
    \\ fs [LIST_REL_EL_EQN]
    \\ Cases_on ‘LENGTH xs = LENGTH ys’ \\ fs []
    \\ Cases_on ‘m = n’ \\ fs [EL_MAP]
    \\ rw [] \\ res_tac \\ fs []
    \\ Cases_on ‘k’ \\ fs [v_rel'_def])
  \\ rename [‘v_rel' _ k’]
  \\ Cases_on ‘k’ \\ fs [v_rel'_def]
  \\ disj2_tac
  \\ fs [LIST_REL_EL_EQN]
  \\ rfs [] \\ rw [] \\ fs [EL_MAP]
QED

Definition progress_def:
  progress c exp next =
    ∀input.
       exp_rel c (App exp input)
                 (case next input of
                  | INL final => final
                  | INR (n,x,rec_input) =>
                      Cons n [x; App exp rec_input])
End

Theorem progress_lemma:
  progress c exp1 next ∧ progress c exp2 next ∧
  isClos (eval c exp1) ∧ isClos (eval c exp2) ⇒
  exp_rel c exp1 exp2
Proof
  fs [exp_rel_extend,progress_def] \\ rw []
  \\ rw [exp_rel_def,v_rel_def]
  \\ qid_spec_tac ‘a’
  \\ completeInduct_on ‘n’ \\ fs [] \\ strip_tac
  \\ first_assum (qspec_then ‘a’ mp_tac)
  \\ last_assum (qspec_then ‘a’ mp_tac)
  \\ rewrite_tac [exp_rel_def,v_rel_def]
  \\ Cases_on ‘next a’ \\ fs []
  THEN1 metis_tac [v_rel'_trans,v_rel'_sym]
  \\ PairCases_on ‘y’ \\ fs [] \\ rw []
  \\ qsuff_tac ‘v_rel' c n
       (eval c (Cons y0 [y1; App exp1 y2]))
       (eval c (Cons y0 [y1; App exp2 y2]))’
  THEN1 metis_tac [v_rel'_trans,v_rel'_sym]
  \\ once_rewrite_tac [eval_thm] \\ rewrite_tac [MAP]
  \\ Cases_on ‘n’ \\ fs [v_rel'_def,v_rel'_refl]
QED

val _ = export_theory();
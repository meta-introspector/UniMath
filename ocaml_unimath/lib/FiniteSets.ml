open DecidablePropositions
open NaturalNumbers
open NegativePropositions
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets
open StandardFiniteSets
open Subtypes

let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'x nelstruct = (stn, 'x) weq

(** val nelstructToFunction : nat -> 'a1 nelstruct -> stn -> 'a1 **)

let nelstructToFunction _ =
  pr1weq

(** val nelstructonstn : nat -> stn nelstruct **)

let nelstructonstn _ =
  idweq

(** val nelstructweqf :
    nat -> ('a1, 'a2) weq -> 'a1 nelstruct -> 'a2 nelstruct **)

let nelstructweqf _ w sx =
  weqcomp sx w

(** val nelstructweqb :
    nat -> ('a1, 'a2) weq -> 'a2 nelstruct -> 'a1 nelstruct **)

let nelstructweqb _ w sy =
  weqcomp sy (invweq w)

(** val nelstructonempty : empty nelstruct **)

let nelstructonempty = false
  (* weqstn0toempty *)

(** val nelstructonempty2 : 'a1 neg -> 'a1 nelstruct **)

let nelstructonempty2 nx =
  weqcomp weqstn0toempty (invweq (weqtoempty nx))

(** val nelstructonunit : coq_unit nelstruct **)

let nelstructonunit =
  weqstn1tounit

(** val nelstructoncontr : 'a1 iscontr -> 'a1 nelstruct **)

let nelstructoncontr contrx =
  weqcomp weqstn1tounit (invweq (weqcontrtounit contrx))

(** val nelstructonbool : bool nelstruct **)

let nelstructonbool =
  weqstn2tobool

(** val nelstructoncoprodwithunit :
    nat -> 'a1 nelstruct -> ('a1, coq_unit) coprod nelstruct **)

let nelstructoncoprodwithunit n sx =
  weqcomp (invweq (weqdnicoprod n (lastelement n))) (weqcoprodf1 sx)

(** val nelstructoncompl :
    nat -> 'a1 -> 'a1 nelstruct -> 'a1 compl nelstruct **)

let nelstructoncompl n x sx =
  weqcomp (weqdnicompl n (pr1weq (invweq sx) x))
    (weqcomp
      (compl_weq_compl_ne (pr1weq (invweq sx) x)
        (stnneq (S n) (pr1weq (invweq sx) x)))
      (invweq (weqoncompl (invweq sx) x)))

(** val nelstructoncoprod :
    nat -> nat -> 'a1 nelstruct -> 'a2 nelstruct -> ('a1, 'a2) coprod
    nelstruct **)

let nelstructoncoprod n m sx sy =
  weqcomp (invweq (weqfromcoprodofstn n m)) (weqcoprodf sx sy)

(** val nelstructontotal2 :
    nat -> ('a1 -> nat) -> 'a1 nelstruct -> ('a1 -> 'a2 nelstruct) -> ('a1,
    'a2) total2 nelstruct **)

let nelstructontotal2 n f sx fs =
  weqcomp
    (invweq
      (weqstnsum n (funcomp (nelstructToFunction n sx) f)
        (funcomp (nelstructToFunction n sx) fs))) (weqfp sx)

(** val nelstructondirprod :
    nat -> nat -> 'a1 nelstruct -> 'a2 nelstruct -> ('a1, 'a2) dirprod
    nelstruct **)

let nelstructondirprod n m sx sy =
  weqcomp (invweq (weqfromprodofstn n m)) (weqdirprodf sx sy)

(** val nelstructonfun :
    nat -> nat -> 'a1 nelstruct -> 'a2 nelstruct -> ('a1 -> 'a2) nelstruct **)

let nelstructonfun n m sx sy =
  weqcomp (invweq (weqfromfunstntostn n m))
    (weqcomp (weqffun sy) (weqbfun (invweq sx)))

(** val nelstructonforall :
    nat -> ('a1 -> nat) -> 'a1 nelstruct -> ('a1 -> 'a2 nelstruct) -> ('a1 ->
    'a2) nelstruct **)

let nelstructonforall n f sx fs =
  invweq
    (weqcomp (weqonsecbase sx)
      (weqstnprod n (funcomp (nelstructToFunction n sx) f) (fun i ->
        fs (nelstructToFunction n sx i))))

(** val nelstructonweq : nat -> 'a1 nelstruct -> ('a1, 'a1) weq nelstruct **)

let nelstructonweq n sx =
  weqcomp (invweq (weqfromweqstntostn n))
    (weqcomp (weqbweq (invweq sx)) (weqfweq sx))

(** val isofnel : nat -> hProp **)

let isofnel _ =
  ishinh

(** val isofneluniv :
    nat -> hProp -> ('a1 nelstruct -> hProptoType) -> hProptoType ->
    hProptoType **)

let isofneluniv _ =
  hinhuniv

(** val isofnelstn : nat -> hProptoType **)

let isofnelstn n =
  hinhpr (nelstructonstn n)

(** val isofnelweqf : nat -> ('a1, 'a2) weq -> hProptoType -> hProptoType **)

let isofnelweqf n w sx =
  hinhfun (nelstructweqf n w) sx

(** val isofnelweqb : nat -> ('a1, 'a2) weq -> hProptoType -> hProptoType **)

let isofnelweqb n w sy =
  hinhfun (nelstructweqb n w) sy

(** val isofnelempty : hProptoType **)

let isofnelempty =
  hinhpr nelstructonempty

(** val isofnelempty2 : 'a1 neg -> hProptoType **)

let isofnelempty2 nx =
  hinhpr (nelstructonempty2 nx)

(** val isofnelunit : hProptoType **)

let isofnelunit =
  hinhpr nelstructonunit

(** val isofnelcontr : 'a1 iscontr -> hProptoType **)

let isofnelcontr contrx =
  hinhpr (nelstructoncontr contrx)

(** val isofnelbool : hProptoType **)

let isofnelbool =
  hinhpr nelstructonbool

(** val isofnelcoprodwithunit : nat -> hProptoType -> hProptoType **)

let isofnelcoprodwithunit n sx =
  hinhfun (nelstructoncoprodwithunit n) sx

(** val isofnelcompl : nat -> 'a1 -> hProptoType -> hProptoType **)

let isofnelcompl n x sx =
  hinhfun (nelstructoncompl n x) sx

(** val isofnelcoprod :
    nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let isofnelcoprod n m sx sy =
  hinhfun2 (nelstructoncoprod n m) sx sy

(** val isofnelondirprod :
    nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let isofnelondirprod n m sx sy =
  hinhfun2 (nelstructondirprod n m) sx sy

(** val isofnelonfun :
    nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let isofnelonfun n m sx sy =
  hinhfun2 (nelstructonfun n m) sx sy

(** val isofnelonweq : nat -> hProptoType -> hProptoType **)

let isofnelonweq n sx =
  hinhfun (nelstructonweq n) sx

type 'x finstruct = (nat, 'x nelstruct) total2

(** val finstruct_cardinality : 'a1 finstruct -> nat **)

let finstruct_cardinality fs =
  fs.pr1

(** val finstructToFunction : 'a1 finstruct -> 'a1 nelstruct **)

let finstructToFunction s =
  s.pr2

(** val make_finstruct : nat -> (stn, 'a1) weq -> 'a1 finstruct **)

let make_finstruct n w =
  { pr1 = n; pr2 = w }

(** val finstructonstn : nat -> stn finstruct **)

let finstructonstn n =
  make_finstruct n (nelstructonstn n)

(** val finstructweqf : ('a1, 'a2) weq -> 'a1 finstruct -> 'a2 finstruct **)

let finstructweqf w sx =
  make_finstruct sx.pr1 (nelstructweqf sx.pr1 w (finstructToFunction sx))

(** val finstructweqb : ('a1, 'a2) weq -> 'a2 finstruct -> 'a1 finstruct **)

let finstructweqb w sy =
  make_finstruct sy.pr1 (nelstructweqb sy.pr1 w (finstructToFunction sy))

(** val finstructonempty : empty finstruct **)

let finstructonempty =
  make_finstruct O nelstructonempty

(** val finstructonempty2 : 'a1 neg -> 'a1 finstruct **)

let finstructonempty2 nx =
  make_finstruct O (nelstructonempty2 nx)

(** val finstructonunit : coq_unit finstruct **)

let finstructonunit =
  make_finstruct (S O) nelstructonunit

(** val finstructoncontr : 'a1 iscontr -> 'a1 finstruct **)

let finstructoncontr xcontr =
  make_finstruct (S O) (nelstructoncontr xcontr)

(** val finstructonbool : bool finstruct **)

let finstructonbool =
  make_finstruct (S (S O)) nelstructonbool

(** val finstructoncoprodwithunit :
    'a1 finstruct -> ('a1, coq_unit) coprod finstruct **)

let finstructoncoprodwithunit sx =
  make_finstruct (S sx.pr1)
    (nelstructoncoprodwithunit sx.pr1 (finstructToFunction sx))

(** val finstructoncompl : 'a1 -> 'a1 finstruct -> 'a1 compl finstruct **)

let finstructoncompl x sx =
  let n = sx.pr1 in
  let w = sx.pr2 in
  (match n with
   | O -> fromempty (negstn0 (pr1weq (invweq w) x))
   | S n0 -> make_finstruct n0 (nelstructoncompl n0 x w))

(** val finstructoncoprod :
    'a1 finstruct -> 'a2 finstruct -> ('a1, 'a2) coprod finstruct **)

let finstructoncoprod sx sy =
  make_finstruct (add sx.pr1 sy.pr1)
    (nelstructoncoprod sx.pr1 sy.pr1 (finstructToFunction sx)
      (finstructToFunction sy))

(** val finstructontotal2 :
    'a1 finstruct -> ('a1 -> 'a2 finstruct) -> ('a1, 'a2) total2 finstruct **)

let finstructontotal2 sx fs =
  make_finstruct
    (stnsum sx.pr1
      (funcomp (nelstructToFunction sx.pr1 (finstructToFunction sx))
        (fun x -> finstruct_cardinality (fs x))))
    (nelstructontotal2 sx.pr1 (fun x -> finstruct_cardinality (fs x))
      (finstructToFunction sx) (fun x -> finstructToFunction (fs x)))

(** val finstructondirprod :
    'a1 finstruct -> 'a2 finstruct -> ('a1, 'a2) dirprod finstruct **)

let finstructondirprod sx sy =
  make_finstruct (mul sx.pr1 sy.pr1)
    (nelstructondirprod sx.pr1 sy.pr1 (finstructToFunction sx)
      (finstructToFunction sy))

(** val finstructondecsubset :
    ('a1 -> bool) -> 'a1 finstruct -> ('a1, bool) hfiber finstruct **)

let finstructondecsubset f sx =
  make_finstruct
    (weqfromdecsubsetofstn sx.pr1
      (funcomp (nelstructToFunction sx.pr1 (finstructToFunction sx)) f)).pr1
    (weqcomp
      (invweq
        (weqfromdecsubsetofstn sx.pr1
          (funcomp (nelstructToFunction sx.pr1 (finstructToFunction sx)) f)).pr2)
      (weqhfibersgwtog (finstructToFunction sx) f Coq_true))

(** val finstructonfun :
    'a1 finstruct -> 'a2 finstruct -> ('a1 -> 'a2) finstruct **)

let finstructonfun sx sy =
  make_finstruct (natpower sy.pr1 sx.pr1)
    (nelstructonfun sx.pr1 sy.pr1 (finstructToFunction sx)
      (finstructToFunction sy))

(** val finstructonforall :
    'a1 finstruct -> ('a1 -> 'a2 finstruct) -> ('a1 -> 'a2) finstruct **)

let finstructonforall sx fs =
  make_finstruct
    (stnprod sx.pr1
      (funcomp (nelstructToFunction sx.pr1 (finstructToFunction sx))
        (fun x -> (fs x).pr1)))
    (nelstructonforall sx.pr1 (fun x -> (fs x).pr1) (finstructToFunction sx)
      (fun x -> finstructToFunction (fs x)))

(** val finstructonweq : 'a1 finstruct -> ('a1, 'a1) weq finstruct **)

let finstructonweq sx =
  make_finstruct (factorial sx.pr1)
    (nelstructonweq sx.pr1 (finstructToFunction sx))

(** val isfinite : hProp **)

let isfinite =
  ishinh

(** val isfinite_isdeceq : hProptoType -> 'a1 isdeceq **)

let isfinite_isdeceq isfin =
  factor_through_squash isapropisdeceq (fun fstruct ->
    isdeceqweqf fstruct.pr2 (isdeceqstn (finstruct_cardinality fstruct)))
    isfin

(** val isfinite_isaset : hProptoType -> 'a1 isaset **)

let isfinite_isaset isfin =
  factor_through_squash isapropisaset (fun f ->
    Obj.magic isofhlevelweqf (S (S O)) f.pr2
      (isasetstn (finstruct_cardinality f))) isfin

(** val fincard : hProptoType -> nat **)

let fincard xf =
  squash_pairs_to_set isasetnat (fun n n' w w' ->
    weqtoeqstn n n' (weqcomp w (invweq w'))) xf

(** val ischoicebasefiniteset : hProptoType -> hProptoType **)

let ischoicebasefiniteset xf =
  hinhuniv ischoicebase (fun x0 ->
    let n = x0.pr1 in let w = x0.pr2 in ischoicebaseweqf w (ischoicebasestn n))
    xf

(** val isfinitestn : nat -> hProptoType **)

let isfinitestn n =
  hinhpr (finstructonstn n)

(** val isfiniteweqf : ('a1, 'a2) weq -> hProptoType -> hProptoType **)

let isfiniteweqf w sx =
  hinhfun (finstructweqf w) sx

(** val isfiniteweqb : ('a1, 'a2) weq -> hProptoType -> hProptoType **)

let isfiniteweqb w sy =
  hinhfun (finstructweqb w) sy

(** val isfiniteempty : hProptoType **)

let isfiniteempty =
  hinhpr finstructonempty

(** val isfiniteempty2 : 'a1 neg -> hProptoType **)

let isfiniteempty2 nx =
  hinhpr (finstructonempty2 nx)

(** val isfiniteunit : hProptoType **)

let isfiniteunit =
  hinhpr finstructonunit

(** val isfinitecontr : 'a1 iscontr -> hProptoType **)

let isfinitecontr contrx =
  hinhpr (finstructoncontr contrx)

(** val isfinitebool : hProptoType **)

let isfinitebool =
  hinhpr finstructonbool

(** val isfinitecoprodwithunit : hProptoType -> hProptoType **)

let isfinitecoprodwithunit sx =
  hinhfun finstructoncoprodwithunit sx

(** val isfinitecompl : 'a1 -> hProptoType -> hProptoType **)

let isfinitecompl x sx =
  hinhfun (finstructoncompl x) sx

(** val isfinitecoprod : hProptoType -> hProptoType -> hProptoType **)

let isfinitecoprod sx sy =
  hinhfun2 finstructoncoprod sx sy

(** val isfinitetotal2 :
    hProptoType -> ('a1 -> hProptoType) -> hProptoType **)

let isfinitetotal2 sx fs =
  let fs' = Obj.magic ischoicebasefiniteset sx __ fs in
  hinhfun2 (fun x x0 -> finstructontotal2 x0 x) fs' sx

(** val isfinitedirprod : hProptoType -> hProptoType -> hProptoType **)

let isfinitedirprod sx sy =
  hinhfun2 finstructondirprod sx sy

(** val isfinitedecsubset : ('a1 -> bool) -> hProptoType -> hProptoType **)

let isfinitedecsubset f sx =
  hinhfun (finstructondecsubset f) sx

(** val isfinitefun : hProptoType -> hProptoType -> hProptoType **)

let isfinitefun sx sy =
  hinhfun2 finstructonfun sx sy

(** val isfiniteforall :
    hProptoType -> ('a1 -> hProptoType) -> hProptoType **)

let isfiniteforall sx fs =
  let fs' = Obj.magic ischoicebasefiniteset sx __ fs in
  hinhfun2 (fun a b -> finstructonforall b a) fs' sx

(** val isfiniteweq : hProptoType -> hProptoType **)

let isfiniteweq sx =
  hinhfun finstructonweq sx

(** val isfinite_to_DecidableEquality :
    hProptoType -> 'a1 coq_DecidableRelation **)

let isfinite_to_DecidableEquality fin x y =
  isdecprop_to_DecidableProposition
    (isdecpropif (isfinite_isaset fin x y) (isfinite_isdeceq fin x y))

(** val subsetFiniteness :
    hProptoType -> 'a1 coq_DecidableSubtype -> hProptoType **)

let subsetFiniteness is p =
  let fin = isfinitedecsubset (fun x -> choice (p x) Coq_true Coq_false) is in
  isfiniteweqf (decidableSubtypeCarrier_weq p) fin

(** val fincard_subset : hProptoType -> 'a1 coq_DecidableSubtype -> nat **)

let fincard_subset fx p =
  fincard (subsetFiniteness fx p)

(** val fincard_standardSubset : nat -> stn coq_DecidableSubtype -> nat **)

let fincard_standardSubset n p =
  fincard (subsetFiniteness (isfinitestn n) p)

(** val bound01 : coq_DecidableProposition -> hProptoType **)

let bound01 p =
  let c = (decidabilityProperty p).pr1 in
  (match c with
   | Coq_ii1 _ -> Obj.magic Coq_paths_refl
   | Coq_ii2 _ -> Obj.magic Coq_paths_refl)

(** val tallyStandardSubset : nat -> stn coq_DecidableSubtype -> stn **)

let tallyStandardSubset n p =
  { pr1 = (stnsum n (fun x -> choice (p x) (S O) O)); pr2 =
    (natlehtolthsn (stnsum n (fun x -> choice (p x) (S O) O)) n
      (istransnatleh (stnsum n (fun x -> choice (p x) (S O) O))
        (stnsum n (fun _ -> S O)) n
        (stnsum_le n (fun x -> choice (p x) (S O) O) (fun _ -> S O) (fun i ->
          bound01 (p i))) (let r = stnsum n (fun _ -> S O) in isreflnatleh r))) }

(** val tallyStandardSubsetSegment :
    nat -> stn coq_DecidableSubtype -> stn -> stn **)

let tallyStandardSubsetSegment n p i =
  let k =
    tallyStandardSubset (stntonat n i) (fun j ->
      p (stnmtostnn (stntonat n i) n (natlthtoleh (stntonat n i) n i.pr2) j))
  in
  stnmtostnn (S (stntonat n i)) n (natlthtolehsn (stntonat n i) n i.pr2) k

type finite_subset = (pr1hSet hsubtype, hProptoType) total2

(** val make_finite_subset :
    hSet -> pr1hSet hsubtype -> hProptoType -> finite_subset **)

let make_finite_subset _ a p =
  { pr1 = a; pr2 = p }

(** val subtype_from_finite_subset :
    hSet -> finite_subset -> pr1hSet hsubtype **)

let subtype_from_finite_subset _ a =
  a.pr1

(** val isfinite_singleton : hSet -> pr1hSet -> hProptoType **)

let isfinite_singleton x x0 = x x0
  (* isfinitecontr (iscontr_singleton x x0) *)

(** val finite_singleton : hSet -> pr1hSet -> finite_subset **)

let finite_singleton x x0 = x x0
  (* make_finite_subset x (singleton x0) (isfinite_singleton x x0) *)

(** val finite_singleton_is_in :
    hSet -> pr1hSet hsubtype -> pr1hSet carrier -> hProptoType **)

let finite_singleton_is_in _ = false
  (* singleton_is_in *)

type coq_FiniteSet = (coq_UU, hProptoType) total2

(** val isfinite_to_FiniteSet : hProptoType -> coq_FiniteSet **)

let isfinite_to_FiniteSet f =
  { pr1 = __; pr2 = f }

(** val coq_FiniteSet_to_hSet : coq_FiniteSet -> hSet **)

let coq_FiniteSet_to_hSet x =
  make_hSet (isfinite_isaset x.pr2)

(** val coq_FiniteSetSum :
    coq_FiniteSet -> (pr1hSet -> coq_FiniteSet) -> coq_FiniteSet **)

let coq_FiniteSetSum i x =
  { pr1 = __; pr2 = (isfinitetotal2 i.pr2 (fun i0 -> (x i0).pr2)) }

(** val cardinalityFiniteSet : coq_FiniteSet -> nat **)

let cardinalityFiniteSet x =
  fincard x.pr2

(** val standardFiniteSet : nat -> coq_FiniteSet **)

let standardFiniteSet n =
  isfinite_to_FiniteSet (isfinitestn n)

(** val subsetFiniteSet :
    coq_FiniteSet -> pr1hSet coq_DecidableSubtype -> coq_FiniteSet **)

let subsetFiniteSet x p =
  isfinite_to_FiniteSet (subsetFiniteness x.pr2 p)

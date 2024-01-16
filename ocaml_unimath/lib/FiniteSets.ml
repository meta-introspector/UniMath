open PartA
open Preamble
open Propositions
open Sets
open StandardFiniteSets

let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'x nelstruct = (stn, 'x) weq

(** val nelstructToFunction : nat -> 'a1 nelstruct -> stn -> 'a1 **)

let nelstructToFunction _ =
  pr1weq

(** val nelstructonstn : nat -> stn nelstruct **)

let nelstructonstn _ =
  idweq

(** val nelstructontotal2 :
    nat -> ('a1 -> nat) -> 'a1 nelstruct -> ('a1 -> 'a2 nelstruct) -> ('a1,
    'a2) total2 nelstruct **)

let nelstructontotal2 n f sx fs =
  weqcomp
    (invweq
      (weqstnsum n (funcomp (nelstructToFunction n sx) f)
        (funcomp (nelstructToFunction n sx) fs))) (weqfp sx)

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

(** val finstructontotal2 :
    'a1 finstruct -> ('a1 -> 'a2 finstruct) -> ('a1, 'a2) total2 finstruct **)

let finstructontotal2 sx fs =
  make_finstruct
    (stnsum sx.pr1
      (funcomp (nelstructToFunction sx.pr1 (finstructToFunction sx))
        (fun x -> finstruct_cardinality (fs x))))
    (nelstructontotal2 sx.pr1 (fun x -> finstruct_cardinality (fs x))
      (finstructToFunction sx) (fun x -> finstructToFunction (fs x)))

(** val ischoicebasefiniteset : hProptoType -> hProptoType **)

let ischoicebasefiniteset xf =
  hinhuniv ischoicebase (fun x0 ->
    let n = x0.pr1 in let w = x0.pr2 in ischoicebaseweqf w (ischoicebasestn n))
    xf

(** val isfinitestn : nat -> hProptoType **)

let isfinitestn n =
  hinhpr (finstructonstn n)

(** val isfinitetotal2 :
    hProptoType -> ('a1 -> hProptoType) -> hProptoType **)

let isfinitetotal2 sx fs =
  let fs' = Obj.magic ischoicebasefiniteset sx __ fs in
  hinhfun2 (fun x x0 -> finstructontotal2 x0 x) fs' sx

type coq_FiniteSet = (coq_UU, hProptoType) total2

(** val isfinite_to_FiniteSet : hProptoType -> coq_FiniteSet **)

let isfinite_to_FiniteSet f =
  { pr1 = __; pr2 = f }

(** val coq_FiniteSetSum :
    coq_FiniteSet -> (pr1hSet -> coq_FiniteSet) -> coq_FiniteSet **)

let coq_FiniteSetSum i x =
  { pr1 = __; pr2 = (isfinitetotal2 i.pr2 (fun i0 -> (x i0).pr2)) }

(** val standardFiniteSet : nat -> coq_FiniteSet **)

let standardFiniteSet n =
  isfinite_to_FiniteSet (isfinitestn n)

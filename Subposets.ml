open PartB
open Preamble
open Propositions
open Sets

type coq_Subposet = pr1hSet hsubtype

type coq_Subposet' =
  (coq_Poset, (posetmorphism, (pr1hSet, pr1hSet) isincl) total2) total2

(** val coq_Subposet'_to_Poset : coq_Poset -> coq_Subposet' -> coq_Poset **)

let coq_Subposet'_to_Poset _ s =
  s.pr1

(** val coq_Subposet_to_Subposet' :
    coq_Poset -> coq_Subposet -> coq_Subposet' **)

let coq_Subposet_to_Subposet' x s =
  { pr1 = { pr1 = (carrier_subset (carrierofposet x) s); pr2 = { pr1 =
    (fun s0 t -> posetRelation x (Obj.magic s0).pr1 (Obj.magic t).pr1); pr2 =
    { pr1 = { pr1 = (fun s0 t u ->
    istrans_posetRelation x (Obj.magic s0).pr1 (Obj.magic t).pr1
      (Obj.magic u).pr1); pr2 = (fun s0 ->
    isrefl_posetRelation x (Obj.magic s0).pr1) }; pr2 = (fun s0 t a b ->
    Obj.magic subtypePath_prop s s0 t
      (isantisymm_posetRelation x (Obj.magic s0).pr1 (Obj.magic t).pr1 a b)) } } };
    pr2 = { pr1 = { pr1 = (Obj.magic pr1carrier s); pr2 = (fun _ _ a -> a) };
    pr2 = (isinclpr1carrier s) } }

(** val coq_Subposet'_to_Subposet :
    coq_Poset -> coq_Subposet' -> coq_Subposet **)

let coq_Subposet'_to_Subposet _ _ _ =
  ishinh

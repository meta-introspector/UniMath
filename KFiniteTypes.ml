open FiniteSets
open PartA
open PartA0
open Preamble
open Propositions
open StandardFiniteSets

type 'x kfinstruct = (nat, (stn -> 'x, (stn, 'x) issurjective) total2) total2

(** val make_kfinstruct :
    nat -> (stn -> 'a1) -> (stn, 'a1) issurjective -> 'a1 kfinstruct **)

let make_kfinstruct n f fsurjective =
  { pr1 = n; pr2 = { pr1 = f; pr2 = fsurjective } }

(** val kfinstruct_cardinality : 'a1 kfinstruct -> nat **)

let kfinstruct_cardinality f =
  f.pr1

(** val kfinstruct_map : 'a1 kfinstruct -> stn -> 'a1 **)

let kfinstruct_map f =
  f.pr2.pr1

(** val issurjective_kfinstruct :
    'a1 kfinstruct -> (stn, 'a1) issurjective **)

let issurjective_kfinstruct f =
  f.pr2.pr2

(** val kfinstruct_from_surjection :
    ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> 'a1 kfinstruct -> 'a2
    kfinstruct **)

let kfinstruct_from_surjection g gsurjective f =
  make_kfinstruct (kfinstruct_cardinality f) (funcomp (kfinstruct_map f) g)
    (issurjcomp (kfinstruct_map f) g (issurjective_kfinstruct f) gsurjective)

(** val kfinstruct_weqb :
    ('a1, 'a2) weq -> 'a2 kfinstruct -> 'a1 kfinstruct **)

let kfinstruct_weqb w =
  kfinstruct_from_surjection (invmap w)
    (issurjectiveweq (invmap w) (isweqinvmap w))

(** val kfinstruct_finstruct : 'a1 finstruct -> 'a1 kfinstruct **)

let kfinstruct_finstruct finstr =
  make_kfinstruct finstr.pr1 (let x0 = finstr.pr2 in x0.pr1)
    (issurjectiveweq (let x0 = finstr.pr2 in x0.pr1) (weqproperty finstr.pr2))

(** val kfinstruct_stn : nat -> stn kfinstruct **)

let kfinstruct_stn n =
  make_kfinstruct n idfun issurjective_idfun

(** val kfinstruct_stn_indexed :
    nat -> (stn -> 'a1 kfinstruct) -> (stn, 'a1) total2 kfinstruct **)

let kfinstruct_stn_indexed n index =
  let j = fun j -> kfinstruct_cardinality (index j) in
  kfinstruct_from_surjection
    (totalfun (let x = fun k -> (index k).pr2 in fun k -> (x k).pr1))
    (issurjective_totalfun
      (let x = fun k -> (index k).pr2 in fun k -> (x k).pr1) (fun x ->
      issurjective_kfinstruct (index x)))
    (kfinstruct_weqb (weqstnsum1 n j) (kfinstruct_stn (stnsum n j)))

type 'x iskfinite = hProptoType

(** val kfinstruct_iskfinite : 'a1 kfinstruct -> 'a1 iskfinite **)

let kfinstruct_iskfinite =
  hinhpr

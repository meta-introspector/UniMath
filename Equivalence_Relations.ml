open GraphPaths
open Preamble
open Propositions
open Sets

(** val eqrel_closure_hrel : 'a1 hrel -> 'a1 hrel **)

let eqrel_closure_hrel _ _ _ =
  ishinh

(** val iseqrel_closure : 'a1 hrel -> 'a1 iseqrel **)

let iseqrel_closure r =
  iseqrelconstr (eqrel_closure_hrel r) (fun x y z -> hinhfun2 (concat x y z))
    (fun x -> hinhpr (nil x)) (fun x y -> hinhfun (reverse_in_closure x y))

(** val eqrel_closure : 'a1 hrel -> 'a1 eqrel **)

let eqrel_closure r =
  make_eqrel (eqrel_closure_hrel r) (iseqrel_closure r)

(** val eqrel_closure_minimal :
    'a1 hrel -> 'a1 eqrel -> ('a1 -> 'a1 -> hProptoType -> hProptoType) ->
    'a1 -> 'a1 -> hProptoType -> hProptoType **)

let eqrel_closure_minimal _ s h x x' =
  hinhuniv (pr1eqrel s x x')
    (gpaths_ind x' (eqrelrefl s x') (fun x0 y r _ hS ->
      eqreltrans s x0 y x'
        (match r with
         | Coq_ii1 a -> h x0 y a
         | Coq_ii2 b -> eqrelsymm s y x0 (h y x0 b)) hS) x)

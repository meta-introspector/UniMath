open PartA
open PartB
open PartC
open Preamble

type 'a maybe = ('a, coq_unit) coprod

(** val just : 'a1 -> 'a1 maybe **)

let just x =
  Coq_ii1 x

(** val nothing : 'a1 maybe **)

let nothing =
  Coq_ii2 Coq_tt

(** val just_injectivity : 'a1 -> 'a1 -> 'a1 maybe paths -> 'a1 paths **)

let just_injectivity =
  ii1_injectivity

(** val isasetmaybe : 'a1 isaset -> 'a1 maybe isaset **)

let isasetmaybe h =
  isasetcoprod h isasetunit

(** val flatmap : ('a1 -> 'a2 maybe) -> 'a1 maybe -> 'a2 maybe **)

let flatmap f = function
| Coq_ii1 a -> f a
| Coq_ii2 _ -> nothing

(** val flatmap_just : ('a1 -> 'a2 maybe) -> 'a1 -> 'a2 maybe paths **)

let flatmap_just _ _ =
  Coq_paths_refl

(** val flatmap_nothing : ('a1 -> 'a2 maybe) -> 'a2 maybe paths **)

let flatmap_nothing _ =
  Coq_paths_refl

(** val flatmap_ind : 'a3 -> ('a1 -> 'a3) -> 'a1 maybe -> 'a3 **)

let flatmap_ind pnothing pjust = function
| Coq_ii1 a -> pjust a
| Coq_ii2 _ -> pnothing

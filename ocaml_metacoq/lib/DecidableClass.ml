open Datatypes

type coq_Decidable =
  bool
  (* singleton inductive, whose constructor was Build_Decidable *)

(** val coq_Decidable_witness : coq_Decidable -> bool **)

let coq_Decidable_witness decidable =
  decidable

(** val decide : coq_Decidable -> bool **)

let decide =
  coq_Decidable_witness

(** val coq_Decidable_not : coq_Decidable -> coq_Decidable **)

let coq_Decidable_not h =
  negb (coq_Decidable_witness h)
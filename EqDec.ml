open Classes
open Specif

(** val coq_UIP_K : 'a1 -> 'a2 -> 'a2 **)

let coq_UIP_K _ peq =
  peq

(** val coq_K_dec : 'a1 coq_EqDec -> 'a1 -> 'a2 -> 'a2 **)

let coq_K_dec _ _ x =
  x

(** val coq_K_dec_point : 'a1 -> 'a1 coq_EqDecPoint -> 'a2 -> 'a2 **)

let coq_K_dec_point _ _ x =
  x

(** val eq_eqdec : 'a1 coq_EqDec -> 'a1 -> 'a1 -> sumbool **)

let eq_eqdec _ _ _ =
  Coq_left


type __ = Obj.t

(** val eq_elim : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let eq_elim _ f _ =
  f

(** val eq_elim_r : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let eq_elim_r _ p _ =
  p

(** val transport : 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let transport _ _ x =
  x

(** val transport_r : 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let transport_r _ _ x =
  x

(** val inspect : 'a1 -> 'a1 **)

let inspect x =
  x

(** val coq_False_rect_dep : __ -> 'a1 **)

let coq_False_rect_dep _ =
  assert false (* absurd case *)

(** val coq_True_rect_dep : 'a1 -> 'a1 **)

let coq_True_rect_dep m =
  m

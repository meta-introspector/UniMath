
(** val flipsec : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flipsec f x y =
  f y x

open PartB
open Preamble

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type decSet = (coq_UU, __ isdeceq) total2

(** val make_decSet : 'a1 isdeceq -> decSet **)

let make_decSet i =
  { pr1 = __; pr2 = (Obj.magic i) }

type pr1decSet = __

(** val decproperty : decSet -> __ isdeceq **)

let decproperty x =
  x.pr2

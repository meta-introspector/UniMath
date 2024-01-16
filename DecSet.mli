open PartB
open Preamble

type __ = Obj.t

type decSet = (coq_UU, __ isdeceq) total2

val make_decSet : 'a1 isdeceq -> decSet

type pr1decSet = __

val decproperty : decSet -> __ isdeceq

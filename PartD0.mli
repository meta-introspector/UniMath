open PartA
open PartD
open Preamble
open UnivalenceAxiom

type __ = Obj.t

val eqweqmap_transportb : __ paths -> ('a2 -> 'a1) paths

val eqweqmap_weqtopaths : ('a1, 'a2) weq -> ('a1, 'a2) weq paths

val sum_of_fibers : ('a1 -> 'a2) -> (('a2, ('a1, 'a2) hfiber) total2, 'a1) weq

type 'a display = (__, 'a) hfiber

val totalfst : (__, __ -> 'a1) total2

val totalfst_display : (__, __ -> 'a1) total2 -> (__, __ -> 'a1) total2 paths

val display_totalfst : __ paths

val display_weq : ((__, __ -> 'a1) total2, __) weq

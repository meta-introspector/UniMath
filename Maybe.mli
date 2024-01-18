open PartA
open PartB
open PartC
open Preamble

type 'a maybe = ('a, coq_unit) coprod

val just : 'a1 -> 'a1 maybe

val nothing : 'a1 maybe

val just_injectivity : 'a1 -> 'a1 -> 'a1 maybe paths -> 'a1 paths

val isasetmaybe : 'a1 isaset -> 'a1 maybe isaset

val flatmap : ('a1 -> 'a2 maybe) -> 'a1 maybe -> 'a2 maybe

val flatmap_just : ('a1 -> 'a2 maybe) -> 'a1 -> 'a2 maybe paths

val flatmap_nothing : ('a1 -> 'a2 maybe) -> 'a2 maybe paths

val flatmap_ind : 'a3 -> ('a1 -> 'a3) -> 'a1 maybe -> 'a3

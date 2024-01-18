open NaturalNumbers
open PartA
open PartB
open Preamble
open StandardFiniteSets
open Vectors

type 'a list = (nat, 'a vec) total2

val nil : 'a1 list

val cons : 'a1 -> 'a1 list -> 'a1 list

val list_ind : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val list_ind_compute_2 :
  'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 paths

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val length : 'a1 list -> nat

val foldr1 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 list -> 'a1

val foldr1_map : ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 list -> 'a2

val nth : 'a1 list -> stn -> 'a1

val functionToList' : nat -> (stn -> 'a1) -> 'a1 vec

val functionToList : nat -> (stn -> 'a1) -> 'a1 list

val coq_Unnamed_thm : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm0 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm1 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths

val coq_Unnamed_thm3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 list paths

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val mapStep : ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 list paths

val foldr_nil : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a2 paths

val foldr_cons : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 -> 'a1 list -> 'a2 paths

val map_nil : ('a1 -> 'a2) -> 'a2 list paths

val map_cons : ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 list paths

val map_compose : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 list -> 'a3 list paths

val map_idfun : 'a1 list -> 'a1 list paths

val map_homot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a1 list -> 'a2 list
  paths

val foldr1_nil : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 paths

val foldr1_cons_nil : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 paths

val foldr1_cons :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 list -> 'a1 paths

val foldr1_map_nil : ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a2 paths

val foldr1_map_cons_nil :
  ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 -> 'a2 paths

val foldr1_map_cons :
  ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 list -> 'a2
  paths

val foldr1_foldr1_map :
  ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 list -> 'a2 paths

val concatenate : 'a1 list -> 'a1 list -> 'a1 list

val concatenateStep : 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths

val nil_concatenate : 'a1 list -> 'a1 list paths

val concatenate_nil : 'a1 list -> 'a1 list paths

val assoc_concatenate : 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list paths

val map_concatenate : ('a1 -> 'a2) -> 'a1 list -> 'a1 list -> 'a2 list paths

val foldr_concatenate : ('a1 -> 'a2) -> 'a1 list -> 'a2 list paths

val foldr1_concatenate : ('a1 -> 'a2) -> 'a1 list -> 'a2 list paths

val append : 'a1 -> 'a1 list -> 'a1 list

val appendStep : 'a1 -> 'a1 -> 'a1 list -> 'a1 list paths

val append_concatenate : 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths

val map_append : ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 list paths

val reverse : 'a1 list -> 'a1 list

val reverse_nil : 'a1 list paths

val reverseStep : 'a1 -> 'a1 list -> 'a1 list paths

val map_reverse : ('a1 -> 'a2) -> 'a1 list -> 'a2 list paths

val reverse_concatenate : 'a1 list -> 'a1 list -> 'a1 list paths

val reverse_append : 'a1 -> 'a1 list -> 'a1 list paths

val reverse_reverse : 'a1 list -> 'a1 list paths

val flatten : 'a1 list list -> 'a1 list

val flattenStep : 'a1 list -> 'a1 list list -> 'a1 list paths

val isofhlevellist : nat -> 'a1 isofhlevel -> 'a1 list isofhlevel

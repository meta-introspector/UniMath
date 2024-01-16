open PartA
open PartB
open PartD
open Preamble
open Propositions
open UnivalenceAxiom

type __ = Obj.t

val weq1 :
  (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU, hProptoType)
  total2 paths, (coq_UU paths, hProptoType paths) total2) weq

val ident_is_prop :
  (__ -> hProp) -> hProptoType -> hProptoType -> coq_UU paths -> hProptoType
  paths isaprop

val weq2 :
  (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU paths, hProptoType
  paths) total2, coq_UU paths) weq

val coq_Id_p_weq_Id :
  (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU, hProptoType)
  total2 paths, coq_UU paths) weq

val iscontr_weq : 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) weq iscontr

val isofhlevel0pathspace : 'a1 iscontr -> 'a2 iscontr -> coq_UU paths iscontr

val isofhlevelSnpathspace : nat -> 'a2 isofhlevel -> coq_UU paths isofhlevel

val isofhlevelpathspace :
  nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> coq_UU paths isofhlevel

type coq_HLevel = (coq_UU, __ isofhlevel) total2

val isofhlevel_HLevel : nat -> coq_HLevel isofhlevel

val coq_UA_for_Predicates :
  (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU, hProptoType)
  total2 paths, ('a1, 'a2) weq) weq

val coq_UA_for_HLevels :
  nat -> coq_HLevel -> coq_HLevel -> (coq_HLevel paths, (__, __) weq) weq

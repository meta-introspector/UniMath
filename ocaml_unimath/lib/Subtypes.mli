open Notations
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Propositions0
open Sets
open UnivalenceAxiom

val subtype_set : hSet

val subtype_isIn : 'a1 hsubtype -> 'a1 carrier -> 'a1 hsubtype -> hProp

val subtype_containedIn : pr1hSet hrel

val subtype_notContainedIn : 'a1 hsubtype -> 'a1 hsubtype -> hProp

val subtype_inc :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> 'a1 carrier -> 'a1 carrier

val subtype_smallerThan : 'a1 hsubtype -> 'a1 hsubtype -> hProp

val subtype_equal : 'a1 hsubtype -> 'a1 hsubtype -> hProp

val subtype_notEqual : 'a1 hsubtype -> 'a1 hsubtype -> hProp

val subtype_notEqual_containedIn :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType -> hProptoType

val subtype_notEqual_to_negEqual :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType

val subtype_notEqual_from_negEqual :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType -> hProptoType

val emptysubtype : 'a1 hsubtype

val subtype_difference : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype

val subtype_difference_containedIn :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val subtype_equal_cond : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val subtype_union : ('a2 -> 'a1 hsubtype) -> 'a1 hsubtype

val subtype_binaryunion : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype

val subtype_binaryunion_leq1 : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val subtype_binaryunion_leq2 : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val subtype_union_containedIn :
  hSet -> ('a1 -> pr1hSet hsubtype) -> 'a1 -> hProptoType

val subtype_intersection : ('a2 -> 'a1 hsubtype) -> 'a1 hsubtype

val hsubtype_univalence :
  'a1 hsubtype -> 'a1 hsubtype -> ('a1 hsubtype paths, hProptoType) weq

(* val hsubtype_rect : *)
(*   'a1 hsubtype -> 'a1 hsubtype -> ('a1 hsubtype paths -> 'a2, hProptoType -> *)
(*   'a2) weq *)

val subtype_containment_istrans : pr1hSet istrans

val subtype_containment_isrefl : pr1hSet isrefl

val subtype_containment_ispreorder : pr1hSet ispreorder

val subtype_containment_isantisymm : pr1hSet isantisymm

val subtype_containment_isPartialOrder : pr1hSet isPartialOrder

val subtype_inc_comp :
  'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType
  -> 'a1 carrier -> 'a1 carrier paths

val subtype_deceq : 'a1 hsubtype -> 'a1 isdeceq -> 'a1 carrier isdeceq

type 'x isDecidablePredicate = 'x -> hProptoType decidable

val subtype_plus : 'a1 hsubtype -> 'a1 -> 'a1 hsubtype

val subtype_plus_incl : 'a1 hsubtype -> 'a1 -> hProptoType

val subtype_plus_has_point : 'a1 hsubtype -> 'a1 -> hProptoType

val subtype_plus_in :
  'a1 hsubtype -> 'a1 -> 'a1 hsubtype -> hProptoType -> hProptoType ->
  hProptoType

val subtype_complement : 'a1 hsubtype -> 'a1 hsubtype

val not_in_subtype_and_complement :
  'a1 hsubtype -> 'a1 -> hProptoType -> hProptoType -> empty

val subtype_complement_intersection_empty :
  'a1 hsubtype -> ('a2 -> 'a1 hsubtype) -> ('a2, 'a1 hsubtype paths) total2
  -> ('a2, 'a1 hsubtype paths) total2 -> hProptoType

val subtype_complement_union :
  'a1 hsubtype -> hProptoType -> ('a2 -> 'a1 hsubtype) -> ('a2, 'a1 hsubtype
  paths) total2 -> ('a2, 'a1 hsubtype paths) total2 -> hProptoType

val binary_intersection' : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype

val binary_intersection : 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype

val binary_intersection_commutative :
  'a1 hsubtype -> 'a1 hsubtype -> 'a1 -> hProptoType -> hProptoType

val intersection_contained_l : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val intersection_contained_r : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val intersection_contained :
  'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype -> 'a1 hsubtype -> hProptoType
  -> hProptoType -> hProptoType

val isaprop_subtype_containedIn :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType isaprop

val image_hsubtype : 'a1 hsubtype -> ('a1 -> 'a2) -> 'a2 hsubtype

val image_hsubtype_emptyhsubtype : ('a1 -> 'a2) -> 'a2 hsubtype paths

val image_hsubtype_id : 'a1 hsubtype -> 'a1 hsubtype paths

val image_hsubtype_comp :
  'a1 hsubtype -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 hsubtype paths

type ('x, 'y) hsubtype_preserving = hProptoType

val isaprop_hsubtype_preserving :
  'a1 hsubtype -> 'a2 hsubtype -> ('a1 -> 'a2) -> ('a1, 'a2)
  hsubtype_preserving isaprop

val id_hsubtype_preserving : 'a1 hsubtype -> ('a1, 'a1) hsubtype_preserving

val comp_hsubtype_preserving :
  'a1 hsubtype -> 'a2 hsubtype -> 'a3 hsubtype -> ('a1 -> 'a2) -> ('a2 ->
  'a3) -> ('a1, 'a2) hsubtype_preserving -> ('a2, 'a3) hsubtype_preserving ->
  ('a1, 'a3) hsubtype_preserving

val empty_hsubtype_preserving : ('a1 -> 'a2) -> ('a1, 'a2) hsubtype_preserving

val total_hsubtype_preserving : ('a1 -> 'a2) -> ('a1, 'a2) hsubtype_preserving

val singleton : 'a1 -> 'a1 hsubtype

val singleton_point : 'a1 -> 'a1 carrier

val iscontr_singleton : hSet -> pr1hSet -> pr1hSet carrier iscontr

val singleton_is_in : 'a1 hsubtype -> 'a1 carrier -> hProptoType

val coprod_carrier_binary_union :
  'a1 hsubtype -> 'a1 hsubtype -> ('a1 carrier, 'a1 carrier) coprod -> 'a1
  carrier

val issurjective_coprod_carrier_binary_union :
  'a1 hsubtype -> 'a1 hsubtype -> (('a1 carrier, 'a1 carrier) coprod, 'a1
  carrier) issurjective

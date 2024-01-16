open Notations
open PartA
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

val subtype_equal : 'a1 hsubtype -> 'a1 hsubtype -> hProp

val subtype_notEqual : 'a1 hsubtype -> 'a1 hsubtype -> hProp

val subtype_notEqual_containedIn :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType -> hProptoType

val subtype_notEqual_from_negEqual :
  'a1 hsubtype -> 'a1 hsubtype -> hProptoType -> hProptoType -> hProptoType

val subtype_equal_cond : 'a1 hsubtype -> 'a1 hsubtype -> hProptoType

val subtype_union : ('a2 -> 'a1 hsubtype) -> 'a1 hsubtype

val subtype_union_containedIn :
  hSet -> ('a1 -> pr1hSet hsubtype) -> 'a1 -> hProptoType

val hsubtype_univalence :
  'a1 hsubtype -> 'a1 hsubtype -> ('a1 hsubtype paths, hProptoType) weq

val subtype_containment_istrans : pr1hSet istrans

val subtype_containment_isrefl : pr1hSet isrefl

val subtype_containment_ispreorder : pr1hSet ispreorder

val subtype_containment_isantisymm : pr1hSet isantisymm

val subtype_containment_isPartialOrder : pr1hSet isPartialOrder

val subtype_plus : 'a1 hsubtype -> 'a1 -> 'a1 hsubtype

val subtype_plus_incl : 'a1 hsubtype -> 'a1 -> hProptoType

val subtype_plus_has_point : 'a1 hsubtype -> 'a1 -> hProptoType

val subtype_plus_in :
  'a1 hsubtype -> 'a1 -> 'a1 hsubtype -> hProptoType -> hProptoType ->
  hProptoType

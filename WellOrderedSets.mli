open AxiomOfChoice
open Notations
open OrderedSets
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Propositions0
open Sets
open Sets0
open Subtypes
open UnivalenceAxiom

val coq_TotalOrdering : hSet -> hSet

val coq_TOSubset_set : hSet -> hSet

type coq_TOSubset = pr1hSet

val coq_TOSubset_to_subtype : hSet -> coq_TOSubset -> pr1hSet hsubtype

val coq_TOSrel : hSet -> coq_TOSubset -> pr1hSet hrel

val coq_TOtotal : hSet -> coq_TOSubset -> hProptoType

val coq_TOtot : hSet -> coq_TOSubset -> pr1hSet istotal

val coq_TOanti : hSet -> coq_TOSubset -> pr1hSet isantisymm

val coq_TOrefl : hSet -> coq_TOSubset -> pr1hSet isrefl

val coq_TOeq_to_refl : hSet -> coq_TOSubset -> hProptoType

val coq_TOeq_to_refl_1 : hSet -> coq_TOSubset -> hProptoType

val coq_TOtrans : hSet -> coq_TOSubset -> pr1hSet istrans

val h1'' :
  hSet -> coq_TOSubset -> pr1hSet carrier -> pr1hSet carrier -> pr1hSet
  carrier -> pr1hSet carrier -> hProptoType -> pr1hSet paths -> pr1hSet paths
  -> hProptoType

val tosub_order_compat :
  hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType -> hProp

val tosub_le : hSet -> coq_TOSubset -> coq_TOSubset -> hProp

val sub_initial :
  hSet -> pr1hSet hsubtype -> coq_TOSubset -> hProptoType -> hProp

val same_induced_ordering :
  hSet -> coq_TOSubset -> coq_TOSubset -> pr1hSet hsubtype -> hProptoType ->
  hProptoType -> hProp

val common_initial :
  hSet -> pr1hSet hsubtype -> coq_TOSubset -> coq_TOSubset -> hProp

val max_common_initial :
  hSet -> coq_TOSubset -> coq_TOSubset -> pr1hSet hsubtype

val max_common_initial_is_max :
  hSet -> coq_TOSubset -> coq_TOSubset -> pr1hSet hsubtype -> hProptoType ->
  hProptoType

val max_common_initial_is_sub :
  hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType

val max_common_initial_is_common_initial :
  hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType

val tosub_fidelity :
  hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType -> pr1hSet carrier ->
  pr1hSet carrier -> hProptoType

val coq_TOSubset_plus_point_rel :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> pr1hSet hrel

val isTotalOrder_TOSubset_plus_point :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType

val coq_TOSubset_plus_point :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> coq_TOSubset

val coq_TOSubset_plus_point_incl :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType

val coq_TOSubset_plus_point_le :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType

val coq_TOSubset_plus_point_initial :
  hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType

val hasSmallest : 'a1 hrel -> hProp

val isWellOrder : hSet -> pr1hSet hrel -> hProp

val coq_WellOrdering : hSet -> hSet

val coq_WOSubset_set : hSet -> hSet

type coq_WOSubset = pr1hSet

val coq_WOSubset_to_subtype : hSet -> coq_WOSubset -> pr1hSet hsubtype

val coq_WOSrel : hSet -> coq_WOSubset -> pr1hSet hrel

val coq_WOStotal : hSet -> coq_WOSubset -> hProptoType

val coq_WOSubset_to_TOSubset : hSet -> coq_WOSubset -> coq_TOSubset

val coq_WOSwo : hSet -> coq_WOSubset -> pr1hSet

val lt : hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet carrier -> hProp

val coq_WOS_hasSmallest : hSet -> coq_WOSubset -> hProptoType

val wo_lt_to_le :
  hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet carrier -> hProptoType
  -> hProptoType

val wosub_le : hSet -> coq_WOSubset hrel

val wosub_le_inc :
  hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> hProptoType

val wosub_le_comp :
  hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> hProptoType

val wosub_le_subi :
  hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> hProptoType

val wosub_le_isrefl : hSet -> coq_WOSubset isrefl

val wosub_equal : hSet -> coq_WOSubset hrel

val wosub_comparable : hSet -> coq_WOSubset hrel

val hasSmallest_WOSubset_plus_point :
  hSet -> coq_WOSubset -> pr1hSet -> hProptoType -> hProptoType

val coq_WOSubset_plus_point :
  hSet -> coq_WOSubset -> pr1hSet -> hProptoType -> hProptoType ->
  coq_WOSubset

val wosub_univalence_map :
  hSet -> coq_WOSubset -> coq_WOSubset -> coq_WOSubset paths -> hProptoType

val wosub_univalence :
  hSet -> coq_WOSubset -> coq_WOSubset -> (coq_WOSubset paths, hProptoType)
  weq

val wosub_univalence_compute :
  hSet -> coq_WOSubset -> coq_WOSubset -> coq_WOSubset paths -> hProptoType
  paths

val wosub_inc :
  hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> pr1hSet carrier ->
  pr1hSet carrier

val wosub_fidelity :
  hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> pr1hSet carrier ->
  pr1hSet carrier -> hProptoType

val h1 :
  hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet carrier -> pr1hSet
  carrier -> pr1hSet carrier paths -> hProptoType -> hProptoType

val wosub_le_isPartialOrder : hSet -> coq_WOSubset isPartialOrder

val coq_WosubPoset : hSet -> coq_Poset

val wosub_le_smaller : hSet -> coq_WOSubset -> coq_WOSubset -> hProp

val upto : hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet hsubtype

val upto_eqn :
  hSet -> coq_WOSubset -> coq_WOSubset -> pr1hSet -> hProptoType ->
  hProptoType -> hProptoType -> pr1hSet hsubtype paths

val isInterval :
  hSet -> pr1hSet hsubtype -> coq_WOSubset -> hProptoType -> hProptoType ->
  hProptoType -> hProptoType -> hProptoType

val is_wosubset_chain : hSet -> ('a1 -> coq_WOSubset) -> hProp

val common_index :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> 'a1 -> pr1hSet ->
  hProptoType

val common_index2 :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet ->
  hProptoType

val common_index3 :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet ->
  pr1hSet -> hProptoType

val chain_union_prelim_eq0 :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet -> 'a1
  -> 'a1 -> hProptoType -> hProptoType -> hProptoType -> hProptoType -> hProp
  paths

val chain_union_rel :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet hrel

val chain_union_rel_eqn :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet -> 'a1
  -> hProptoType -> hProptoType -> hProp paths

val chain_union_rel_istrans :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet istrans

val chain_union_rel_isrefl :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet isrefl

val chain_union_rel_isantisymm :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet isantisymm

val chain_union_rel_istotal :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet istotal

val chain_union_rel_isTotalOrder :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> hProptoType

val chain_union_TOSubset :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> coq_TOSubset

val chain_union_tosub_le :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> 'a1 -> hProptoType

val chain_union_rel_initial :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> 'a1 -> hProptoType

val chain_union_rel_hasSmallest :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> hProptoType

val chain_union_WOSubset :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> coq_WOSubset

val chain_union_le :
  hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> hProptoType

val proper_subtypes_set : hSet

val upto' : hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet

val choice_fun : hSet -> hSet

val coq_AC_to_choice_fun : hSet -> hProptoType

val is_guided_WOSubset : hSet -> pr1hSet -> coq_WOSubset -> hProp

val upto'_eqn :
  hSet -> pr1hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> pr1hSet
  carrier -> pr1hSet carrier -> pr1hSet paths -> pr1hSet paths

type coq_Guided_WOSubset = (coq_WOSubset, hProptoType) total2

val guidedFamily : hSet -> pr1hSet -> coq_Guided_WOSubset -> coq_WOSubset

val guided_WOSubset_total : hSet -> pr1hSet -> hProptoType -> hProptoType

val coq_ZermeloWellOrdering : hSet -> hProptoType

type coq_WellOrderedSet = (hSet, pr1hSet) total2

val coq_WellOrderedSet_to_hSet : coq_WellOrderedSet -> hSet

val coq_WOrel : coq_WellOrderedSet -> pr1hSet hrel

val coq_WOlt : coq_WellOrderedSet -> pr1hSet -> pr1hSet -> hProp

val isaprop_theSmallest :
  hSet -> pr1hSet hrel -> hProptoType -> pr1hSet hsubtype -> pr1hSet isaprop

val coq_WO_isTotalOrder : coq_WellOrderedSet -> hProptoType

val coq_WO_isrefl : coq_WellOrderedSet -> pr1hSet isrefl

val coq_WO_istrans : coq_WellOrderedSet -> pr1hSet istrans

val coq_WO_istotal : coq_WellOrderedSet -> pr1hSet istotal

val coq_WO_isantisymm : coq_WellOrderedSet -> pr1hSet isantisymm

val coq_WO_hasSmallest : coq_WellOrderedSet -> hProptoType

val coq_WOlt_istrans : coq_WellOrderedSet -> pr1hSet istrans

val coq_WOlt_isirrefl : coq_WellOrderedSet -> pr1hSet isirrefl

val coq_WOlt'_subproof :
  coq_WellOrderedSet -> pr1hSet -> pr1hSet -> (hProptoType, pr1hSet paths
  neg) dirprod isaprop

val coq_WOlt' : coq_WellOrderedSet -> pr1hSet -> pr1hSet -> hProp

val coq_WOlt'_to_WOlt :
  coq_WellOrderedSet -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType

val coq_WOlt_to_WOlt' :
  coq_WellOrderedSet -> pr1hSet isdeceq -> pr1hSet -> pr1hSet -> hProptoType
  -> hProptoType

val coq_WOlt_trich :
  coq_WellOrderedSet -> pr1hSet isdeceq -> pr1hSet -> pr1hSet -> hProptoType

val theSmallest : coq_WellOrderedSet -> pr1hSet hsubtype -> hProp

val coq_WO_theSmallest : coq_WellOrderedSet -> pr1hSet hsubtype -> hProptoType

val coq_WO_theUniqueSmallest :
  coq_WellOrderedSet -> pr1hSet hsubtype -> hProptoType

type iswofun =
  ((pr1hSet, pr1hSet) iscomprelrelfun, pr1hSet -> pr1hSet -> hProptoType ->
  hProptoType) dirprod

val isaprop_iswofun :
  coq_WellOrderedSet -> coq_WellOrderedSet -> (pr1hSet -> pr1hSet) -> iswofun
  isaprop

type wofun = (pr1hSet -> pr1hSet, iswofun) total2

val pr1wofun :
  coq_WellOrderedSet -> coq_WellOrderedSet -> wofun -> pr1hSet -> pr1hSet

val wofun_eq :
  coq_WellOrderedSet -> coq_WellOrderedSet -> wofun -> wofun -> (pr1hSet ->
  pr1hSet) paths -> wofun paths

val iswofun_idfun : coq_WellOrderedSet -> iswofun

val iswofun_funcomp :
  coq_WellOrderedSet -> coq_WellOrderedSet -> coq_WellOrderedSet -> wofun ->
  wofun -> iswofun

val empty_woset_subproof : pr1hSet

val empty_woset : coq_WellOrderedSet

val unit_woset_subproof : pr1hSet -> pr1hSet -> hProptoType isaprop

val unit_woset : coq_WellOrderedSet

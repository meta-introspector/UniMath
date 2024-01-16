open PartA
open PartB
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom
open WellOrderedSets

val contr_to_pr1contr :
  ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2
  paths iscontr -> 'a1 paths iscontr

val pr1contr_to_contr :
  ('a1 -> hProp) -> ('a1, hProptoType) total2 -> 'a1 paths iscontr -> ('a1,
  hProptoType) total2 paths iscontr

val substructure_univalence :
  ('a1 -> 'a1 -> ('a1 paths, 'a2) weq) -> ('a1 -> hProp) -> ('a1,
  hProptoType) total2 -> ('a1, hProptoType) total2 -> (('a1, hProptoType)
  total2 paths, 'a2) weq

type coq_PointedGraph = (hSet, (pr1hSet hrel, pr1hSet) total2) total2

type isaroot = pr1hSet -> hProptoType

val isaprop_isaroot : hSet -> pr1hSet hrel -> pr1hSet -> isaroot isaprop

type isTRR = (pr1hSet isrefl, (pr1hSet istrans, isaroot) dirprod) dirprod

val isaprop_isTRR : hSet -> pr1hSet hrel -> pr1hSet -> isTRR isaprop

type coq_TRRGraphData = (pr1hSet hrel, (pr1hSet, isTRR) total2) total2

val isaset_TRRGraphData : hSet -> coq_TRRGraphData isaset

type coq_TRRGraph = (hSet, coq_TRRGraphData) total2

val coq_TRRG_edgerel : coq_TRRGraph -> pr1hSet hrel

val coq_TRRG_root : coq_TRRGraph -> pr1hSet

val coq_TRRG_transitivity : coq_TRRGraph -> pr1hSet istrans

val selfedge : coq_TRRGraph -> pr1hSet -> hProptoType

type isTRRGhomo =
  (pr1hSet -> pr1hSet -> (hProptoType, hProptoType) logeq, pr1hSet paths)
  dirprod

val isaprop_isTRRGhomo :
  coq_TRRGraph -> coq_TRRGraph -> (pr1hSet -> pr1hSet) -> isTRRGhomo isaprop

val coq_TRRGhomo_frompath :
  hSet -> hSet -> coq_TRRGraphData -> coq_TRRGraphData -> hSet paths ->
  coq_TRRGraphData paths -> isTRRGhomo

val helper :
  hSet -> (pr1hSet -> pr1hSet -> hProp) -> (pr1hSet -> pr1hSet -> hProp) ->
  pr1hSet -> pr1hSet -> isTRR -> isTRR -> (pr1hSet -> pr1hSet -> hProp) paths
  -> pr1hSet paths -> (pr1hSet, isTRR) total2 paths

val coq_TRRGhomo_topath :
  hSet -> hSet -> coq_TRRGraphData -> coq_TRRGraphData -> hSet paths ->
  isTRRGhomo -> coq_TRRGraphData paths

type coq_TRRGraphiso = ((pr1hSet, pr1hSet) weq, isTRRGhomo) total2

val id_TRRGraphiso : coq_TRRGraph -> coq_TRRGraphiso

val coq_TRRGraph_univalence_map :
  coq_TRRGraph -> coq_TRRGraph -> coq_TRRGraph paths -> coq_TRRGraphiso

val coq_TRRGraph_univalence_weq1 :
  coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths, (hSet,
  coq_TRRGraphData) coq_PathPair) weq

val coq_TRRGraph_univalence_weq2 :
  coq_TRRGraph -> coq_TRRGraph -> ((hSet, coq_TRRGraphData) coq_PathPair,
  coq_TRRGraphiso) weq

val coq_TRRGraph_univalence_weq2_idpath :
  coq_TRRGraph -> coq_TRRGraphiso paths

val coq_TRRGraph_univalence_weq1_idpath :
  coq_TRRGraph -> (hSet, coq_TRRGraphData) coq_PathPair paths

val isweq_TRRGraph_univalence_map :
  coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths, coq_TRRGraphiso) isweq

val coq_TRRGraph_univalence :
  coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths, coq_TRRGraphiso) weq

val coq_TRRGraph_univalence_compute :
  coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths -> coq_TRRGraphiso)
  paths

type coq_DownwardClosure = (pr1hSet, hProptoType) total2

type antisymmetric = (hProptoType, hProptoType) dirprod -> pr1hSet paths

val total : coq_TRRGraph -> pr1hSet -> pr1hSet -> hProp

type isatree =
  pr1hSet -> coq_DownwardClosure -> coq_DownwardClosure -> (antisymmetric,
  hProptoType) dirprod

val isaprop_isatree : coq_TRRGraph -> isatree isaprop

type coq_Tree = (coq_TRRGraph, isatree) total2

type coq_Tree_iso = coq_TRRGraphiso

val coq_Tree_univalence :
  coq_Tree -> coq_Tree -> (coq_Tree paths, coq_Tree_iso) weq

type coq_Upw_underlying = (pr1hSet, hProptoType) total2

val isaset_Upw_underlying : coq_Tree -> pr1hSet -> coq_Upw_underlying isaset

val coq_Upw : coq_Tree -> pr1hSet -> hSet

val coq_Upw_E : coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> hProp

val coq_Upw_to_PointedGraph : coq_Tree -> pr1hSet -> coq_PointedGraph

val coq_Upw_reflexive : coq_Tree -> pr1hSet -> pr1hSet -> hProptoType

val coq_Upw_transitive :
  coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet -> hProptoType ->
  hProptoType -> hProptoType

val coq_Upw_rooted : coq_Tree -> pr1hSet -> pr1hSet -> hProptoType

val coq_Upw_to_TRRGraph : coq_Tree -> pr1hSet -> coq_TRRGraph

val isatree_Upw : coq_Tree -> pr1hSet -> isatree

val coq_Up : coq_Tree -> pr1hSet -> coq_Tree

type isrigid = coq_Tree paths iscontr

val isaprop_isrigid : coq_Tree -> isrigid isaprop

type issuperrigid = (isrigid, pr1hSet -> isrigid) dirprod

val isaprop_issuperrigid : coq_Tree -> issuperrigid isaprop

val isWellFoundedUp : coq_Tree -> hProp

val hasLargest : 'a1 hrel -> hProp

val isWellFoundedDown : coq_Tree -> hProp

type coq_Tree_isWellFounded = (hProptoType, hProptoType) dirprod

val isaprop_Tree_isWellFounded : coq_Tree -> coq_Tree_isWellFounded isaprop

type ispreZFS = (coq_Tree_isWellFounded, issuperrigid) dirprod

val isaprop_ispreZFS : coq_Tree -> ispreZFS isaprop

type preZFS = (coq_Tree, ispreZFS) total2

val coq_Ve : preZFS -> hSet

val coq_Ed : preZFS -> pr1hSet -> pr1hSet -> hProp

val root : preZFS -> pr1hSet

val preZFS_isrigid : preZFS -> preZFS paths iscontr

val isaset_preZFS : preZFS isaset

type preZFS_iso = coq_Tree_iso

val preZFS_univalence : preZFS -> preZFS -> (preZFS paths, preZFS_iso) weq

val preZFS_Branch : preZFS -> pr1hSet -> coq_Tree

val preZFS_Branch_hsubtype_tohsubtype :
  preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet hsubtype

val hsubtype_to_preZFS_Branch_hsubtype :
  preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet hsubtype

val coq_Branch_to_subtype :
  preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet hsubtype paths

val fromBranch_hsubtype :
  preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet -> hProptoType ->
  hProptoType

val toBranch_hsubtype :
  preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet -> hProptoType ->
  hProptoType -> hProptoType

val preZFS_Branch_isWellFounded : preZFS -> pr1hSet -> coq_Tree_isWellFounded

val iscontrauto_Tree_TRRGraph :
  coq_Tree -> isrigid -> coq_TRRGraph paths iscontr

val coq_Up_to_Up : coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet

val coq_Up_to_Up_inv : coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet

val isweq_Up_to_Up :
  coq_Tree -> pr1hSet -> pr1hSet -> (pr1hSet, pr1hSet) isweq

val isTRRGhomo_Up_to_Up : coq_Tree -> pr1hSet -> pr1hSet -> isTRRGhomo

val coq_UpUpid : coq_Tree -> pr1hSet -> pr1hSet -> coq_TRRGraph paths

val preZFS_Branch_issuperrigid : preZFS -> pr1hSet -> issuperrigid

val coq_Branch : preZFS -> pr1hSet -> preZFS

type hasuniquerepbranch = pr1hSet -> pr1hSet -> preZFS paths -> pr1hSet paths

val isaprop_hasuniquerepbranch : preZFS -> hasuniquerepbranch isaprop

type coq_ZFS = (preZFS, hasuniquerepbranch) total2

val pr1ZFS : coq_ZFS -> preZFS

type coq_ZFS_iso = preZFS_iso

val coq_ZFS_univalence :
  coq_ZFS -> coq_ZFS -> (coq_ZFS paths, coq_ZFS_iso) weq

val isaset_ZFS : coq_ZFS isaset

val coq_Branch_of_Branch_to_Branch :
  preZFS -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet

val coq_Branch_of_Branch_to_Branch_inv :
  preZFS -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet

val isweq_Branch_of_Branch_to_Branch :
  preZFS -> pr1hSet -> pr1hSet -> (pr1hSet, pr1hSet) isweq

val isTRRGhomo_Branch_of_Branch_to_Branch :
  preZFS -> pr1hSet -> pr1hSet -> isTRRGhomo

val coq_Branch_of_Branch_eq_Branch :
  preZFS -> pr1hSet -> pr1hSet -> preZFS paths

val coq_ZFS_Branch_is_ZFS : coq_ZFS -> pr1hSet -> hasuniquerepbranch

val coq_ZFS_Branch : coq_ZFS -> pr1hSet -> coq_ZFS

val coq_Root : coq_ZFS -> pr1hSet

val isapoint : coq_ZFS -> pr1hSet -> hProp

val isaprop_isapoint : coq_ZFS -> pr1hSet -> hProptoType isaprop

type coq_ZFS_elementof =
  (pr1hSet, (hProptoType, coq_ZFS paths) dirprod) total2

val isaprop_ZFS_elementof : coq_ZFS -> coq_ZFS -> coq_ZFS_elementof isaprop

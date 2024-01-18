open BasicAst
open BinInt
open Classes
open Datatypes
open EqDecInstances
open FloatOps
open Kernames
open MCPrelude
open PrimFloat
open PrimInt63
open ReflectEq
open SpecFloat
open Specif
open Universes

type __ = Obj.t

val reflect_prim_int : int coq_ReflectEq

val coq_NoConfusionPackage_spec_float : spec_float coq_NoConfusionPackage

val spec_float_eqdec : spec_float -> spec_float -> spec_float dec_eq

val spec_float_EqDec : spec_float coq_EqDec

val reflect_prim_float : float coq_ReflectEq

val eq_prop_level : PropLevel.t -> PropLevel.t -> bool

val reflect_prop_level : PropLevel.t coq_ReflectEq

val eq_levels :
  (PropLevel.t, Level.t) sum -> (PropLevel.t, Level.t) sum -> bool

val reflect_levels : (PropLevel.t, Level.t) sum coq_ReflectEq

val eq_name : name -> name -> bool

val reflect_name : name coq_ReflectEq

val eq_relevance : relevance -> relevance -> bool

val reflect_relevance : relevance coq_ReflectEq

val eq_aname : name binder_annot -> name binder_annot -> bool

val reflect_aname : aname coq_ReflectEq

val eq_def : 'a1 coq_ReflectEq -> 'a1 def -> 'a1 def -> bool

val reflect_def : 'a1 coq_ReflectEq -> 'a1 def coq_ReflectEq

val eq_cast_kind : cast_kind -> cast_kind -> bool

val reflect_cast_kind : cast_kind coq_ReflectEq

val eqb_case_info : case_info -> case_info -> bool

val reflect_case_info : case_info coq_ReflectEq

val coq_NoConfusionPackage_sig : 'a1 coq_NoConfusionPackage

val coq_NoConfusionHomPackage_sig : 'a1 coq_NoConfusionPackage

val coq_NoConfusionPackage_prod : ('a1, 'a2) prod coq_NoConfusionPackage

val coq_NoConfusionHomPackage_prod : ('a1, 'a2) prod coq_NoConfusionPackage

val eqb_context_decl :
  ('a1 -> 'a1 -> bool) -> 'a1 context_decl -> 'a1 context_decl -> bool

val eq_decl_reflect : 'a1 coq_ReflectEq -> 'a1 context_decl coq_ReflectEq

val eqb_recursivity_kind : recursivity_kind -> recursivity_kind -> bool

val reflect_recursivity_kind : recursivity_kind coq_ReflectEq

val eqb_ConstraintType : ConstraintType.t_ -> ConstraintType.t_ -> bool

val reflect_ConstraintType : ConstraintType.t coq_ReflectEq

val coq_Z_as_int : Int.Z_as_Int.t coq_ReflectEq

val lt__sig_pack :
  UnivConstraint.t -> UnivConstraint.t ->
  (UnivConstraint.t * UnivConstraint.t) * __

val lt__Signature :
  UnivConstraint.t -> UnivConstraint.t ->
  (UnivConstraint.t * UnivConstraint.t) * __

val le_sig_pack : nat -> nat -> nat * __

val le_Signature : nat -> nat -> nat * __

val coq_NoConfusionPackage_comparison : comparison coq_NoConfusionPackage

val comparison_eqdec : comparison -> comparison -> comparison dec_eq

val comparison_EqDec : comparison coq_EqDec

module LevelSetsUIP :
 sig
  val levels_tree_eqb : LevelSet.Raw.t -> LevelSet.Raw.t -> bool

  val levels_tree_rect :
    'a1 -> (Int.Z_as_Int.t -> LevelSet.Raw.tree -> 'a1 -> Level.t_ ->
    LevelSet.Raw.tree -> 'a1 -> 'a1) -> LevelSet.Raw.tree -> 'a1

  val levels_tree_reflect : LevelSet.Raw.t coq_ReflectEq

  val coq_NoConfusionPackage_tree : LevelSet.Raw.tree coq_NoConfusionPackage

  val bst_sig_pack : LevelSet.Raw.tree -> LevelSet.Raw.tree * __

  val bst_Signature : LevelSet.Raw.tree -> LevelSet.Raw.tree * __

  val eqb_LevelSet : LevelSet.t_ -> LevelSet.t_ -> bool

  val reflect_LevelSet : LevelSet.t coq_ReflectEq
 end

module ConstraintSetsUIP :
 sig
  val cs_tree_eqb : ConstraintSet.Raw.t -> ConstraintSet.Raw.t -> bool

  val cs_tree_rect :
    'a1 -> (Int.Z_as_Int.t -> ConstraintSet.Raw.tree -> 'a1 -> ((Level.t,
    ConstraintType.t) prod, Level.t) prod -> ConstraintSet.Raw.tree -> 'a1 ->
    'a1) -> ConstraintSet.Raw.tree -> 'a1

  val cs_tree_reflect : ConstraintSet.Raw.t coq_ReflectEq

  val eqb_ConstraintSet : ConstraintSet.t_ -> ConstraintSet.t_ -> bool

  val coq_NoConfusionPackage_tree :
    ConstraintSet.Raw.tree coq_NoConfusionPackage

  val bst_sig_pack : ConstraintSet.Raw.tree -> ConstraintSet.Raw.tree * __

  val bst_Signature : ConstraintSet.Raw.tree -> ConstraintSet.Raw.tree * __

  val reflect_ConstraintSet : ConstraintSet.t coq_ReflectEq
 end

val eqb_universes_decl : universes_decl -> universes_decl -> bool

val reflect_universes_decl : universes_decl coq_ReflectEq

val eqb_allowed_eliminations :
  allowed_eliminations -> allowed_eliminations -> bool

val reflect_allowed_eliminations : allowed_eliminations coq_ReflectEq

val eqb_Variance : Variance.t -> Variance.t -> bool

val reflect_Variance : Variance.t coq_ReflectEq

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
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val reflect_prim_int : int coq_ReflectEq **)

let reflect_prim_int =
  PrimInt63.eqb

(** val coq_NoConfusionPackage_spec_float :
    spec_float coq_NoConfusionPackage **)

let coq_NoConfusionPackage_spec_float =
  Build_NoConfusionPackage

(** val spec_float_eqdec : spec_float -> spec_float -> spec_float dec_eq **)

let spec_float_eqdec x y =
  match x with
  | S754_zero s ->
    (match y with
     | S754_zero s0 -> eq_dec_point s (coq_EqDec_EqDecPoint bool_EqDec s) s0
     | _ -> Coq_right)
  | S754_infinity s ->
    (match y with
     | S754_infinity s0 ->
       eq_dec_point s (coq_EqDec_EqDecPoint bool_EqDec s) s0
     | _ -> Coq_right)
  | S754_nan -> (match y with
                 | S754_nan -> Coq_left
                 | _ -> Coq_right)
  | S754_finite (s, m, e) ->
    (match y with
     | S754_finite (s0, m0, e0) ->
       (match eq_dec_point s (coq_EqDec_EqDecPoint bool_EqDec s) s0 with
        | Coq_left ->
          (match eq_dec_point m (coq_EqDec_EqDecPoint positive_EqDec m) m0 with
           | Coq_left ->
             eq_dec_point e (coq_EqDec_EqDecPoint coq_Z_EqDec e) e0
           | Coq_right -> Coq_right)
        | Coq_right -> Coq_right)
     | _ -> Coq_right)

(** val spec_float_EqDec : spec_float coq_EqDec **)

let spec_float_EqDec =
  spec_float_eqdec

(** val reflect_prim_float : float coq_ReflectEq **)

let reflect_prim_float x y =
  eqb (coq_EqDec_ReflectEq spec_float_EqDec) (coq_Prim2SF x) (coq_Prim2SF y)

(** val eq_prop_level : PropLevel.t -> PropLevel.t -> bool **)

let eq_prop_level l1 l2 =
  match l1 with
  | PropLevel.Coq_lSProp ->
    (match l2 with
     | PropLevel.Coq_lSProp -> Coq_true
     | PropLevel.Coq_lProp -> Coq_false)
  | PropLevel.Coq_lProp ->
    (match l2 with
     | PropLevel.Coq_lSProp -> Coq_false
     | PropLevel.Coq_lProp -> Coq_true)

(** val reflect_prop_level : PropLevel.t coq_ReflectEq **)

let reflect_prop_level =
  eq_prop_level

(** val eq_levels :
    (PropLevel.t, Level.t) sum -> (PropLevel.t, Level.t) sum -> bool **)

let eq_levels l1 l2 =
  match l1 with
  | Coq_inl l ->
    (match l2 with
     | Coq_inl l' -> eqb reflect_prop_level l l'
     | Coq_inr _ -> Coq_false)
  | Coq_inr l ->
    (match l2 with
     | Coq_inl _ -> Coq_false
     | Coq_inr l' -> eqb Level.reflect_level l l')

(** val reflect_levels : (PropLevel.t, Level.t) sum coq_ReflectEq **)

let reflect_levels =
  eq_levels

(** val eq_name : name -> name -> bool **)

let eq_name na nb =
  match na with
  | Coq_nAnon ->
    (match nb with
     | Coq_nAnon -> Coq_true
     | Coq_nNamed _ -> Coq_false)
  | Coq_nNamed a ->
    (match nb with
     | Coq_nAnon -> Coq_false
     | Coq_nNamed b -> eqb IdentOT.reflect_eq_string a b)

(** val reflect_name : name coq_ReflectEq **)

let reflect_name =
  eq_name

(** val eq_relevance : relevance -> relevance -> bool **)

let eq_relevance r r' =
  match r with
  | Relevant -> (match r' with
                 | Relevant -> Coq_true
                 | Irrelevant -> Coq_false)
  | Irrelevant ->
    (match r' with
     | Relevant -> Coq_false
     | Irrelevant -> Coq_true)

(** val reflect_relevance : relevance coq_ReflectEq **)

let reflect_relevance =
  eq_relevance

(** val eq_aname : name binder_annot -> name binder_annot -> bool **)

let eq_aname na nb =
  match eqb reflect_name na.binder_name nb.binder_name with
  | Coq_true -> eqb reflect_relevance na.binder_relevance nb.binder_relevance
  | Coq_false -> Coq_false

(** val reflect_aname : aname coq_ReflectEq **)

let reflect_aname =
  eq_aname

(** val eq_def : 'a1 coq_ReflectEq -> 'a1 def -> 'a1 def -> bool **)

let eq_def h d1 d2 =
  let { dname = n1; dtype = t1; dbody = b1; rarg = a1 } = d1 in
  let { dname = n2; dtype = t2; dbody = b2; rarg = a2 } = d2 in
  (match match match eqb reflect_aname n1 n2 with
               | Coq_true -> eqb h t1 t2
               | Coq_false -> Coq_false with
         | Coq_true -> eqb h b1 b2
         | Coq_false -> Coq_false with
   | Coq_true -> eqb reflect_nat a1 a2
   | Coq_false -> Coq_false)

(** val reflect_def : 'a1 coq_ReflectEq -> 'a1 def coq_ReflectEq **)

let reflect_def =
  eq_def

(** val eq_cast_kind : cast_kind -> cast_kind -> bool **)

let eq_cast_kind c c' =
  match c with
  | VmCast -> (match c' with
               | VmCast -> Coq_true
               | _ -> Coq_false)
  | NativeCast -> (match c' with
                   | NativeCast -> Coq_true
                   | _ -> Coq_false)
  | Cast -> (match c' with
             | Cast -> Coq_true
             | _ -> Coq_false)

(** val reflect_cast_kind : cast_kind coq_ReflectEq **)

let reflect_cast_kind =
  eq_cast_kind

(** val eqb_case_info : case_info -> case_info -> bool **)

let eqb_case_info ci ci' =
  let { ci_ind = ci_ind0; ci_npar = ci_npar0; ci_relevance =
    ci_relevance0 } = ci
  in
  let { ci_ind = ci_ind'; ci_npar = ci_npar'; ci_relevance =
    ci_relevance' } = ci'
  in
  (match match eqb reflect_eq_inductive ci_ind0 ci_ind' with
         | Coq_true -> eqb reflect_nat ci_npar0 ci_npar'
         | Coq_false -> Coq_false with
   | Coq_true -> eqb reflect_relevance ci_relevance0 ci_relevance'
   | Coq_false -> Coq_false)

(** val reflect_case_info : case_info coq_ReflectEq **)

let reflect_case_info =
  eqb_case_info

(** val coq_NoConfusionPackage_sig : 'a1 coq_NoConfusionPackage **)

let coq_NoConfusionPackage_sig =
  Build_NoConfusionPackage

(** val coq_NoConfusionHomPackage_sig : 'a1 coq_NoConfusionPackage **)

let coq_NoConfusionHomPackage_sig =
  Build_NoConfusionPackage

(** val coq_NoConfusionPackage_prod :
    ('a1, 'a2) prod coq_NoConfusionPackage **)

let coq_NoConfusionPackage_prod =
  Build_NoConfusionPackage

(** val coq_NoConfusionHomPackage_prod :
    ('a1, 'a2) prod coq_NoConfusionPackage **)

let coq_NoConfusionHomPackage_prod =
  Build_NoConfusionPackage

(** val eqb_context_decl :
    ('a1 -> 'a1 -> bool) -> 'a1 context_decl -> 'a1 context_decl -> bool **)

let eqb_context_decl eqterm x y =
  let { decl_name = na; decl_body = b; decl_type = ty } = x in
  let { decl_name = na'; decl_body = b'; decl_type = ty' } = y in
  (match match eqb reflect_aname na na' with
         | Coq_true -> eq_option eqterm b b'
         | Coq_false -> Coq_false with
   | Coq_true -> eqterm ty ty'
   | Coq_false -> Coq_false)

(** val eq_decl_reflect :
    'a1 coq_ReflectEq -> 'a1 context_decl coq_ReflectEq **)

let eq_decl_reflect ht =
  eqb_context_decl (eqb ht)

(** val eqb_recursivity_kind :
    recursivity_kind -> recursivity_kind -> bool **)

let eqb_recursivity_kind r r' =
  match r with
  | Finite -> (match r' with
               | Finite -> Coq_true
               | _ -> Coq_false)
  | CoFinite -> (match r' with
                 | CoFinite -> Coq_true
                 | _ -> Coq_false)
  | BiFinite -> (match r' with
                 | BiFinite -> Coq_true
                 | _ -> Coq_false)

(** val reflect_recursivity_kind : recursivity_kind coq_ReflectEq **)

let reflect_recursivity_kind =
  eqb_recursivity_kind

(** val eqb_ConstraintType :
    ConstraintType.t_ -> ConstraintType.t_ -> bool **)

let eqb_ConstraintType x y =
  match x with
  | ConstraintType.Le n ->
    (match y with
     | ConstraintType.Le m -> BinInt.Z.eqb n m
     | ConstraintType.Eq -> Coq_false)
  | ConstraintType.Eq ->
    (match y with
     | ConstraintType.Le _ -> Coq_false
     | ConstraintType.Eq -> Coq_true)

(** val reflect_ConstraintType : ConstraintType.t coq_ReflectEq **)

let reflect_ConstraintType =
  eqb_ConstraintType

(** val coq_Z_as_int : Int.Z_as_Int.t coq_ReflectEq **)

let coq_Z_as_int =
  BinInt.Z.eqb

(** val lt__sig_pack :
    UnivConstraint.t -> UnivConstraint.t ->
    (UnivConstraint.t * UnivConstraint.t) * __ **)

let lt__sig_pack x x0 =
  (x,x0),__

(** val lt__Signature :
    UnivConstraint.t -> UnivConstraint.t ->
    (UnivConstraint.t * UnivConstraint.t) * __ **)

let lt__Signature x x0 =
  (x,x0),__

(** val le_sig_pack : nat -> nat -> nat * __ **)

let le_sig_pack _ x =
  x,__

(** val le_Signature : nat -> nat -> nat * __ **)

let le_Signature _ x =
  x,__

(** val coq_NoConfusionPackage_comparison :
    comparison coq_NoConfusionPackage **)

let coq_NoConfusionPackage_comparison =
  Build_NoConfusionPackage

(** val comparison_eqdec : comparison -> comparison -> comparison dec_eq **)

let comparison_eqdec x y =
  match x with
  | Eq -> (match y with
           | Eq -> Coq_left
           | _ -> Coq_right)
  | Lt -> (match y with
           | Lt -> Coq_left
           | _ -> Coq_right)
  | Gt -> (match y with
           | Gt -> Coq_left
           | _ -> Coq_right)

(** val comparison_EqDec : comparison coq_EqDec **)

let comparison_EqDec =
  comparison_eqdec

module LevelSetsUIP =
 struct
  (** val levels_tree_eqb : LevelSet.Raw.t -> LevelSet.Raw.t -> bool **)

  let rec levels_tree_eqb x y =
    match x with
    | LevelSet.Raw.Leaf ->
      (match y with
       | LevelSet.Raw.Leaf -> Coq_true
       | LevelSet.Raw.Node (_, _, _, _) -> Coq_false)
    | LevelSet.Raw.Node (h, l, o, r) ->
      (match y with
       | LevelSet.Raw.Leaf -> Coq_false
       | LevelSet.Raw.Node (h', l', o', r') ->
         (match match match eqb coq_Z_as_int h h' with
                      | Coq_true -> levels_tree_eqb l l'
                      | Coq_false -> Coq_false with
                | Coq_true -> eqb Level.reflect_level o o'
                | Coq_false -> Coq_false with
          | Coq_true -> levels_tree_eqb r r'
          | Coq_false -> Coq_false))

  (** val levels_tree_rect :
      'a1 -> (Int.Z_as_Int.t -> LevelSet.Raw.tree -> 'a1 -> Level.t_ ->
      LevelSet.Raw.tree -> 'a1 -> 'a1) -> LevelSet.Raw.tree -> 'a1 **)

  let rec levels_tree_rect f f0 = function
  | LevelSet.Raw.Leaf -> f
  | LevelSet.Raw.Node (t1, t2, t3, t4) ->
    f0 t1 t2 (levels_tree_rect f f0 t2) t3 t4 (levels_tree_rect f f0 t4)

  (** val levels_tree_reflect : LevelSet.Raw.t coq_ReflectEq **)

  let levels_tree_reflect =
    levels_tree_eqb

  (** val coq_NoConfusionPackage_tree :
      LevelSet.Raw.tree coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_tree =
    Build_NoConfusionPackage

  (** val bst_sig_pack : LevelSet.Raw.tree -> LevelSet.Raw.tree * __ **)

  let bst_sig_pack x =
    x,__

  (** val bst_Signature : LevelSet.Raw.tree -> LevelSet.Raw.tree * __ **)

  let bst_Signature x =
    x,__

  (** val eqb_LevelSet : LevelSet.t_ -> LevelSet.t_ -> bool **)

  let eqb_LevelSet x y =
    eqb levels_tree_reflect (LevelSet.this x) (LevelSet.this y)

  (** val reflect_LevelSet : LevelSet.t coq_ReflectEq **)

  let reflect_LevelSet =
    eqb_LevelSet
 end

module ConstraintSetsUIP =
 struct
  (** val cs_tree_eqb : ConstraintSet.Raw.t -> ConstraintSet.Raw.t -> bool **)

  let rec cs_tree_eqb x y =
    match x with
    | ConstraintSet.Raw.Leaf ->
      (match y with
       | ConstraintSet.Raw.Leaf -> Coq_true
       | ConstraintSet.Raw.Node (_, _, _, _) -> Coq_false)
    | ConstraintSet.Raw.Node (h, l, o, r) ->
      (match y with
       | ConstraintSet.Raw.Leaf -> Coq_false
       | ConstraintSet.Raw.Node (h', l', o', r') ->
         (match match match eqb coq_Z_as_int h h' with
                      | Coq_true -> cs_tree_eqb l l'
                      | Coq_false -> Coq_false with
                | Coq_true ->
                  eqb
                    (reflect_prod
                      (reflect_prod Level.reflect_level
                        reflect_ConstraintType) Level.reflect_level) o o'
                | Coq_false -> Coq_false with
          | Coq_true -> cs_tree_eqb r r'
          | Coq_false -> Coq_false))

  (** val cs_tree_rect :
      'a1 -> (Int.Z_as_Int.t -> ConstraintSet.Raw.tree -> 'a1 -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> ConstraintSet.Raw.tree -> 'a1
      -> 'a1) -> ConstraintSet.Raw.tree -> 'a1 **)

  let rec cs_tree_rect f f0 = function
  | ConstraintSet.Raw.Leaf -> f
  | ConstraintSet.Raw.Node (t1, t2, p, t3) ->
    f0 t1 t2 (cs_tree_rect f f0 t2) p t3 (cs_tree_rect f f0 t3)

  (** val cs_tree_reflect : ConstraintSet.Raw.t coq_ReflectEq **)

  let cs_tree_reflect =
    cs_tree_eqb

  (** val eqb_ConstraintSet : ConstraintSet.t_ -> ConstraintSet.t_ -> bool **)

  let eqb_ConstraintSet x y =
    eqb cs_tree_reflect (ConstraintSet.this x) (ConstraintSet.this y)

  (** val coq_NoConfusionPackage_tree :
      ConstraintSet.Raw.tree coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_tree =
    Build_NoConfusionPackage

  (** val bst_sig_pack :
      ConstraintSet.Raw.tree -> ConstraintSet.Raw.tree * __ **)

  let bst_sig_pack x =
    x,__

  (** val bst_Signature :
      ConstraintSet.Raw.tree -> ConstraintSet.Raw.tree * __ **)

  let bst_Signature x =
    x,__

  (** val reflect_ConstraintSet : ConstraintSet.t coq_ReflectEq **)

  let reflect_ConstraintSet =
    eqb_ConstraintSet
 end

(** val eqb_universes_decl : universes_decl -> universes_decl -> bool **)

let eqb_universes_decl x y =
  match x with
  | Monomorphic_ctx ->
    (match y with
     | Monomorphic_ctx -> Coq_true
     | Polymorphic_ctx _ -> Coq_false)
  | Polymorphic_ctx cx ->
    (match y with
     | Monomorphic_ctx -> Coq_false
     | Polymorphic_ctx cy ->
       eqb
         (reflect_prod (reflect_list reflect_name)
           ConstraintSetsUIP.reflect_ConstraintSet) cx cy)

(** val reflect_universes_decl : universes_decl coq_ReflectEq **)

let reflect_universes_decl =
  eqb_universes_decl

(** val eqb_allowed_eliminations :
    allowed_eliminations -> allowed_eliminations -> bool **)

let eqb_allowed_eliminations x y =
  match x with
  | IntoSProp -> (match y with
                  | IntoSProp -> Coq_true
                  | _ -> Coq_false)
  | IntoPropSProp -> (match y with
                      | IntoPropSProp -> Coq_true
                      | _ -> Coq_false)
  | IntoSetPropSProp ->
    (match y with
     | IntoSetPropSProp -> Coq_true
     | _ -> Coq_false)
  | IntoAny -> (match y with
                | IntoAny -> Coq_true
                | _ -> Coq_false)

(** val reflect_allowed_eliminations : allowed_eliminations coq_ReflectEq **)

let reflect_allowed_eliminations =
  eqb_allowed_eliminations

(** val eqb_Variance : Variance.t -> Variance.t -> bool **)

let eqb_Variance x y =
  match x with
  | Variance.Irrelevant ->
    (match y with
     | Variance.Irrelevant -> Coq_true
     | _ -> Coq_false)
  | Variance.Covariant ->
    (match y with
     | Variance.Covariant -> Coq_true
     | _ -> Coq_false)
  | Variance.Invariant ->
    (match y with
     | Variance.Invariant -> Coq_true
     | _ -> Coq_false)

(** val reflect_Variance : Variance.t coq_ReflectEq **)

let reflect_Variance =
  eqb_Variance

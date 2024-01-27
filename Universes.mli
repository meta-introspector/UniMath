open All_Forall
open BasicAst
open BinInt
open BinNums
open BinPos
open Bool
open Byte
open Classes
open Datatypes
open EqDecInstances
open FMapAVL
open FMapFacts
open Kernames
open List
open MCList
open MCPrelude
open MCString
open MSetAVL
open MSetFacts
open MSetList
open MSetProperties
open Nat
open OrdersAlt
open ReflectEq
open Specif
open Bytestring
open Config

type __ = Obj.t

type valuation = { valuation_mono : (String.t -> positive);
                   valuation_poly : (nat -> nat) }

val valuation_mono : valuation -> String.t -> positive

val valuation_poly : valuation -> nat -> nat

type 'a coq_Evaluable = valuation -> 'a -> nat

val coq_val : 'a1 coq_Evaluable -> valuation -> 'a1 -> nat

module Level :
 sig
  type t_ =
  | Coq_lzero
  | Coq_level of String.t
  | Coq_lvar of nat

  val t__rect : 'a1 -> (String.t -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1

  val t__rec : 'a1 -> (String.t -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1

  val coq_NoConfusionPackage_t_ : t_ coq_NoConfusionPackage

  type t = t_

  val is_set : t -> bool

  val is_var : t -> bool

  val coq_Evaluable : t coq_Evaluable

  val compare : t -> t -> comparison

  val lt__sig_pack : t -> t -> (t * t) * __

  val lt__Signature : t -> t -> (t * t) * __

  val eq_level : t_ -> t_ -> bool

  val reflect_level : t coq_ReflectEq

  val eqb : t_ -> t_ -> bool

  val eqb_spec : t -> t -> reflect

  val eq_dec : t -> t -> sumbool
 end

module LevelSet :
 sig
  module Raw :
   sig
    type elt = Level.t_

    type tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree * Level.t_ * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : Level.t_ -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : Level.t_ list -> tree -> Level.t_ list

    val elements : tree -> Level.t_ list

    val rev_elements_aux : Level.t_ list -> tree -> Level.t_ list

    val rev_elements : tree -> Level.t_ list

    val cardinal : tree -> nat

    val maxdepth : tree -> nat

    val mindepth : tree -> nat

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      Level.t_ -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> Level.t_ -> tree -> bool

    val subsetr : (tree -> bool) -> Level.t_ -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : Level.t_ -> tree

    val create : t -> Level.t_ -> t -> tree

    val assert_false : t -> Level.t_ -> t -> tree

    val bal : t -> Level.t_ -> t -> tree

    val add : Level.t_ -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> (t, elt) prod

    val merge : tree -> tree -> tree

    val remove : Level.t_ -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : Level.t_ -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> (t, t) prod

    val ltb_tree : Level.t_ -> tree -> bool

    val gtb_tree : Level.t_ -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = Level.t_

          val compare : Level.t_ -> Level.t_ -> comparison

          val eq_dec : Level.t_ -> Level.t_ -> sumbool
         end

        module TO :
         sig
          type t = Level.t_

          val compare : Level.t_ -> Level.t_ -> comparison

          val eq_dec : Level.t_ -> Level.t_ -> sumbool
         end
       end

      val eq_dec : Level.t_ -> Level.t_ -> sumbool

      val lt_dec : Level.t_ -> Level.t_ -> sumbool

      val eqb : Level.t_ -> Level.t_ -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = Level.t_

            val compare : Level.t_ -> Level.t_ -> comparison

            val eq_dec : Level.t_ -> Level.t_ -> sumbool
           end

          module TO :
           sig
            type t = Level.t_

            val compare : Level.t_ -> Level.t_ -> comparison

            val eq_dec : Level.t_ -> Level.t_ -> sumbool
           end
         end

        val eq_dec : Level.t_ -> Level.t_ -> sumbool

        val lt_dec : Level.t_ -> Level.t_ -> sumbool

        val eqb : Level.t_ -> Level.t_ -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * Level.t_ * t
    | R_bal_1 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_2 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_3 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * 
       tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_4 of t * Level.t_ * t
    | R_bal_5 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_6 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_7 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * 
       tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_8 of t * Level.t_ * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * Level.t_
       * tree * (t, elt) prod * coq_R_remove_min * t * elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * 
       tree * Int.Z_as_Int.t * tree * Level.t_ * tree * t * elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = Level.t_

    val compare : Level.t_ -> Level.t_ -> comparison

    val eq_dec : Level.t_ -> Level.t_ -> sumbool
   end

  type elt = Level.t_

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val eq_dec : t -> t -> sumbool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

module LevelSetFact :
 sig
  val eqb : Level.t_ -> Level.t_ -> bool
 end

module LevelSetOrdProp :
 sig
  module ME :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = Level.t_

        val compare : Level.t_ -> Level.t_ -> comparison

        val eq_dec : Level.t_ -> Level.t_ -> sumbool
       end

      module TO :
       sig
        type t = Level.t_

        val compare : Level.t_ -> Level.t_ -> comparison

        val eq_dec : Level.t_ -> Level.t_ -> sumbool
       end
     end

    val eq_dec : Level.t_ -> Level.t_ -> sumbool

    val lt_dec : Level.t_ -> Level.t_ -> sumbool

    val eqb : Level.t_ -> Level.t_ -> bool
   end

  module ML :
   sig
   end

  module P :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : Level.t_ -> Level.t_ -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb : Level.t_ -> Level.t_ -> bool
     end

    val coq_In_dec : LevelSet.elt -> LevelSet.t -> sumbool

    val of_list : LevelSet.elt list -> LevelSet.t

    val to_list : LevelSet.t -> LevelSet.elt list

    val fold_rec :
      (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> (LevelSet.t -> __
      -> 'a2) -> (LevelSet.elt -> 'a1 -> LevelSet.t -> LevelSet.t -> __ -> __
      -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> (LevelSet.t ->
      LevelSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelSet.elt -> 'a1
      -> LevelSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> 'a2 ->
      (LevelSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> (LevelSet.t -> LevelSet.t -> 'a1
      -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelSet.elt -> 'a1 -> LevelSet.t -> __
      -> 'a2 -> 'a2) -> LevelSet.t -> 'a2

    val fold_rel :
      (LevelSet.elt -> 'a1 -> 'a1) -> (LevelSet.elt -> 'a2 -> 'a2) -> 'a1 ->
      'a2 -> LevelSet.t -> 'a3 -> (LevelSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
      'a3) -> 'a3

    val set_induction :
      (LevelSet.t -> __ -> 'a1) -> (LevelSet.t -> LevelSet.t -> 'a1 ->
      LevelSet.elt -> __ -> __ -> 'a1) -> LevelSet.t -> 'a1

    val set_induction_bis :
      (LevelSet.t -> LevelSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (LevelSet.elt
      -> LevelSet.t -> __ -> 'a1 -> 'a1) -> LevelSet.t -> 'a1

    val cardinal_inv_2 : LevelSet.t -> nat -> LevelSet.elt

    val cardinal_inv_2b : LevelSet.t -> LevelSet.elt
   end

  val gtb : Level.t_ -> Level.t_ -> bool

  val leb : Level.t_ -> Level.t_ -> bool

  val elements_lt : Level.t_ -> LevelSet.t -> Level.t_ list

  val elements_ge : Level.t_ -> LevelSet.t -> Level.t_ list

  val set_induction_max :
    (LevelSet.t -> __ -> 'a1) -> (LevelSet.t -> LevelSet.t -> 'a1 -> Level.t_
    -> __ -> __ -> 'a1) -> LevelSet.t -> 'a1

  val set_induction_min :
    (LevelSet.t -> __ -> 'a1) -> (LevelSet.t -> LevelSet.t -> 'a1 -> Level.t_
    -> __ -> __ -> 'a1) -> LevelSet.t -> 'a1
 end

module LevelSetProp :
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb : Level.t_ -> Level.t_ -> bool
     end

    module MSetLogicalFacts :
     sig
     end

    module MSetDecideAuxiliary :
     sig
     end

    module MSetDecideTestCases :
     sig
     end
   end

  module FM :
   sig
    val eqb : Level.t_ -> Level.t_ -> bool
   end

  val coq_In_dec : LevelSet.elt -> LevelSet.t -> sumbool

  val of_list : LevelSet.elt list -> LevelSet.t

  val to_list : LevelSet.t -> LevelSet.elt list

  val fold_rec :
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> (LevelSet.t -> __ ->
    'a2) -> (LevelSet.elt -> 'a1 -> LevelSet.t -> LevelSet.t -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> (LevelSet.t ->
    LevelSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelSet.elt -> 'a1 ->
    LevelSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_nodep :
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelSet.t -> 'a2 -> (LevelSet.elt
    -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_weak :
    (LevelSet.elt -> 'a1 -> 'a1) -> 'a1 -> (LevelSet.t -> LevelSet.t -> 'a1
    -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelSet.elt -> 'a1 -> LevelSet.t -> __
    -> 'a2 -> 'a2) -> LevelSet.t -> 'a2

  val fold_rel :
    (LevelSet.elt -> 'a1 -> 'a1) -> (LevelSet.elt -> 'a2 -> 'a2) -> 'a1 ->
    'a2 -> LevelSet.t -> 'a3 -> (LevelSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
    'a3) -> 'a3

  val set_induction :
    (LevelSet.t -> __ -> 'a1) -> (LevelSet.t -> LevelSet.t -> 'a1 ->
    LevelSet.elt -> __ -> __ -> 'a1) -> LevelSet.t -> 'a1

  val set_induction_bis :
    (LevelSet.t -> LevelSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (LevelSet.elt ->
    LevelSet.t -> __ -> 'a1 -> 'a1) -> LevelSet.t -> 'a1

  val cardinal_inv_2 : LevelSet.t -> nat -> LevelSet.elt

  val cardinal_inv_2b : LevelSet.t -> LevelSet.elt
 end

module LevelSetDecide :
 sig
  module F :
   sig
    val eqb : Level.t_ -> Level.t_ -> bool
   end

  module MSetLogicalFacts :
   sig
   end

  module MSetDecideAuxiliary :
   sig
   end

  module MSetDecideTestCases :
   sig
   end
 end

module LevelSetExtraOrdProp :
 sig
  module P :
   sig
    val coq_Exists_dec : LevelSet.t -> (Level.t_ -> sumbool) -> sumbool
   end

  val above : Level.t_ -> LevelSet.t -> bool

  val below : Level.t_ -> LevelSet.t -> bool
 end

module LevelSetExtraDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a1 -> (Int.Z_as_Int.t -> LevelSet.Raw.tree -> 'a1 -> Level.t_ ->
      LevelSet.Raw.tree -> 'a1 -> 'a1) -> LevelSet.Raw.tree -> 'a1

    val tree_rec :
      'a1 -> (Int.Z_as_Int.t -> LevelSet.Raw.tree -> 'a1 -> Level.t_ ->
      LevelSet.Raw.tree -> 'a1 -> 'a1) -> LevelSet.Raw.tree -> 'a1

    val tree_caset_nodep :
      'a1 -> (Int.Z_as_Int.t -> LevelSet.Raw.tree -> 'a1 -> Level.t_ ->
      LevelSet.Raw.tree -> 'a1 -> 'a1) -> LevelSet.Raw.tree -> 'a1

    val tree_rect_nodep :
      'a1 -> (Int.Z_as_Int.t -> LevelSet.Raw.tree -> 'a1 -> Level.t_ ->
      LevelSet.Raw.tree -> 'a1 -> 'a1) -> LevelSet.Raw.tree -> 'a1

    val tree_rec_nodep :
      'a1 -> (Int.Z_as_Int.t -> LevelSet.Raw.tree -> 'a1 -> Level.t_ ->
      LevelSet.Raw.tree -> 'a1 -> 'a1) -> LevelSet.Raw.tree -> 'a1

    val lt_tree_dec : Level.t_ -> LevelSet.Raw.tree -> sumbool

    val gt_tree_dec : Level.t_ -> LevelSet.Raw.tree -> sumbool

    val bst_dec : LevelSet.Raw.tree -> sumbool
   end
 end

module LS :
 sig
  module Raw :
   sig
    type elt = Level.t_

    type tree = LevelSet.Raw.tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree * Level.t_ * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : Level.t_ -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : Level.t_ list -> tree -> Level.t_ list

    val elements : tree -> Level.t_ list

    val rev_elements_aux : Level.t_ list -> tree -> Level.t_ list

    val rev_elements : tree -> Level.t_ list

    val cardinal : tree -> nat

    val maxdepth : tree -> nat

    val mindepth : tree -> nat

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration = LevelSet.Raw.enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      Level.t_ -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> Level.t_ -> tree -> bool

    val subsetr : (tree -> bool) -> Level.t_ -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : Level.t_ -> tree

    val create : t -> Level.t_ -> t -> tree

    val assert_false : t -> Level.t_ -> t -> tree

    val bal : t -> Level.t_ -> t -> tree

    val add : Level.t_ -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> (t, elt) prod

    val merge : tree -> tree -> tree

    val remove : Level.t_ -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = LevelSet.Raw.triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : Level.t_ -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> (t, t) prod

    val ltb_tree : Level.t_ -> tree -> bool

    val gtb_tree : Level.t_ -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = Level.t_

          val compare : Level.t_ -> Level.t_ -> comparison

          val eq_dec : Level.t_ -> Level.t_ -> sumbool
         end

        module TO :
         sig
          type t = Level.t_

          val compare : Level.t_ -> Level.t_ -> comparison

          val eq_dec : Level.t_ -> Level.t_ -> sumbool
         end
       end

      val eq_dec : Level.t_ -> Level.t_ -> sumbool

      val lt_dec : Level.t_ -> Level.t_ -> sumbool

      val eqb : Level.t_ -> Level.t_ -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = Level.t_

            val compare : Level.t_ -> Level.t_ -> comparison

            val eq_dec : Level.t_ -> Level.t_ -> sumbool
           end

          module TO :
           sig
            type t = Level.t_

            val compare : Level.t_ -> Level.t_ -> comparison

            val eq_dec : Level.t_ -> Level.t_ -> sumbool
           end
         end

        val eq_dec : Level.t_ -> Level.t_ -> sumbool

        val lt_dec : Level.t_ -> Level.t_ -> sumbool

        val eqb : Level.t_ -> Level.t_ -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal = LevelSet.Raw.coq_R_bal =
    | R_bal_0 of t * Level.t_ * t
    | R_bal_1 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_2 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_3 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * 
       tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_4 of t * Level.t_ * t
    | R_bal_5 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_6 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_7 of t * Level.t_ * t * Int.Z_as_Int.t * tree * Level.t_ * 
       tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_bal_8 of t * Level.t_ * t

    type coq_R_remove_min = LevelSet.Raw.coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * Level.t_
       * tree * (t, elt) prod * coq_R_remove_min * t * elt

    type coq_R_merge = LevelSet.Raw.coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * elt

    type coq_R_concat = LevelSet.Raw.coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * 
       tree * Int.Z_as_Int.t * tree * Level.t_ * tree * t * elt

    type coq_R_inter = LevelSet.Raw.coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter

    type coq_R_diff = LevelSet.Raw.coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff

    type coq_R_union = LevelSet.Raw.coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * Level.t_ * tree
       * Int.Z_as_Int.t * tree * Level.t_ * tree * t * bool * t * tree
       * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = Level.t_

    val compare : Level.t_ -> Level.t_ -> comparison

    val eq_dec : Level.t_ -> Level.t_ -> sumbool
   end

  type elt = Level.t_

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val eq_dec : t -> t -> sumbool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

val coq_LevelSet_pair : LevelSet.elt -> LevelSet.elt -> LevelSet.t

module PropLevel :
 sig
  type t =
  | Coq_lSProp
  | Coq_lProp

  val t_rect : 'a1 -> 'a1 -> t -> 'a1

  val t_rec : 'a1 -> 'a1 -> t -> 'a1

  val coq_NoConfusionPackage_t : t coq_NoConfusionPackage

  val t_eqdec : t -> t -> t dec_eq

  val t_EqDec : t coq_EqDec

  val compare : t -> t -> comparison

  val lt__rect : 'a1 -> t -> t -> 'a1

  val lt__rec : 'a1 -> t -> t -> 'a1
 end

module LevelExpr :
 sig
  type t = (Level.t, nat) prod

  val coq_Evaluable : t coq_Evaluable

  val succ : t -> (Level.t, nat) prod

  val get_level : t -> Level.t

  val get_noprop : t -> Level.t option

  val is_level : t -> bool

  val make : Level.t -> t

  val set : t

  val type1 : t

  val from_kernel_repr : (Level.t, bool) prod -> t

  val to_kernel_repr : t -> (Level.t, bool) prod

  val compare : t -> t -> comparison

  val reflect_t : t coq_ReflectEq

  val eq_dec : t -> t -> sumbool
 end

module LevelExprSet :
 sig
  module E :
   sig
    type t = (Level.t, nat) prod

    val compare : (Level.t, nat) prod -> (Level.t, nat) prod -> comparison

    val eq_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool
   end

  module Raw :
   sig
    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = (Level.t, nat) prod

          val compare :
            (Level.t, nat) prod -> (Level.t, nat) prod -> comparison

          val eq_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool
         end

        module TO :
         sig
          type t = (Level.t, nat) prod

          val compare :
            (Level.t, nat) prod -> (Level.t, nat) prod -> comparison

          val eq_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool
         end
       end

      val eq_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool

      val lt_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool

      val eqb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool
     end

    module ML :
     sig
     end

    type elt = (Level.t, nat) prod

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : (Level.t, nat) prod -> (Level.t, nat) prod list -> bool

    val add :
      (Level.t, nat) prod -> (Level.t, nat) prod list -> (Level.t, nat) prod
      list

    val singleton : elt -> elt list

    val remove : (Level.t, nat) prod -> (Level.t, nat) prod list -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : (Level.t, nat) prod list -> (Level.t, nat) prod list -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> (t, t) prod

    val cardinal : t -> nat

    val elements : t -> elt list

    val min_elt : t -> elt option

    val max_elt : t -> elt option

    val choose : t -> elt option

    val compare :
      (Level.t, nat) prod list -> (Level.t, nat) prod list -> comparison

    val inf : (Level.t, nat) prod -> (Level.t, nat) prod list -> bool

    val isok : (Level.t, nat) prod list -> bool

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = (Level.t, nat) prod

            val compare :
              (Level.t, nat) prod -> (Level.t, nat) prod -> comparison

            val eq_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool
           end

          module TO :
           sig
            type t = (Level.t, nat) prod

            val compare :
              (Level.t, nat) prod -> (Level.t, nat) prod -> comparison

            val eq_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool
           end
         end

        val eq_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool

        val lt_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool

        val eqb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool
       end
     end
   end

  type elt = (Level.t, nat) prod

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val eq_dec : t -> t -> sumbool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

module LevelExprSetFact :
 sig
  val eqb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool
 end

module LevelExprSetOrdProp :
 sig
  module ME :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = (Level.t, nat) prod

        val compare : (Level.t, nat) prod -> (Level.t, nat) prod -> comparison

        val eq_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool
       end

      module TO :
       sig
        type t = (Level.t, nat) prod

        val compare : (Level.t, nat) prod -> (Level.t, nat) prod -> comparison

        val eq_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool
       end
     end

    val eq_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool

    val lt_dec : (Level.t, nat) prod -> (Level.t, nat) prod -> sumbool

    val eqb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool
   end

  module ML :
   sig
   end

  module P :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool
     end

    val coq_In_dec : LevelExprSet.elt -> LevelExprSet.t -> sumbool

    val of_list : LevelExprSet.elt list -> LevelExprSet.t

    val to_list : LevelExprSet.t -> LevelExprSet.elt list

    val fold_rec :
      (LevelExprSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelExprSet.t ->
      (LevelExprSet.t -> __ -> 'a2) -> (LevelExprSet.elt -> 'a1 ->
      LevelExprSet.t -> LevelExprSet.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (LevelExprSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelExprSet.t ->
      (LevelExprSet.t -> LevelExprSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
      (LevelExprSet.elt -> 'a1 -> LevelExprSet.t -> __ -> __ -> 'a2 -> 'a2)
      -> 'a2

    val fold_rec_nodep :
      (LevelExprSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelExprSet.t -> 'a2 ->
      (LevelExprSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (LevelExprSet.elt -> 'a1 -> 'a1) -> 'a1 -> (LevelExprSet.t ->
      LevelExprSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelExprSet.elt
      -> 'a1 -> LevelExprSet.t -> __ -> 'a2 -> 'a2) -> LevelExprSet.t -> 'a2

    val fold_rel :
      (LevelExprSet.elt -> 'a1 -> 'a1) -> (LevelExprSet.elt -> 'a2 -> 'a2) ->
      'a1 -> 'a2 -> LevelExprSet.t -> 'a3 -> (LevelExprSet.elt -> 'a1 -> 'a2
      -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (LevelExprSet.t -> __ -> 'a1) -> (LevelExprSet.t -> LevelExprSet.t ->
      'a1 -> LevelExprSet.elt -> __ -> __ -> 'a1) -> LevelExprSet.t -> 'a1

    val set_induction_bis :
      (LevelExprSet.t -> LevelExprSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
      (LevelExprSet.elt -> LevelExprSet.t -> __ -> 'a1 -> 'a1) ->
      LevelExprSet.t -> 'a1

    val cardinal_inv_2 : LevelExprSet.t -> nat -> LevelExprSet.elt

    val cardinal_inv_2b : LevelExprSet.t -> LevelExprSet.elt
   end

  val gtb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool

  val leb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool

  val elements_lt :
    (Level.t, nat) prod -> LevelExprSet.t -> (Level.t, nat) prod list

  val elements_ge :
    (Level.t, nat) prod -> LevelExprSet.t -> (Level.t, nat) prod list

  val set_induction_max :
    (LevelExprSet.t -> __ -> 'a1) -> (LevelExprSet.t -> LevelExprSet.t -> 'a1
    -> (Level.t, nat) prod -> __ -> __ -> 'a1) -> LevelExprSet.t -> 'a1

  val set_induction_min :
    (LevelExprSet.t -> __ -> 'a1) -> (LevelExprSet.t -> LevelExprSet.t -> 'a1
    -> (Level.t, nat) prod -> __ -> __ -> 'a1) -> LevelExprSet.t -> 'a1
 end

module LevelExprSetProp :
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool
     end

    module MSetLogicalFacts :
     sig
     end

    module MSetDecideAuxiliary :
     sig
     end

    module MSetDecideTestCases :
     sig
     end
   end

  module FM :
   sig
    val eqb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool
   end

  val coq_In_dec : LevelExprSet.elt -> LevelExprSet.t -> sumbool

  val of_list : LevelExprSet.elt list -> LevelExprSet.t

  val to_list : LevelExprSet.t -> LevelExprSet.elt list

  val fold_rec :
    (LevelExprSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelExprSet.t ->
    (LevelExprSet.t -> __ -> 'a2) -> (LevelExprSet.elt -> 'a1 ->
    LevelExprSet.t -> LevelExprSet.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (LevelExprSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelExprSet.t ->
    (LevelExprSet.t -> LevelExprSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
    (LevelExprSet.elt -> 'a1 -> LevelExprSet.t -> __ -> __ -> 'a2 -> 'a2) ->
    'a2

  val fold_rec_nodep :
    (LevelExprSet.elt -> 'a1 -> 'a1) -> 'a1 -> LevelExprSet.t -> 'a2 ->
    (LevelExprSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_weak :
    (LevelExprSet.elt -> 'a1 -> 'a1) -> 'a1 -> (LevelExprSet.t ->
    LevelExprSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (LevelExprSet.elt ->
    'a1 -> LevelExprSet.t -> __ -> 'a2 -> 'a2) -> LevelExprSet.t -> 'a2

  val fold_rel :
    (LevelExprSet.elt -> 'a1 -> 'a1) -> (LevelExprSet.elt -> 'a2 -> 'a2) ->
    'a1 -> 'a2 -> LevelExprSet.t -> 'a3 -> (LevelExprSet.elt -> 'a1 -> 'a2 ->
    __ -> 'a3 -> 'a3) -> 'a3

  val set_induction :
    (LevelExprSet.t -> __ -> 'a1) -> (LevelExprSet.t -> LevelExprSet.t -> 'a1
    -> LevelExprSet.elt -> __ -> __ -> 'a1) -> LevelExprSet.t -> 'a1

  val set_induction_bis :
    (LevelExprSet.t -> LevelExprSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
    (LevelExprSet.elt -> LevelExprSet.t -> __ -> 'a1 -> 'a1) ->
    LevelExprSet.t -> 'a1

  val cardinal_inv_2 : LevelExprSet.t -> nat -> LevelExprSet.elt

  val cardinal_inv_2b : LevelExprSet.t -> LevelExprSet.elt
 end

module LevelExprSetDecide :
 sig
  module F :
   sig
    val eqb : (Level.t, nat) prod -> (Level.t, nat) prod -> bool
   end

  module MSetLogicalFacts :
   sig
   end

  module MSetDecideAuxiliary :
   sig
   end

  module MSetDecideTestCases :
   sig
   end
 end

module LevelExprSetExtraOrdProp :
 sig
  module P :
   sig
    val coq_Exists_dec :
      LevelExprSet.t -> ((Level.t, nat) prod -> sumbool) -> sumbool
   end

  val above : (Level.t, nat) prod -> LevelExprSet.t -> bool

  val below : (Level.t, nat) prod -> LevelExprSet.t -> bool
 end

val levelexprset_reflect : LevelExprSet.t coq_ReflectEq

val levelexprset_eq_dec : LevelExprSet.t coq_EqDec

type nonEmptyLevelExprSet =
  LevelExprSet.t
  (* singleton inductive, whose constructor was Build_nonEmptyLevelExprSet *)

val t_set : nonEmptyLevelExprSet -> LevelExprSet.t

val coq_NoConfusionPackage_nonEmptyLevelExprSet :
  nonEmptyLevelExprSet coq_NoConfusionPackage

module NonEmptySetFacts :
 sig
  val singleton : LevelExpr.t -> nonEmptyLevelExprSet

  val add : LevelExpr.t -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet

  val add_list :
    LevelExpr.t list -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet

  val to_nonempty_list :
    nonEmptyLevelExprSet -> (LevelExpr.t, LevelExpr.t list) prod

  val map :
    (LevelExpr.t -> LevelExpr.t) -> nonEmptyLevelExprSet ->
    nonEmptyLevelExprSet

  val non_empty_union :
    nonEmptyLevelExprSet -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet
 end

module LevelAlgExpr :
 sig
  type t = nonEmptyLevelExprSet

  val levelexprset_reflect : t coq_ReflectEq

  val eq_dec_univ0 : t coq_EqDec

  val make : LevelExpr.t -> t

  val make' : Level.t -> nonEmptyLevelExprSet

  val exprs : t -> (LevelExpr.t, LevelExpr.t list) prod

  val coq_Evaluable : t coq_Evaluable

  val is_levels : t -> bool

  val is_level : t -> bool

  val succ : t -> t

  val sup : t -> t -> t

  val get_is_level : t -> Level.t option
 end

type concreteUniverses =
| UProp
| USProp
| UType of nat

val concreteUniverses_rect :
  'a1 -> 'a1 -> (nat -> 'a1) -> concreteUniverses -> 'a1

val concreteUniverses_rec :
  'a1 -> 'a1 -> (nat -> 'a1) -> concreteUniverses -> 'a1

val coq_NoConfusionPackage_concreteUniverses :
  concreteUniverses coq_NoConfusionPackage

val concreteUniverses_eqdec :
  concreteUniverses -> concreteUniverses -> concreteUniverses dec_eq

val concreteUniverses_EqDec : concreteUniverses coq_EqDec

val cuniv_sup : concreteUniverses -> concreteUniverses -> concreteUniverses

val cuniv_of_product :
  concreteUniverses -> concreteUniverses -> concreteUniverses

val cuniv_sup_not_uproplevel :
  concreteUniverses -> concreteUniverses -> (nat, __) sigT

type allowed_eliminations =
| IntoSProp
| IntoPropSProp
| IntoSetPropSProp
| IntoAny

val allowed_eliminations_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> allowed_eliminations -> 'a1

val allowed_eliminations_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> allowed_eliminations -> 'a1

val coq_NoConfusionPackage_allowed_eliminations :
  allowed_eliminations coq_NoConfusionPackage

val allowed_eliminations_eqdec :
  allowed_eliminations -> allowed_eliminations -> allowed_eliminations dec_eq

val allowed_eliminations_EqDec : allowed_eliminations coq_EqDec

module Universe :
 sig
  type t_ =
  | Coq_lProp
  | Coq_lSProp
  | Coq_lType of LevelAlgExpr.t

  val t__rect : 'a1 -> 'a1 -> (LevelAlgExpr.t -> 'a1) -> t_ -> 'a1

  val t__rec : 'a1 -> 'a1 -> (LevelAlgExpr.t -> 'a1) -> t_ -> 'a1

  val coq_NoConfusionPackage_t_ : t_ coq_NoConfusionPackage

  module Coq__1 : sig
   type t = t_
  end
  include module type of struct include Coq__1 end

  val eqb : t -> t -> bool

  val reflect_eq_universe : t coq_ReflectEq

  val eq_dec_univ : t coq_EqDec

  val make : Level.t -> t

  val of_expr : LevelExpr.t -> t_

  val add_to_exprs : LevelExpr.t -> t -> t

  val add_list_to_exprs : LevelExpr.t list -> t -> t

  val is_levels : t -> bool

  val is_level : t -> bool

  val is_sprop : t -> bool

  val is_prop : t -> bool

  val is_type_sort : t -> bool

  val type0 : t

  val type1 : t

  val of_levels : (PropLevel.t, Level.t) sum -> t

  val from_kernel_repr :
    (Level.t, bool) prod -> (Level.t, bool) prod list -> t

  val super : t -> t

  val sup : t -> t -> t

  val get_univ_exprs : t -> LevelAlgExpr.t

  val sort_of_product : t -> t -> t

  val get_is_level : t -> Level.t option

  val to_cuniv : valuation -> t_ -> concreteUniverses

  val lt__sig_pack : t -> t -> (t * t) * __

  val lt__Signature : t -> t -> (t * t) * __

  module OT :
   sig
    type t = Coq__1.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> sumbool
   end

  module OTOrig :
   sig
    type t = Coq__1.t

    val eq_dec : Coq__1.t -> Coq__1.t -> sumbool

    val compare : Coq__1.t -> Coq__1.t -> Coq__1.t OrderedType.coq_Compare
   end
 end

module UniverseMap :
 sig
  module E :
   sig
    type t = Universe.t

    val compare :
      Universe.t -> Universe.t -> Universe.t OrderedType.coq_Compare

    val eq_dec : Universe.t -> Universe.t -> sumbool
   end

  module Raw :
   sig
    type key = Universe.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Int.Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
      Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
      Int.Z_as_Int.t -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Int.Z_as_Int.t

    val cardinal : 'a1 tree -> nat

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : Universe.t -> 'a1 tree -> bool

    val find : Universe.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : Universe.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : Universe.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list

    val elements : 'a1 tree -> (key, 'a1) prod list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> Universe.t -> 'a1 -> ('a1 enumeration -> bool)
      -> 'a1 enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = Universe.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : Universe.t -> Universe.t -> sumbool

        val lt_dec : Universe.t -> Universe.t -> sumbool

        val eqb : Universe.t -> Universe.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = Universe.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Universe.t -> Universe.t -> sumbool

          val lt_dec : Universe.t -> Universe.t -> sumbool

          val eqb : Universe.t -> Universe.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = Universe.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Universe.t -> Universe.t -> sumbool

          val lt_dec : Universe.t -> Universe.t -> sumbool

          val eqb : Universe.t -> Universe.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = Universe.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Universe.t -> Universe.t -> sumbool

            val lt_dec : Universe.t -> Universe.t -> sumbool

            val eqb : Universe.t -> Universe.t -> bool
           end
         end

        type key = Universe.t

        type 'elt t = (Universe.t, 'elt) prod list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        val find : key -> 'a1 t -> 'a1 option

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        val remove : key -> 'a1 t -> 'a1 t

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
          'a3) prod list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        Universe.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
        __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
        coq_R_mem -> 'a2

      val coq_R_mem_rec :
        Universe.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
        __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
        coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        Universe.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option
        -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
        __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
        -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        Universe.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option
        -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
        __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
        -> 'a1 option -> 'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Int.Z_as_Int.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Int.Z_as_Int.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 'elt
         * 'elt tree * Int.Z_as_Int.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Int.Z_as_Int.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Int.Z_as_Int.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 'elt
         * 'elt tree * Int.Z_as_Int.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
        -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
        -> __ -> 'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 coq_R_add -> 'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Int.Z_as_Int.t
         * ('elt tree, (key, 'elt) prod) prod * 'elt coq_R_remove_min
         * 'elt tree * (key, 'elt) prod

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod -> 'a1 coq_R_remove_min -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> ('a1 tree, (key, 'a1) prod) prod -> 'a1
        coq_R_remove_min -> 'a2 -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2)
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod)
        prod -> 'a1 coq_R_remove_min -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Int.Z_as_Int.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt tree * (key, 'elt) prod * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> 'a2)
        -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key ->
        'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> 'a2)
        -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> key ->
        'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        Universe.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
        __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        Universe.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
        __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Int.Z_as_Int.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Int.Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt tree * (key, 'elt) prod

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> 'a2)
        -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> 'a2)
        -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> 'a1 tree -> (key, 'a1) prod -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree

      val coq_R_split_rect :
        Universe.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple
        -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        Universe.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple
        -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option
         * 'x tree * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 ->
        __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> 'a2 tree
        -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 ->
        __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> 'a2 tree
        -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Int.Z_as_Int.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Int.Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Int.Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Int.Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Int.Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree ->
        key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2
        option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
        -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree ->
        key -> 'a2 -> 'a2 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2
        option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt
        -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Int.Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key, 'a1) prod list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = Universe.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key, 'a1) prod list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module UniverseMapFact :
 sig
  module F :
   sig
    val eqb : Universe.t -> Universe.t -> bool

    val coq_In_dec : 'a1 UniverseMap.t -> UniverseMap.key -> sumbool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3

  val of_list : (UniverseMap.key, 'a1) prod list -> 'a1 UniverseMap.t

  val to_list : 'a1 UniverseMap.t -> (UniverseMap.key, 'a1) prod list

  val fold_rec :
    (UniverseMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 UniverseMap.t ->
    ('a1 UniverseMap.t -> __ -> 'a3) -> (UniverseMap.key -> 'a1 -> 'a2 -> 'a1
    UniverseMap.t -> 'a1 UniverseMap.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_bis :
    (UniverseMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 UniverseMap.t ->
    ('a1 UniverseMap.t -> 'a1 UniverseMap.t -> 'a2 -> __ -> 'a3 -> 'a3) ->
    'a3 -> (UniverseMap.key -> 'a1 -> 'a2 -> 'a1 UniverseMap.t -> __ -> __ ->
    'a3 -> 'a3) -> 'a3

  val fold_rec_nodep :
    (UniverseMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 UniverseMap.t -> 'a3
    -> (UniverseMap.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (UniverseMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 UniverseMap.t ->
    'a1 UniverseMap.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (UniverseMap.key
    -> 'a1 -> 'a2 -> 'a1 UniverseMap.t -> __ -> 'a3 -> 'a3) -> 'a1
    UniverseMap.t -> 'a3

  val fold_rel :
    (UniverseMap.key -> 'a1 -> 'a2 -> 'a2) -> (UniverseMap.key -> 'a1 -> 'a3
    -> 'a3) -> 'a2 -> 'a3 -> 'a1 UniverseMap.t -> 'a4 -> (UniverseMap.key ->
    'a1 -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

  val map_induction :
    ('a1 UniverseMap.t -> __ -> 'a2) -> ('a1 UniverseMap.t -> 'a1
    UniverseMap.t -> 'a2 -> UniverseMap.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1
    UniverseMap.t -> 'a2

  val map_induction_bis :
    ('a1 UniverseMap.t -> 'a1 UniverseMap.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
    (UniverseMap.key -> 'a1 -> 'a1 UniverseMap.t -> __ -> 'a2 -> 'a2) -> 'a1
    UniverseMap.t -> 'a2

  val cardinal_inv_2 : 'a1 UniverseMap.t -> nat -> (UniverseMap.key, 'a1) prod

  val cardinal_inv_2b : 'a1 UniverseMap.t -> (UniverseMap.key, 'a1) prod

  val filter :
    (UniverseMap.key -> 'a1 -> bool) -> 'a1 UniverseMap.t -> 'a1 UniverseMap.t

  val for_all : (UniverseMap.key -> 'a1 -> bool) -> 'a1 UniverseMap.t -> bool

  val exists_ : (UniverseMap.key -> 'a1 -> bool) -> 'a1 UniverseMap.t -> bool

  val partition :
    (UniverseMap.key -> 'a1 -> bool) -> 'a1 UniverseMap.t -> ('a1
    UniverseMap.t, 'a1 UniverseMap.t) prod

  val update : 'a1 UniverseMap.t -> 'a1 UniverseMap.t -> 'a1 UniverseMap.t

  val restrict : 'a1 UniverseMap.t -> 'a1 UniverseMap.t -> 'a1 UniverseMap.t

  val diff : 'a1 UniverseMap.t -> 'a1 UniverseMap.t -> 'a1 UniverseMap.t

  val coq_Partition_In :
    'a1 UniverseMap.t -> 'a1 UniverseMap.t -> 'a1 UniverseMap.t ->
    UniverseMap.key -> sumbool

  val update_dec :
    'a1 UniverseMap.t -> 'a1 UniverseMap.t -> UniverseMap.key -> 'a1 ->
    sumbool

  val filter_dom :
    (UniverseMap.key -> bool) -> 'a1 UniverseMap.t -> 'a1 UniverseMap.t

  val filter_range : ('a1 -> bool) -> 'a1 UniverseMap.t -> 'a1 UniverseMap.t

  val for_all_dom : (UniverseMap.key -> bool) -> 'a1 UniverseMap.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 UniverseMap.t -> bool

  val exists_dom : (UniverseMap.key -> bool) -> 'a1 UniverseMap.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 UniverseMap.t -> bool

  val partition_dom :
    (UniverseMap.key -> bool) -> 'a1 UniverseMap.t -> ('a1 UniverseMap.t, 'a1
    UniverseMap.t) prod

  val partition_range :
    ('a1 -> bool) -> 'a1 UniverseMap.t -> ('a1 UniverseMap.t, 'a1
    UniverseMap.t) prod
 end

module UniverseMapExtraFact :
 sig
 end

module UniverseMapDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a2 -> ('a1 UniverseMap.Raw.tree -> 'a2 -> UniverseMap.Raw.key -> 'a1
      -> 'a1 UniverseMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      UniverseMap.Raw.tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 UniverseMap.Raw.tree -> 'a2 -> UniverseMap.Raw.key -> 'a1
      -> 'a1 UniverseMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      UniverseMap.Raw.tree -> 'a2

    val tree_caset_nodep :
      'a2 -> ('a1 UniverseMap.Raw.tree -> 'a2 -> UniverseMap.Raw.key -> 'a1
      -> 'a1 UniverseMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      UniverseMap.Raw.tree -> 'a2

    val tree_rect_nodep :
      'a2 -> ('a1 UniverseMap.Raw.tree -> 'a2 -> UniverseMap.Raw.key -> 'a1
      -> 'a1 UniverseMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      UniverseMap.Raw.tree -> 'a2

    val tree_rec_nodep :
      'a2 -> ('a1 UniverseMap.Raw.tree -> 'a2 -> UniverseMap.Raw.key -> 'a1
      -> 'a1 UniverseMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      UniverseMap.Raw.tree -> 'a2

    val lt_tree_dec : Universe.t -> 'a1 UniverseMap.Raw.tree -> sumbool

    val gt_tree_dec : Universe.t -> 'a1 UniverseMap.Raw.tree -> sumbool

    val bst_dec : 'a1 UniverseMap.Raw.tree -> sumbool
   end
 end

val is_propositional : Universe.t -> bool

val is_prop_and_is_sprop_val_false : Universe.t -> valuation -> (nat, __) sigT

val is_not_prop_and_is_not_sprop : Universe.t -> (LevelAlgExpr.t, __) sigT

module ConstraintType :
 sig
  type t_ =
  | Le of coq_Z
  | Eq

  val t__rect : (coq_Z -> 'a1) -> 'a1 -> t_ -> 'a1

  val t__rec : (coq_Z -> 'a1) -> 'a1 -> t_ -> 'a1

  val coq_NoConfusionPackage_t_ : t_ coq_NoConfusionPackage

  val t__eqdec : t_ -> t_ -> t_ dec_eq

  val t__EqDec : t_ coq_EqDec

  type t = t_

  val coq_Le0 : t_

  val coq_Lt : t_

  val lt__sig_pack : t -> t -> (t * t) * __

  val lt__Signature : t -> t -> (t * t) * __

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module UnivConstraint :
 sig
  type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

  val make : Level.t -> ConstraintType.t -> Level.t -> t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> sumbool
 end

module ConstraintSet :
 sig
  module Raw :
   sig
    type elt = ((Level.t, ConstraintType.t) prod, Level.t) prod

    type tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux :
      ((Level.t, ConstraintType.t) prod, Level.t) prod list -> tree ->
      ((Level.t, ConstraintType.t) prod, Level.t) prod list

    val elements :
      tree -> ((Level.t, ConstraintType.t) prod, Level.t) prod list

    val rev_elements_aux :
      ((Level.t, ConstraintType.t) prod, Level.t) prod list -> tree ->
      ((Level.t, ConstraintType.t) prod, Level.t) prod list

    val rev_elements :
      tree -> ((Level.t, ConstraintType.t) prod, Level.t) prod list

    val cardinal : tree -> nat

    val maxdepth : tree -> nat

    val mindepth : tree -> nat

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> (enumeration ->
      comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl :
      (tree -> bool) -> ((Level.t, ConstraintType.t) prod, Level.t) prod ->
      tree -> bool

    val subsetr :
      (tree -> bool) -> ((Level.t, ConstraintType.t) prod, Level.t) prod ->
      tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree

    val create :
      t -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> t -> tree

    val assert_false :
      t -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> t -> tree

    val bal :
      t -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> t -> tree

    val add : ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> (t, elt) prod

    val merge : tree -> tree -> tree

    val remove :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> (t, t) prod

    val ltb_tree :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> bool

    val gtb_tree :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

          val compare :
            ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
            ConstraintType.t) prod, Level.t) prod -> comparison

          val eq_dec :
            ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
            ConstraintType.t) prod, Level.t) prod -> sumbool
         end

        module TO :
         sig
          type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

          val compare :
            ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
            ConstraintType.t) prod, Level.t) prod -> comparison

          val eq_dec :
            ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
            ConstraintType.t) prod, Level.t) prod -> sumbool
         end
       end

      val eq_dec :
        ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
        ConstraintType.t) prod, Level.t) prod -> sumbool

      val lt_dec :
        ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
        ConstraintType.t) prod, Level.t) prod -> sumbool

      val eqb :
        ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
        ConstraintType.t) prod, Level.t) prod -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

            val compare :
              ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
              ConstraintType.t) prod, Level.t) prod -> comparison

            val eq_dec :
              ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
              ConstraintType.t) prod, Level.t) prod -> sumbool
           end

          module TO :
           sig
            type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

            val compare :
              ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
              ConstraintType.t) prod, Level.t) prod -> comparison

            val eq_dec :
              ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
              ConstraintType.t) prod, Level.t) prod -> sumbool
           end
         end

        val eq_dec :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> sumbool

        val lt_dec :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> sumbool

        val eqb :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * t
    | R_bal_1 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_2 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_3 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_4 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * t
    | R_bal_5 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_6 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_7 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_8 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * (t, elt) prod * coq_R_remove_min * t * elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       bool * t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       bool * t * tree * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       bool * t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       bool * t * tree * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       bool * t * tree * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

    val compare :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> comparison

    val eq_dec :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> sumbool
   end

  type elt = ((Level.t, ConstraintType.t) prod, Level.t) prod

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val eq_dec : t -> t -> sumbool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

module ConstraintSetFact :
 sig
  val eqb :
    ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
    ConstraintType.t) prod, Level.t) prod -> bool
 end

module ConstraintSetOrdProp :
 sig
  module ME :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

        val compare :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> comparison

        val eq_dec :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> sumbool
       end

      module TO :
       sig
        type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

        val compare :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> comparison

        val eq_dec :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> sumbool
       end
     end

    val eq_dec :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> sumbool

    val lt_dec :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> sumbool

    val eqb :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> bool
   end

  module ML :
   sig
   end

  module P :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb :
        ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
        ConstraintType.t) prod, Level.t) prod -> bool
     end

    val coq_In_dec : ConstraintSet.elt -> ConstraintSet.t -> sumbool

    val of_list : ConstraintSet.elt list -> ConstraintSet.t

    val to_list : ConstraintSet.t -> ConstraintSet.elt list

    val fold_rec :
      (ConstraintSet.elt -> 'a1 -> 'a1) -> 'a1 -> ConstraintSet.t ->
      (ConstraintSet.t -> __ -> 'a2) -> (ConstraintSet.elt -> 'a1 ->
      ConstraintSet.t -> ConstraintSet.t -> __ -> __ -> __ -> 'a2 -> 'a2) ->
      'a2

    val fold_rec_bis :
      (ConstraintSet.elt -> 'a1 -> 'a1) -> 'a1 -> ConstraintSet.t ->
      (ConstraintSet.t -> ConstraintSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2
      -> (ConstraintSet.elt -> 'a1 -> ConstraintSet.t -> __ -> __ -> 'a2 ->
      'a2) -> 'a2

    val fold_rec_nodep :
      (ConstraintSet.elt -> 'a1 -> 'a1) -> 'a1 -> ConstraintSet.t -> 'a2 ->
      (ConstraintSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (ConstraintSet.elt -> 'a1 -> 'a1) -> 'a1 -> (ConstraintSet.t ->
      ConstraintSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
      (ConstraintSet.elt -> 'a1 -> ConstraintSet.t -> __ -> 'a2 -> 'a2) ->
      ConstraintSet.t -> 'a2

    val fold_rel :
      (ConstraintSet.elt -> 'a1 -> 'a1) -> (ConstraintSet.elt -> 'a2 -> 'a2)
      -> 'a1 -> 'a2 -> ConstraintSet.t -> 'a3 -> (ConstraintSet.elt -> 'a1 ->
      'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (ConstraintSet.t -> __ -> 'a1) -> (ConstraintSet.t -> ConstraintSet.t
      -> 'a1 -> ConstraintSet.elt -> __ -> __ -> 'a1) -> ConstraintSet.t ->
      'a1

    val set_induction_bis :
      (ConstraintSet.t -> ConstraintSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
      (ConstraintSet.elt -> ConstraintSet.t -> __ -> 'a1 -> 'a1) ->
      ConstraintSet.t -> 'a1

    val cardinal_inv_2 : ConstraintSet.t -> nat -> ConstraintSet.elt

    val cardinal_inv_2b : ConstraintSet.t -> ConstraintSet.elt
   end

  val gtb :
    ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
    ConstraintType.t) prod, Level.t) prod -> bool

  val leb :
    ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
    ConstraintType.t) prod, Level.t) prod -> bool

  val elements_lt :
    ((Level.t, ConstraintType.t) prod, Level.t) prod -> ConstraintSet.t ->
    ((Level.t, ConstraintType.t) prod, Level.t) prod list

  val elements_ge :
    ((Level.t, ConstraintType.t) prod, Level.t) prod -> ConstraintSet.t ->
    ((Level.t, ConstraintType.t) prod, Level.t) prod list

  val set_induction_max :
    (ConstraintSet.t -> __ -> 'a1) -> (ConstraintSet.t -> ConstraintSet.t ->
    'a1 -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> __ -> __ ->
    'a1) -> ConstraintSet.t -> 'a1

  val set_induction_min :
    (ConstraintSet.t -> __ -> 'a1) -> (ConstraintSet.t -> ConstraintSet.t ->
    'a1 -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> __ -> __ ->
    'a1) -> ConstraintSet.t -> 'a1
 end

module ConstraintSetProp :
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb :
        ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
        ConstraintType.t) prod, Level.t) prod -> bool
     end

    module MSetLogicalFacts :
     sig
     end

    module MSetDecideAuxiliary :
     sig
     end

    module MSetDecideTestCases :
     sig
     end
   end

  module FM :
   sig
    val eqb :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> bool
   end

  val coq_In_dec : ConstraintSet.elt -> ConstraintSet.t -> sumbool

  val of_list : ConstraintSet.elt list -> ConstraintSet.t

  val to_list : ConstraintSet.t -> ConstraintSet.elt list

  val fold_rec :
    (ConstraintSet.elt -> 'a1 -> 'a1) -> 'a1 -> ConstraintSet.t ->
    (ConstraintSet.t -> __ -> 'a2) -> (ConstraintSet.elt -> 'a1 ->
    ConstraintSet.t -> ConstraintSet.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (ConstraintSet.elt -> 'a1 -> 'a1) -> 'a1 -> ConstraintSet.t ->
    (ConstraintSet.t -> ConstraintSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
    (ConstraintSet.elt -> 'a1 -> ConstraintSet.t -> __ -> __ -> 'a2 -> 'a2)
    -> 'a2

  val fold_rec_nodep :
    (ConstraintSet.elt -> 'a1 -> 'a1) -> 'a1 -> ConstraintSet.t -> 'a2 ->
    (ConstraintSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_weak :
    (ConstraintSet.elt -> 'a1 -> 'a1) -> 'a1 -> (ConstraintSet.t ->
    ConstraintSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (ConstraintSet.elt
    -> 'a1 -> ConstraintSet.t -> __ -> 'a2 -> 'a2) -> ConstraintSet.t -> 'a2

  val fold_rel :
    (ConstraintSet.elt -> 'a1 -> 'a1) -> (ConstraintSet.elt -> 'a2 -> 'a2) ->
    'a1 -> 'a2 -> ConstraintSet.t -> 'a3 -> (ConstraintSet.elt -> 'a1 -> 'a2
    -> __ -> 'a3 -> 'a3) -> 'a3

  val set_induction :
    (ConstraintSet.t -> __ -> 'a1) -> (ConstraintSet.t -> ConstraintSet.t ->
    'a1 -> ConstraintSet.elt -> __ -> __ -> 'a1) -> ConstraintSet.t -> 'a1

  val set_induction_bis :
    (ConstraintSet.t -> ConstraintSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
    (ConstraintSet.elt -> ConstraintSet.t -> __ -> 'a1 -> 'a1) ->
    ConstraintSet.t -> 'a1

  val cardinal_inv_2 : ConstraintSet.t -> nat -> ConstraintSet.elt

  val cardinal_inv_2b : ConstraintSet.t -> ConstraintSet.elt
 end

module CS :
 sig
  module Raw :
   sig
    type elt = ((Level.t, ConstraintType.t) prod, Level.t) prod

    type tree = ConstraintSet.Raw.tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux :
      ((Level.t, ConstraintType.t) prod, Level.t) prod list -> tree ->
      ((Level.t, ConstraintType.t) prod, Level.t) prod list

    val elements :
      tree -> ((Level.t, ConstraintType.t) prod, Level.t) prod list

    val rev_elements_aux :
      ((Level.t, ConstraintType.t) prod, Level.t) prod list -> tree ->
      ((Level.t, ConstraintType.t) prod, Level.t) prod list

    val rev_elements :
      tree -> ((Level.t, ConstraintType.t) prod, Level.t) prod list

    val cardinal : tree -> nat

    val maxdepth : tree -> nat

    val mindepth : tree -> nat

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration = ConstraintSet.Raw.enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> (enumeration ->
      comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl :
      (tree -> bool) -> ((Level.t, ConstraintType.t) prod, Level.t) prod ->
      tree -> bool

    val subsetr :
      (tree -> bool) -> ((Level.t, ConstraintType.t) prod, Level.t) prod ->
      tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree

    val create :
      t -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> t -> tree

    val assert_false :
      t -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> t -> tree

    val bal :
      t -> ((Level.t, ConstraintType.t) prod, Level.t) prod -> t -> tree

    val add : ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> (t, elt) prod

    val merge : tree -> tree -> tree

    val remove :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = ConstraintSet.Raw.triple = { t_left : t; t_in : bool;
                                               t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> (t, t) prod

    val ltb_tree :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> bool

    val gtb_tree :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

          val compare :
            ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
            ConstraintType.t) prod, Level.t) prod -> comparison

          val eq_dec :
            ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
            ConstraintType.t) prod, Level.t) prod -> sumbool
         end

        module TO :
         sig
          type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

          val compare :
            ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
            ConstraintType.t) prod, Level.t) prod -> comparison

          val eq_dec :
            ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
            ConstraintType.t) prod, Level.t) prod -> sumbool
         end
       end

      val eq_dec :
        ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
        ConstraintType.t) prod, Level.t) prod -> sumbool

      val lt_dec :
        ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
        ConstraintType.t) prod, Level.t) prod -> sumbool

      val eqb :
        ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
        ConstraintType.t) prod, Level.t) prod -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

            val compare :
              ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
              ConstraintType.t) prod, Level.t) prod -> comparison

            val eq_dec :
              ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
              ConstraintType.t) prod, Level.t) prod -> sumbool
           end

          module TO :
           sig
            type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

            val compare :
              ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
              ConstraintType.t) prod, Level.t) prod -> comparison

            val eq_dec :
              ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
              ConstraintType.t) prod, Level.t) prod -> sumbool
           end
         end

        val eq_dec :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> sumbool

        val lt_dec :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> sumbool

        val eqb :
          ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
          ConstraintType.t) prod, Level.t) prod -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal = ConstraintSet.Raw.coq_R_bal =
    | R_bal_0 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * t
    | R_bal_1 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_2 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_3 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_4 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * t
    | R_bal_5 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_6 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_7 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * 
       t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_bal_8 of t * ((Level.t, ConstraintType.t) prod, Level.t) prod * t

    type coq_R_remove_min = ConstraintSet.Raw.coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * (t, elt) prod * coq_R_remove_min * t * elt

    type coq_R_merge = ConstraintSet.Raw.coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       elt

    type coq_R_concat = ConstraintSet.Raw.coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       elt

    type coq_R_inter = ConstraintSet.Raw.coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       bool * t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       bool * t * tree * coq_R_inter * tree * coq_R_inter

    type coq_R_diff = ConstraintSet.Raw.coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       bool * t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       bool * t * tree * coq_R_diff * tree * coq_R_diff

    type coq_R_union = ConstraintSet.Raw.coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree
       * Int.Z_as_Int.t * tree
       * ((Level.t, ConstraintType.t) prod, Level.t) prod * tree * t * 
       bool * t * tree * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

    val compare :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> comparison

    val eq_dec :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> sumbool
   end

  type elt = ((Level.t, ConstraintType.t) prod, Level.t) prod

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> (t, t) prod

  val eq_dec : t -> t -> sumbool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

module ConstraintSetDecide :
 sig
  module F :
   sig
    val eqb :
      ((Level.t, ConstraintType.t) prod, Level.t) prod -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> bool
   end

  module MSetLogicalFacts :
   sig
   end

  module MSetDecideAuxiliary :
   sig
   end

  module MSetDecideTestCases :
   sig
   end
 end

module ConstraintSetExtraOrdProp :
 sig
  module P :
   sig
    val coq_Exists_dec :
      ConstraintSet.t -> (((Level.t, ConstraintType.t) prod, Level.t) prod ->
      sumbool) -> sumbool
   end

  val above :
    ((Level.t, ConstraintType.t) prod, Level.t) prod -> ConstraintSet.t ->
    bool

  val below :
    ((Level.t, ConstraintType.t) prod, Level.t) prod -> ConstraintSet.t ->
    bool
 end

module ConstraintSetExtraDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a1 -> (Int.Z_as_Int.t -> ConstraintSet.Raw.tree -> 'a1 -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> ConstraintSet.Raw.tree -> 'a1
      -> 'a1) -> ConstraintSet.Raw.tree -> 'a1

    val tree_rec :
      'a1 -> (Int.Z_as_Int.t -> ConstraintSet.Raw.tree -> 'a1 -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> ConstraintSet.Raw.tree -> 'a1
      -> 'a1) -> ConstraintSet.Raw.tree -> 'a1

    val tree_caset_nodep :
      'a1 -> (Int.Z_as_Int.t -> ConstraintSet.Raw.tree -> 'a1 -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> ConstraintSet.Raw.tree -> 'a1
      -> 'a1) -> ConstraintSet.Raw.tree -> 'a1

    val tree_rect_nodep :
      'a1 -> (Int.Z_as_Int.t -> ConstraintSet.Raw.tree -> 'a1 -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> ConstraintSet.Raw.tree -> 'a1
      -> 'a1) -> ConstraintSet.Raw.tree -> 'a1

    val tree_rec_nodep :
      'a1 -> (Int.Z_as_Int.t -> ConstraintSet.Raw.tree -> 'a1 -> ((Level.t,
      ConstraintType.t) prod, Level.t) prod -> ConstraintSet.Raw.tree -> 'a1
      -> 'a1) -> ConstraintSet.Raw.tree -> 'a1

    val lt_tree_dec :
      ((Level.t, ConstraintType.t) prod, Level.t) prod ->
      ConstraintSet.Raw.tree -> sumbool

    val gt_tree_dec :
      ((Level.t, ConstraintType.t) prod, Level.t) prod ->
      ConstraintSet.Raw.tree -> sumbool

    val bst_dec : ConstraintSet.Raw.tree -> sumbool
   end
 end

val is_declared_cstr_levels : LevelSet.t -> UnivConstraint.t -> bool

module Instance :
 sig
  type t = Level.t list

  val empty : t

  val is_empty : t -> bool

  val eqb : t -> t -> bool

  val equal_upto : (Level.t -> Level.t -> bool) -> t -> t -> bool
 end

module UContext :
 sig
  type t = (name list, (Instance.t, ConstraintSet.t) prod) prod

  val make' :
    Instance.t -> ConstraintSet.t -> (Instance.t, ConstraintSet.t) prod

  val make : name list -> (Instance.t, ConstraintSet.t) prod -> t

  val empty : t

  val instance : t -> Instance.t

  val constraints : t -> ConstraintSet.t

  val dest : t -> (name list, (Instance.t, ConstraintSet.t) prod) prod
 end

module AUContext :
 sig
  type t = (name list, ConstraintSet.t) prod

  val make : name list -> ConstraintSet.t -> t

  val repr : t -> UContext.t

  val levels : t -> LevelSet.t

  val inter : t -> t -> t
 end

module ContextSet :
 sig
  type t = (LevelSet.t, ConstraintSet.t) prod

  val levels : t -> LevelSet.t

  val constraints : t -> ConstraintSet.t

  val empty : t

  val is_empty : t -> bool

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val inter : t -> t -> t

  val union : t -> t -> t

  val subsetP : t -> t -> reflect
 end

module Variance :
 sig
  type t =
  | Irrelevant
  | Covariant
  | Invariant

  val t_rect : 'a1 -> 'a1 -> 'a1 -> t -> 'a1

  val t_rec : 'a1 -> 'a1 -> 'a1 -> t -> 'a1

  val coq_NoConfusionPackage_t : t coq_NoConfusionPackage

  val t_eqdec : t -> t -> t dec_eq

  val t_EqDec : t coq_EqDec
 end

type universes_decl =
| Monomorphic_ctx
| Polymorphic_ctx of AUContext.t

val universes_decl_rect : 'a1 -> (AUContext.t -> 'a1) -> universes_decl -> 'a1

val universes_decl_rec : 'a1 -> (AUContext.t -> 'a1) -> universes_decl -> 'a1

val coq_NoConfusionPackage_universes_decl :
  universes_decl coq_NoConfusionPackage

val levels_of_udecl : universes_decl -> LevelSet.t

val constraints_of_udecl : universes_decl -> ConstraintSet.t

val leqb_universe_n_ :
  checker_flags -> (bool -> LevelAlgExpr.t -> LevelAlgExpr.t -> bool) -> bool
  -> Universe.t_ -> Universe.t_ -> bool

val allowed_eliminations_subset :
  allowed_eliminations -> allowed_eliminations -> bool

val fresh_level : Level.t

val fresh_universe : Universe.t

type 'a coq_UnivSubst = Instance.t -> 'a -> 'a

val subst_instance : 'a1 coq_UnivSubst -> Instance.t -> 'a1 -> 'a1

val subst_instance_level : Level.t coq_UnivSubst

val subst_instance_cstr : UnivConstraint.t coq_UnivSubst

val subst_instance_cstrs : ConstraintSet.t coq_UnivSubst

val subst_instance_level_expr : LevelExpr.t coq_UnivSubst

val subst_instance_univ0 : LevelAlgExpr.t coq_UnivSubst

val subst_instance_univ : Universe.t coq_UnivSubst

val subst_instance_instance : Instance.t coq_UnivSubst

val closedu_level : nat -> Level.t -> bool

val closedu_level_expr : nat -> LevelExpr.t -> bool

val closedu_universe_levels : nat -> LevelAlgExpr.t -> bool

val closedu_universe : nat -> Universe.t -> bool

val closedu_instance : nat -> Instance.t -> bool

val string_of_level : Level.t -> String.t

val string_of_level_expr : LevelExpr.t -> String.t

val string_of_sort : Universe.t -> String.t

val string_of_universe_instance : Level.t list -> String.t

type universes_entry =
| Monomorphic_entry of ContextSet.t
| Polymorphic_entry of UContext.t

val universes_entry_rect :
  (ContextSet.t -> 'a1) -> (UContext.t -> 'a1) -> universes_entry -> 'a1

val universes_entry_rec :
  (ContextSet.t -> 'a1) -> (UContext.t -> 'a1) -> universes_entry -> 'a1

val coq_NoConfusionPackage_universes_entry :
  universes_entry coq_NoConfusionPackage

val universes_entry_of_decl : universes_decl -> universes_entry

val polymorphic_instance : universes_decl -> Instance.t

val abstract_instance : universes_decl -> Instance.t

val print_universe_instance : Level.t list -> String.t

val print_lset : LevelSet.t -> String.t

val print_constraint_type : ConstraintType.t_ -> String.t

val print_constraint_set : ConstraintSet.t -> String.t

open Byte
open Classes
open Datatypes
open FMapAVL
open FMapFacts
open List
open MCCompare
open MCString
open MSetAVL
open MSetFacts
open MSetProperties
open PeanoNat
open ReflectEq
open Specif
open Bytestring

type __ = Obj.t

val compare_ident : String.t -> String.t -> comparison

type ident = String.t

type qualid = String.t

type dirpath = ident list

module IdentOT :
 sig
  type t = String.t

  val compare : String.t -> String.t -> comparison

  val reflect_eq_string : t coq_ReflectEq

  val eq_dec : t -> t -> sumbool
 end

module IdentOTOrig :
 sig
  type t = String.t

  val eq_dec : String.t -> String.t -> sumbool

  val compare : String.t -> String.t -> String.t OrderedType.coq_Compare
 end

module IdentSet :
 sig
  module Raw :
   sig
    type elt = String.t

    type tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree * String.t * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : String.t -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : String.t list -> tree -> String.t list

    val elements : tree -> String.t list

    val rev_elements_aux : String.t list -> tree -> String.t list

    val rev_elements : tree -> String.t list

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
      String.t -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> String.t -> tree -> bool

    val subsetr : (tree -> bool) -> String.t -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : String.t -> tree

    val create : t -> String.t -> t -> tree

    val assert_false : t -> String.t -> t -> tree

    val bal : t -> String.t -> t -> tree

    val add : String.t -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> (t, elt) prod

    val merge : tree -> tree -> tree

    val remove : String.t -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : String.t -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> (t, t) prod

    val ltb_tree : String.t -> tree -> bool

    val gtb_tree : String.t -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = String.t

          val compare : String.t -> String.t -> comparison

          val eq_dec : String.t -> String.t -> sumbool
         end

        module TO :
         sig
          type t = String.t

          val compare : String.t -> String.t -> comparison

          val eq_dec : String.t -> String.t -> sumbool
         end
       end

      val eq_dec : String.t -> String.t -> sumbool

      val lt_dec : String.t -> String.t -> sumbool

      val eqb : String.t -> String.t -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = String.t

            val compare : String.t -> String.t -> comparison

            val eq_dec : String.t -> String.t -> sumbool
           end

          module TO :
           sig
            type t = String.t

            val compare : String.t -> String.t -> comparison

            val eq_dec : String.t -> String.t -> sumbool
           end
         end

        val eq_dec : String.t -> String.t -> sumbool

        val lt_dec : String.t -> String.t -> sumbool

        val eqb : String.t -> String.t -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * String.t * t
    | R_bal_1 of t * String.t * t * Int.Z_as_Int.t * tree * String.t * tree
    | R_bal_2 of t * String.t * t * Int.Z_as_Int.t * tree * String.t * tree
    | R_bal_3 of t * String.t * t * Int.Z_as_Int.t * tree * String.t * 
       tree * Int.Z_as_Int.t * tree * String.t * tree
    | R_bal_4 of t * String.t * t
    | R_bal_5 of t * String.t * t * Int.Z_as_Int.t * tree * String.t * tree
    | R_bal_6 of t * String.t * t * Int.Z_as_Int.t * tree * String.t * tree
    | R_bal_7 of t * String.t * t * Int.Z_as_Int.t * tree * String.t * 
       tree * Int.Z_as_Int.t * tree * String.t * tree
    | R_bal_8 of t * String.t * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * String.t
       * tree * (t, elt) prod * coq_R_remove_min * t * elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
       * Int.Z_as_Int.t * tree * String.t * tree * t * elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * String.t * 
       tree * Int.Z_as_Int.t * tree * String.t * tree * t * elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
       * Int.Z_as_Int.t * tree * String.t * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
       * Int.Z_as_Int.t * tree * String.t * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
       * Int.Z_as_Int.t * tree * String.t * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
       * Int.Z_as_Int.t * tree * String.t * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * String.t * tree
       * Int.Z_as_Int.t * tree * String.t * tree * t * bool * t * tree
       * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = String.t

    val compare : String.t -> String.t -> comparison

    val eq_dec : String.t -> String.t -> sumbool
   end

  type elt = String.t

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

module IdentSetFact :
 sig
  val eqb : String.t -> String.t -> bool
 end

module IdentSetOrdProp :
 sig
  module ME :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = String.t

        val compare : String.t -> String.t -> comparison

        val eq_dec : String.t -> String.t -> sumbool
       end

      module TO :
       sig
        type t = String.t

        val compare : String.t -> String.t -> comparison

        val eq_dec : String.t -> String.t -> sumbool
       end
     end

    val eq_dec : String.t -> String.t -> sumbool

    val lt_dec : String.t -> String.t -> sumbool

    val eqb : String.t -> String.t -> bool
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
        val eqb : String.t -> String.t -> bool
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
      val eqb : String.t -> String.t -> bool
     end

    val coq_In_dec : IdentSet.elt -> IdentSet.t -> sumbool

    val of_list : IdentSet.elt list -> IdentSet.t

    val to_list : IdentSet.t -> IdentSet.elt list

    val fold_rec :
      (IdentSet.elt -> 'a1 -> 'a1) -> 'a1 -> IdentSet.t -> (IdentSet.t -> __
      -> 'a2) -> (IdentSet.elt -> 'a1 -> IdentSet.t -> IdentSet.t -> __ -> __
      -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (IdentSet.elt -> 'a1 -> 'a1) -> 'a1 -> IdentSet.t -> (IdentSet.t ->
      IdentSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (IdentSet.elt -> 'a1
      -> IdentSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (IdentSet.elt -> 'a1 -> 'a1) -> 'a1 -> IdentSet.t -> 'a2 ->
      (IdentSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (IdentSet.elt -> 'a1 -> 'a1) -> 'a1 -> (IdentSet.t -> IdentSet.t -> 'a1
      -> __ -> 'a2 -> 'a2) -> 'a2 -> (IdentSet.elt -> 'a1 -> IdentSet.t -> __
      -> 'a2 -> 'a2) -> IdentSet.t -> 'a2

    val fold_rel :
      (IdentSet.elt -> 'a1 -> 'a1) -> (IdentSet.elt -> 'a2 -> 'a2) -> 'a1 ->
      'a2 -> IdentSet.t -> 'a3 -> (IdentSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
      'a3) -> 'a3

    val set_induction :
      (IdentSet.t -> __ -> 'a1) -> (IdentSet.t -> IdentSet.t -> 'a1 ->
      IdentSet.elt -> __ -> __ -> 'a1) -> IdentSet.t -> 'a1

    val set_induction_bis :
      (IdentSet.t -> IdentSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (IdentSet.elt
      -> IdentSet.t -> __ -> 'a1 -> 'a1) -> IdentSet.t -> 'a1

    val cardinal_inv_2 : IdentSet.t -> nat -> IdentSet.elt

    val cardinal_inv_2b : IdentSet.t -> IdentSet.elt
   end

  val gtb : String.t -> String.t -> bool

  val leb : String.t -> String.t -> bool

  val elements_lt : String.t -> IdentSet.t -> String.t list

  val elements_ge : String.t -> IdentSet.t -> String.t list

  val set_induction_max :
    (IdentSet.t -> __ -> 'a1) -> (IdentSet.t -> IdentSet.t -> 'a1 -> String.t
    -> __ -> __ -> 'a1) -> IdentSet.t -> 'a1

  val set_induction_min :
    (IdentSet.t -> __ -> 'a1) -> (IdentSet.t -> IdentSet.t -> 'a1 -> String.t
    -> __ -> __ -> 'a1) -> IdentSet.t -> 'a1
 end

module IdentSetProp :
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb : String.t -> String.t -> bool
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
    val eqb : String.t -> String.t -> bool
   end

  val coq_In_dec : IdentSet.elt -> IdentSet.t -> sumbool

  val of_list : IdentSet.elt list -> IdentSet.t

  val to_list : IdentSet.t -> IdentSet.elt list

  val fold_rec :
    (IdentSet.elt -> 'a1 -> 'a1) -> 'a1 -> IdentSet.t -> (IdentSet.t -> __ ->
    'a2) -> (IdentSet.elt -> 'a1 -> IdentSet.t -> IdentSet.t -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (IdentSet.elt -> 'a1 -> 'a1) -> 'a1 -> IdentSet.t -> (IdentSet.t ->
    IdentSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (IdentSet.elt -> 'a1 ->
    IdentSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_nodep :
    (IdentSet.elt -> 'a1 -> 'a1) -> 'a1 -> IdentSet.t -> 'a2 -> (IdentSet.elt
    -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_weak :
    (IdentSet.elt -> 'a1 -> 'a1) -> 'a1 -> (IdentSet.t -> IdentSet.t -> 'a1
    -> __ -> 'a2 -> 'a2) -> 'a2 -> (IdentSet.elt -> 'a1 -> IdentSet.t -> __
    -> 'a2 -> 'a2) -> IdentSet.t -> 'a2

  val fold_rel :
    (IdentSet.elt -> 'a1 -> 'a1) -> (IdentSet.elt -> 'a2 -> 'a2) -> 'a1 ->
    'a2 -> IdentSet.t -> 'a3 -> (IdentSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
    'a3) -> 'a3

  val set_induction :
    (IdentSet.t -> __ -> 'a1) -> (IdentSet.t -> IdentSet.t -> 'a1 ->
    IdentSet.elt -> __ -> __ -> 'a1) -> IdentSet.t -> 'a1

  val set_induction_bis :
    (IdentSet.t -> IdentSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (IdentSet.elt ->
    IdentSet.t -> __ -> 'a1 -> 'a1) -> IdentSet.t -> 'a1

  val cardinal_inv_2 : IdentSet.t -> nat -> IdentSet.elt

  val cardinal_inv_2b : IdentSet.t -> IdentSet.elt
 end

module IdentSetDecide :
 sig
  module F :
   sig
    val eqb : String.t -> String.t -> bool
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

module IdentSetExtraOrdProp :
 sig
  module P :
   sig
    val coq_Exists_dec : IdentSet.t -> (String.t -> sumbool) -> sumbool
   end

  val above : String.t -> IdentSet.t -> bool

  val below : String.t -> IdentSet.t -> bool
 end

module IdentSetExtraDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a1 -> (Int.Z_as_Int.t -> IdentSet.Raw.tree -> 'a1 -> String.t ->
      IdentSet.Raw.tree -> 'a1 -> 'a1) -> IdentSet.Raw.tree -> 'a1

    val tree_rec :
      'a1 -> (Int.Z_as_Int.t -> IdentSet.Raw.tree -> 'a1 -> String.t ->
      IdentSet.Raw.tree -> 'a1 -> 'a1) -> IdentSet.Raw.tree -> 'a1

    val tree_caset_nodep :
      'a1 -> (Int.Z_as_Int.t -> IdentSet.Raw.tree -> 'a1 -> String.t ->
      IdentSet.Raw.tree -> 'a1 -> 'a1) -> IdentSet.Raw.tree -> 'a1

    val tree_rect_nodep :
      'a1 -> (Int.Z_as_Int.t -> IdentSet.Raw.tree -> 'a1 -> String.t ->
      IdentSet.Raw.tree -> 'a1 -> 'a1) -> IdentSet.Raw.tree -> 'a1

    val tree_rec_nodep :
      'a1 -> (Int.Z_as_Int.t -> IdentSet.Raw.tree -> 'a1 -> String.t ->
      IdentSet.Raw.tree -> 'a1 -> 'a1) -> IdentSet.Raw.tree -> 'a1

    val lt_tree_dec : String.t -> IdentSet.Raw.tree -> sumbool

    val gt_tree_dec : String.t -> IdentSet.Raw.tree -> sumbool

    val bst_dec : IdentSet.Raw.tree -> sumbool
   end
 end

module IdentMap :
 sig
  module E :
   sig
    type t = String.t

    val compare : String.t -> String.t -> String.t OrderedType.coq_Compare

    val eq_dec : String.t -> String.t -> sumbool
   end

  module Raw :
   sig
    type key = String.t

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

    val mem : String.t -> 'a1 tree -> bool

    val find : String.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : String.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : String.t -> 'a1 tree -> 'a1 triple

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
      ('a1 -> 'a1 -> bool) -> String.t -> 'a1 -> ('a1 enumeration -> bool) ->
      'a1 enumeration -> bool

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
          type t = String.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : String.t -> String.t -> sumbool

        val lt_dec : String.t -> String.t -> sumbool

        val eqb : String.t -> String.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = String.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : String.t -> String.t -> sumbool

          val lt_dec : String.t -> String.t -> sumbool

          val eqb : String.t -> String.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = String.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : String.t -> String.t -> sumbool

          val lt_dec : String.t -> String.t -> sumbool

          val eqb : String.t -> String.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = String.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : String.t -> String.t -> sumbool

            val lt_dec : String.t -> String.t -> sumbool

            val eqb : String.t -> String.t -> bool
           end
         end

        type key = String.t

        type 'elt t = (String.t, 'elt) prod list

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
        String.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ ->
        __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
        coq_R_mem -> 'a2

      val coq_R_mem_rec :
        String.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
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
        String.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 option
        -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
        __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree
        -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        String.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
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
        String.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ ->
        __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        String.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
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
        String.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple
        -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        String.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
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

  type key = String.t

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

module IdentMapFact :
 sig
  module F :
   sig
    val eqb : String.t -> String.t -> bool

    val coq_In_dec : 'a1 IdentMap.t -> IdentMap.key -> sumbool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3

  val of_list : (IdentMap.key, 'a1) prod list -> 'a1 IdentMap.t

  val to_list : 'a1 IdentMap.t -> (IdentMap.key, 'a1) prod list

  val fold_rec :
    (IdentMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 IdentMap.t -> ('a1
    IdentMap.t -> __ -> 'a3) -> (IdentMap.key -> 'a1 -> 'a2 -> 'a1 IdentMap.t
    -> 'a1 IdentMap.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_bis :
    (IdentMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 IdentMap.t -> ('a1
    IdentMap.t -> 'a1 IdentMap.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
    (IdentMap.key -> 'a1 -> 'a2 -> 'a1 IdentMap.t -> __ -> __ -> 'a3 -> 'a3)
    -> 'a3

  val fold_rec_nodep :
    (IdentMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 IdentMap.t -> 'a3 ->
    (IdentMap.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (IdentMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 IdentMap.t -> 'a1
    IdentMap.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (IdentMap.key -> 'a1 ->
    'a2 -> 'a1 IdentMap.t -> __ -> 'a3 -> 'a3) -> 'a1 IdentMap.t -> 'a3

  val fold_rel :
    (IdentMap.key -> 'a1 -> 'a2 -> 'a2) -> (IdentMap.key -> 'a1 -> 'a3 ->
    'a3) -> 'a2 -> 'a3 -> 'a1 IdentMap.t -> 'a4 -> (IdentMap.key -> 'a1 ->
    'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

  val map_induction :
    ('a1 IdentMap.t -> __ -> 'a2) -> ('a1 IdentMap.t -> 'a1 IdentMap.t -> 'a2
    -> IdentMap.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 IdentMap.t -> 'a2

  val map_induction_bis :
    ('a1 IdentMap.t -> 'a1 IdentMap.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
    (IdentMap.key -> 'a1 -> 'a1 IdentMap.t -> __ -> 'a2 -> 'a2) -> 'a1
    IdentMap.t -> 'a2

  val cardinal_inv_2 : 'a1 IdentMap.t -> nat -> (IdentMap.key, 'a1) prod

  val cardinal_inv_2b : 'a1 IdentMap.t -> (IdentMap.key, 'a1) prod

  val filter :
    (IdentMap.key -> 'a1 -> bool) -> 'a1 IdentMap.t -> 'a1 IdentMap.t

  val for_all : (IdentMap.key -> 'a1 -> bool) -> 'a1 IdentMap.t -> bool

  val exists_ : (IdentMap.key -> 'a1 -> bool) -> 'a1 IdentMap.t -> bool

  val partition :
    (IdentMap.key -> 'a1 -> bool) -> 'a1 IdentMap.t -> ('a1 IdentMap.t, 'a1
    IdentMap.t) prod

  val update : 'a1 IdentMap.t -> 'a1 IdentMap.t -> 'a1 IdentMap.t

  val restrict : 'a1 IdentMap.t -> 'a1 IdentMap.t -> 'a1 IdentMap.t

  val diff : 'a1 IdentMap.t -> 'a1 IdentMap.t -> 'a1 IdentMap.t

  val coq_Partition_In :
    'a1 IdentMap.t -> 'a1 IdentMap.t -> 'a1 IdentMap.t -> IdentMap.key ->
    sumbool

  val update_dec :
    'a1 IdentMap.t -> 'a1 IdentMap.t -> IdentMap.key -> 'a1 -> sumbool

  val filter_dom : (IdentMap.key -> bool) -> 'a1 IdentMap.t -> 'a1 IdentMap.t

  val filter_range : ('a1 -> bool) -> 'a1 IdentMap.t -> 'a1 IdentMap.t

  val for_all_dom : (IdentMap.key -> bool) -> 'a1 IdentMap.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 IdentMap.t -> bool

  val exists_dom : (IdentMap.key -> bool) -> 'a1 IdentMap.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 IdentMap.t -> bool

  val partition_dom :
    (IdentMap.key -> bool) -> 'a1 IdentMap.t -> ('a1 IdentMap.t, 'a1
    IdentMap.t) prod

  val partition_range :
    ('a1 -> bool) -> 'a1 IdentMap.t -> ('a1 IdentMap.t, 'a1 IdentMap.t) prod
 end

module IdentMapExtraFact :
 sig
 end

module IdentMapDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a2 -> ('a1 IdentMap.Raw.tree -> 'a2 -> IdentMap.Raw.key -> 'a1 -> 'a1
      IdentMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      IdentMap.Raw.tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 IdentMap.Raw.tree -> 'a2 -> IdentMap.Raw.key -> 'a1 -> 'a1
      IdentMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      IdentMap.Raw.tree -> 'a2

    val tree_caset_nodep :
      'a2 -> ('a1 IdentMap.Raw.tree -> 'a2 -> IdentMap.Raw.key -> 'a1 -> 'a1
      IdentMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      IdentMap.Raw.tree -> 'a2

    val tree_rect_nodep :
      'a2 -> ('a1 IdentMap.Raw.tree -> 'a2 -> IdentMap.Raw.key -> 'a1 -> 'a1
      IdentMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      IdentMap.Raw.tree -> 'a2

    val tree_rec_nodep :
      'a2 -> ('a1 IdentMap.Raw.tree -> 'a2 -> IdentMap.Raw.key -> 'a1 -> 'a1
      IdentMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      IdentMap.Raw.tree -> 'a2

    val lt_tree_dec : String.t -> 'a1 IdentMap.Raw.tree -> sumbool

    val gt_tree_dec : String.t -> 'a1 IdentMap.Raw.tree -> sumbool

    val bst_dec : 'a1 IdentMap.Raw.tree -> sumbool
   end
 end

module DirPathOT :
 sig
  type t = String.t list

  val compare : t -> t -> comparison

  val lt__sig_pack : t -> t -> (t * t) * __

  val lt__Signature : t -> t -> (t * t) * __

  val eqb : t -> t -> bool

  val eqb_dec : t -> t -> sumbool

  val eq_dec : t coq_EqDec
 end

module DirPathOTOrig :
 sig
  type t = String.t list

  val eq_dec : String.t list -> String.t list -> sumbool

  val compare :
    String.t list -> String.t list -> String.t list OrderedType.coq_Compare
 end

module DirPathSet :
 sig
  module Raw :
   sig
    type elt = String.t list

    type tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree * String.t list * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : String.t list -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : String.t list list -> tree -> String.t list list

    val elements : tree -> String.t list list

    val rev_elements_aux : String.t list list -> tree -> String.t list list

    val rev_elements : tree -> String.t list list

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
      String.t list -> (enumeration -> comparison) -> enumeration ->
      comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> String.t list -> tree -> bool

    val subsetr : (tree -> bool) -> String.t list -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : String.t list -> tree

    val create : t -> String.t list -> t -> tree

    val assert_false : t -> String.t list -> t -> tree

    val bal : t -> String.t list -> t -> tree

    val add : String.t list -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> (t, elt) prod

    val merge : tree -> tree -> tree

    val remove : String.t list -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : String.t list -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> (t, t) prod

    val ltb_tree : String.t list -> tree -> bool

    val gtb_tree : String.t list -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = String.t list

          val compare : String.t list -> String.t list -> comparison

          val eq_dec : String.t list -> String.t list -> sumbool
         end

        module TO :
         sig
          type t = String.t list

          val compare : String.t list -> String.t list -> comparison

          val eq_dec : String.t list -> String.t list -> sumbool
         end
       end

      val eq_dec : String.t list -> String.t list -> sumbool

      val lt_dec : String.t list -> String.t list -> sumbool

      val eqb : String.t list -> String.t list -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = String.t list

            val compare : String.t list -> String.t list -> comparison

            val eq_dec : String.t list -> String.t list -> sumbool
           end

          module TO :
           sig
            type t = String.t list

            val compare : String.t list -> String.t list -> comparison

            val eq_dec : String.t list -> String.t list -> sumbool
           end
         end

        val eq_dec : String.t list -> String.t list -> sumbool

        val lt_dec : String.t list -> String.t list -> sumbool

        val eqb : String.t list -> String.t list -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * String.t list * t
    | R_bal_1 of t * String.t list * t * Int.Z_as_Int.t * tree
       * String.t list * tree
    | R_bal_2 of t * String.t list * t * Int.Z_as_Int.t * tree
       * String.t list * tree
    | R_bal_3 of t * String.t list * t * Int.Z_as_Int.t * tree
       * String.t list * tree * Int.Z_as_Int.t * tree * String.t list * 
       tree
    | R_bal_4 of t * String.t list * t
    | R_bal_5 of t * String.t list * t * Int.Z_as_Int.t * tree
       * String.t list * tree
    | R_bal_6 of t * String.t list * t * Int.Z_as_Int.t * tree
       * String.t list * tree
    | R_bal_7 of t * String.t list * t * Int.Z_as_Int.t * tree
       * String.t list * tree * Int.Z_as_Int.t * tree * String.t list * 
       tree
    | R_bal_8 of t * String.t list * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
       * String.t list * tree * (t, elt) prod * coq_R_remove_min * t * 
       elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * String.t list * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * String.t list * 
       tree * Int.Z_as_Int.t * tree * String.t list * tree * t * elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * String.t list * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * String.t list
       * tree * Int.Z_as_Int.t * tree * String.t list * tree * t * elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * String.t list * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * String.t list * 
       tree * Int.Z_as_Int.t * tree * String.t list * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * String.t list * 
       tree * Int.Z_as_Int.t * tree * String.t list * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * String.t list * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * String.t list * 
       tree * Int.Z_as_Int.t * tree * String.t list * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * String.t list * 
       tree * Int.Z_as_Int.t * tree * String.t list * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * String.t list * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * String.t list * 
       tree * Int.Z_as_Int.t * tree * String.t list * tree * t * bool * 
       t * tree * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = String.t list

    val compare : String.t list -> String.t list -> comparison

    val eq_dec : String.t list -> String.t list -> sumbool
   end

  type elt = String.t list

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

module DirPathSetFact :
 sig
  val eqb : String.t list -> String.t list -> bool
 end

module DirPathSetOrdProp :
 sig
  module ME :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = String.t list

        val compare : String.t list -> String.t list -> comparison

        val eq_dec : String.t list -> String.t list -> sumbool
       end

      module TO :
       sig
        type t = String.t list

        val compare : String.t list -> String.t list -> comparison

        val eq_dec : String.t list -> String.t list -> sumbool
       end
     end

    val eq_dec : String.t list -> String.t list -> sumbool

    val lt_dec : String.t list -> String.t list -> sumbool

    val eqb : String.t list -> String.t list -> bool
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
        val eqb : String.t list -> String.t list -> bool
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
      val eqb : String.t list -> String.t list -> bool
     end

    val coq_In_dec : DirPathSet.elt -> DirPathSet.t -> sumbool

    val of_list : DirPathSet.elt list -> DirPathSet.t

    val to_list : DirPathSet.t -> DirPathSet.elt list

    val fold_rec :
      (DirPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> DirPathSet.t -> (DirPathSet.t
      -> __ -> 'a2) -> (DirPathSet.elt -> 'a1 -> DirPathSet.t -> DirPathSet.t
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (DirPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> DirPathSet.t -> (DirPathSet.t
      -> DirPathSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (DirPathSet.elt
      -> 'a1 -> DirPathSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (DirPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> DirPathSet.t -> 'a2 ->
      (DirPathSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (DirPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> (DirPathSet.t -> DirPathSet.t
      -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (DirPathSet.elt -> 'a1 ->
      DirPathSet.t -> __ -> 'a2 -> 'a2) -> DirPathSet.t -> 'a2

    val fold_rel :
      (DirPathSet.elt -> 'a1 -> 'a1) -> (DirPathSet.elt -> 'a2 -> 'a2) -> 'a1
      -> 'a2 -> DirPathSet.t -> 'a3 -> (DirPathSet.elt -> 'a1 -> 'a2 -> __ ->
      'a3 -> 'a3) -> 'a3

    val set_induction :
      (DirPathSet.t -> __ -> 'a1) -> (DirPathSet.t -> DirPathSet.t -> 'a1 ->
      DirPathSet.elt -> __ -> __ -> 'a1) -> DirPathSet.t -> 'a1

    val set_induction_bis :
      (DirPathSet.t -> DirPathSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
      (DirPathSet.elt -> DirPathSet.t -> __ -> 'a1 -> 'a1) -> DirPathSet.t ->
      'a1

    val cardinal_inv_2 : DirPathSet.t -> nat -> DirPathSet.elt

    val cardinal_inv_2b : DirPathSet.t -> DirPathSet.elt
   end

  val gtb : String.t list -> String.t list -> bool

  val leb : String.t list -> String.t list -> bool

  val elements_lt : String.t list -> DirPathSet.t -> String.t list list

  val elements_ge : String.t list -> DirPathSet.t -> String.t list list

  val set_induction_max :
    (DirPathSet.t -> __ -> 'a1) -> (DirPathSet.t -> DirPathSet.t -> 'a1 ->
    String.t list -> __ -> __ -> 'a1) -> DirPathSet.t -> 'a1

  val set_induction_min :
    (DirPathSet.t -> __ -> 'a1) -> (DirPathSet.t -> DirPathSet.t -> 'a1 ->
    String.t list -> __ -> __ -> 'a1) -> DirPathSet.t -> 'a1
 end

module DirPathSetProp :
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb : String.t list -> String.t list -> bool
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
    val eqb : String.t list -> String.t list -> bool
   end

  val coq_In_dec : DirPathSet.elt -> DirPathSet.t -> sumbool

  val of_list : DirPathSet.elt list -> DirPathSet.t

  val to_list : DirPathSet.t -> DirPathSet.elt list

  val fold_rec :
    (DirPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> DirPathSet.t -> (DirPathSet.t ->
    __ -> 'a2) -> (DirPathSet.elt -> 'a1 -> DirPathSet.t -> DirPathSet.t ->
    __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (DirPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> DirPathSet.t -> (DirPathSet.t ->
    DirPathSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (DirPathSet.elt -> 'a1
    -> DirPathSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_nodep :
    (DirPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> DirPathSet.t -> 'a2 ->
    (DirPathSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_weak :
    (DirPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> (DirPathSet.t -> DirPathSet.t ->
    'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (DirPathSet.elt -> 'a1 -> DirPathSet.t
    -> __ -> 'a2 -> 'a2) -> DirPathSet.t -> 'a2

  val fold_rel :
    (DirPathSet.elt -> 'a1 -> 'a1) -> (DirPathSet.elt -> 'a2 -> 'a2) -> 'a1
    -> 'a2 -> DirPathSet.t -> 'a3 -> (DirPathSet.elt -> 'a1 -> 'a2 -> __ ->
    'a3 -> 'a3) -> 'a3

  val set_induction :
    (DirPathSet.t -> __ -> 'a1) -> (DirPathSet.t -> DirPathSet.t -> 'a1 ->
    DirPathSet.elt -> __ -> __ -> 'a1) -> DirPathSet.t -> 'a1

  val set_induction_bis :
    (DirPathSet.t -> DirPathSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
    (DirPathSet.elt -> DirPathSet.t -> __ -> 'a1 -> 'a1) -> DirPathSet.t ->
    'a1

  val cardinal_inv_2 : DirPathSet.t -> nat -> DirPathSet.elt

  val cardinal_inv_2b : DirPathSet.t -> DirPathSet.elt
 end

module DirPathSetDecide :
 sig
  module F :
   sig
    val eqb : String.t list -> String.t list -> bool
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

module DirPathSetExtraOrdProp :
 sig
  module P :
   sig
    val coq_Exists_dec : DirPathSet.t -> (String.t list -> sumbool) -> sumbool
   end

  val above : String.t list -> DirPathSet.t -> bool

  val below : String.t list -> DirPathSet.t -> bool
 end

module DirPathSetExtraDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a1 -> (Int.Z_as_Int.t -> DirPathSet.Raw.tree -> 'a1 -> String.t list
      -> DirPathSet.Raw.tree -> 'a1 -> 'a1) -> DirPathSet.Raw.tree -> 'a1

    val tree_rec :
      'a1 -> (Int.Z_as_Int.t -> DirPathSet.Raw.tree -> 'a1 -> String.t list
      -> DirPathSet.Raw.tree -> 'a1 -> 'a1) -> DirPathSet.Raw.tree -> 'a1

    val tree_caset_nodep :
      'a1 -> (Int.Z_as_Int.t -> DirPathSet.Raw.tree -> 'a1 -> String.t list
      -> DirPathSet.Raw.tree -> 'a1 -> 'a1) -> DirPathSet.Raw.tree -> 'a1

    val tree_rect_nodep :
      'a1 -> (Int.Z_as_Int.t -> DirPathSet.Raw.tree -> 'a1 -> String.t list
      -> DirPathSet.Raw.tree -> 'a1 -> 'a1) -> DirPathSet.Raw.tree -> 'a1

    val tree_rec_nodep :
      'a1 -> (Int.Z_as_Int.t -> DirPathSet.Raw.tree -> 'a1 -> String.t list
      -> DirPathSet.Raw.tree -> 'a1 -> 'a1) -> DirPathSet.Raw.tree -> 'a1

    val lt_tree_dec : String.t list -> DirPathSet.Raw.tree -> sumbool

    val gt_tree_dec : String.t list -> DirPathSet.Raw.tree -> sumbool

    val bst_dec : DirPathSet.Raw.tree -> sumbool
   end
 end

module DirPathMap :
 sig
  module E :
   sig
    type t = String.t list

    val compare :
      String.t list -> String.t list -> String.t list OrderedType.coq_Compare

    val eq_dec : String.t list -> String.t list -> sumbool
   end

  module Raw :
   sig
    type key = String.t list

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

    val mem : String.t list -> 'a1 tree -> bool

    val find : String.t list -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : String.t list -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : String.t list -> 'a1 tree -> 'a1 triple

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
      ('a1 -> 'a1 -> bool) -> String.t list -> 'a1 -> ('a1 enumeration ->
      bool) -> 'a1 enumeration -> bool

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
          type t = String.t list
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : String.t list -> String.t list -> sumbool

        val lt_dec : String.t list -> String.t list -> sumbool

        val eqb : String.t list -> String.t list -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = String.t list
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : String.t list -> String.t list -> sumbool

          val lt_dec : String.t list -> String.t list -> sumbool

          val eqb : String.t list -> String.t list -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = String.t list
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : String.t list -> String.t list -> sumbool

          val lt_dec : String.t list -> String.t list -> sumbool

          val eqb : String.t list -> String.t list -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = String.t list
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : String.t list -> String.t list -> sumbool

            val lt_dec : String.t list -> String.t list -> sumbool

            val eqb : String.t list -> String.t list -> bool
           end
         end

        type key = String.t list

        type 'elt t = (String.t list, 'elt) prod list

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
        String.t list -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> bool ->
        'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
        -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool ->
        'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        String.t list -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> bool ->
        'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
        -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool ->
        'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        String.t list -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        String.t list -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

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
        String.t list -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        String.t list -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

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
        String.t list -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
        -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        String.t list -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
        -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
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

  type key = String.t list

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

module DirPathMapFact :
 sig
  module F :
   sig
    val eqb : String.t list -> String.t list -> bool

    val coq_In_dec : 'a1 DirPathMap.t -> DirPathMap.key -> sumbool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3

  val of_list : (DirPathMap.key, 'a1) prod list -> 'a1 DirPathMap.t

  val to_list : 'a1 DirPathMap.t -> (DirPathMap.key, 'a1) prod list

  val fold_rec :
    (DirPathMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 DirPathMap.t -> ('a1
    DirPathMap.t -> __ -> 'a3) -> (DirPathMap.key -> 'a1 -> 'a2 -> 'a1
    DirPathMap.t -> 'a1 DirPathMap.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_bis :
    (DirPathMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 DirPathMap.t -> ('a1
    DirPathMap.t -> 'a1 DirPathMap.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
    (DirPathMap.key -> 'a1 -> 'a2 -> 'a1 DirPathMap.t -> __ -> __ -> 'a3 ->
    'a3) -> 'a3

  val fold_rec_nodep :
    (DirPathMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 DirPathMap.t -> 'a3
    -> (DirPathMap.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (DirPathMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 DirPathMap.t -> 'a1
    DirPathMap.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (DirPathMap.key -> 'a1
    -> 'a2 -> 'a1 DirPathMap.t -> __ -> 'a3 -> 'a3) -> 'a1 DirPathMap.t -> 'a3

  val fold_rel :
    (DirPathMap.key -> 'a1 -> 'a2 -> 'a2) -> (DirPathMap.key -> 'a1 -> 'a3 ->
    'a3) -> 'a2 -> 'a3 -> 'a1 DirPathMap.t -> 'a4 -> (DirPathMap.key -> 'a1
    -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

  val map_induction :
    ('a1 DirPathMap.t -> __ -> 'a2) -> ('a1 DirPathMap.t -> 'a1 DirPathMap.t
    -> 'a2 -> DirPathMap.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 DirPathMap.t
    -> 'a2

  val map_induction_bis :
    ('a1 DirPathMap.t -> 'a1 DirPathMap.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
    (DirPathMap.key -> 'a1 -> 'a1 DirPathMap.t -> __ -> 'a2 -> 'a2) -> 'a1
    DirPathMap.t -> 'a2

  val cardinal_inv_2 : 'a1 DirPathMap.t -> nat -> (DirPathMap.key, 'a1) prod

  val cardinal_inv_2b : 'a1 DirPathMap.t -> (DirPathMap.key, 'a1) prod

  val filter :
    (DirPathMap.key -> 'a1 -> bool) -> 'a1 DirPathMap.t -> 'a1 DirPathMap.t

  val for_all : (DirPathMap.key -> 'a1 -> bool) -> 'a1 DirPathMap.t -> bool

  val exists_ : (DirPathMap.key -> 'a1 -> bool) -> 'a1 DirPathMap.t -> bool

  val partition :
    (DirPathMap.key -> 'a1 -> bool) -> 'a1 DirPathMap.t -> ('a1 DirPathMap.t,
    'a1 DirPathMap.t) prod

  val update : 'a1 DirPathMap.t -> 'a1 DirPathMap.t -> 'a1 DirPathMap.t

  val restrict : 'a1 DirPathMap.t -> 'a1 DirPathMap.t -> 'a1 DirPathMap.t

  val diff : 'a1 DirPathMap.t -> 'a1 DirPathMap.t -> 'a1 DirPathMap.t

  val coq_Partition_In :
    'a1 DirPathMap.t -> 'a1 DirPathMap.t -> 'a1 DirPathMap.t ->
    DirPathMap.key -> sumbool

  val update_dec :
    'a1 DirPathMap.t -> 'a1 DirPathMap.t -> DirPathMap.key -> 'a1 -> sumbool

  val filter_dom :
    (DirPathMap.key -> bool) -> 'a1 DirPathMap.t -> 'a1 DirPathMap.t

  val filter_range : ('a1 -> bool) -> 'a1 DirPathMap.t -> 'a1 DirPathMap.t

  val for_all_dom : (DirPathMap.key -> bool) -> 'a1 DirPathMap.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 DirPathMap.t -> bool

  val exists_dom : (DirPathMap.key -> bool) -> 'a1 DirPathMap.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 DirPathMap.t -> bool

  val partition_dom :
    (DirPathMap.key -> bool) -> 'a1 DirPathMap.t -> ('a1 DirPathMap.t, 'a1
    DirPathMap.t) prod

  val partition_range :
    ('a1 -> bool) -> 'a1 DirPathMap.t -> ('a1 DirPathMap.t, 'a1 DirPathMap.t)
    prod
 end

module DirPathMapExtraFact :
 sig
 end

module DirPathMapDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a2 -> ('a1 DirPathMap.Raw.tree -> 'a2 -> DirPathMap.Raw.key -> 'a1 ->
      'a1 DirPathMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      DirPathMap.Raw.tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 DirPathMap.Raw.tree -> 'a2 -> DirPathMap.Raw.key -> 'a1 ->
      'a1 DirPathMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      DirPathMap.Raw.tree -> 'a2

    val tree_caset_nodep :
      'a2 -> ('a1 DirPathMap.Raw.tree -> 'a2 -> DirPathMap.Raw.key -> 'a1 ->
      'a1 DirPathMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      DirPathMap.Raw.tree -> 'a2

    val tree_rect_nodep :
      'a2 -> ('a1 DirPathMap.Raw.tree -> 'a2 -> DirPathMap.Raw.key -> 'a1 ->
      'a1 DirPathMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      DirPathMap.Raw.tree -> 'a2

    val tree_rec_nodep :
      'a2 -> ('a1 DirPathMap.Raw.tree -> 'a2 -> DirPathMap.Raw.key -> 'a1 ->
      'a1 DirPathMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      DirPathMap.Raw.tree -> 'a2

    val lt_tree_dec : String.t list -> 'a1 DirPathMap.Raw.tree -> sumbool

    val gt_tree_dec : String.t list -> 'a1 DirPathMap.Raw.tree -> sumbool

    val bst_dec : 'a1 DirPathMap.Raw.tree -> sumbool
   end
 end

val dirpath_eqdec : dirpath coq_EqDec

val string_of_dirpath : dirpath -> String.t

type modpath =
| MPfile of dirpath
| MPbound of dirpath * ident * nat
| MPdot of modpath * ident

val modpath_rect :
  (dirpath -> 'a1) -> (dirpath -> ident -> nat -> 'a1) -> (modpath -> 'a1 ->
  ident -> 'a1) -> modpath -> 'a1

val modpath_rec :
  (dirpath -> 'a1) -> (dirpath -> ident -> nat -> 'a1) -> (modpath -> 'a1 ->
  ident -> 'a1) -> modpath -> 'a1

val coq_NoConfusionPackage_modpath : modpath coq_NoConfusionPackage

val string_of_modpath : modpath -> String.t

type kername = (modpath, ident) prod

val string_of_kername : kername -> String.t

module ModPathComp :
 sig
  type t = modpath

  val mpbound_compare :
    DirPathOT.t -> String.t -> nat -> DirPathOT.t -> String.t -> nat ->
    comparison

  val compare : modpath -> modpath -> comparison
 end

module ModPathOT :
 sig
  type t = ModPathComp.t

  val compare :
    ModPathComp.t -> ModPathComp.t -> ModPathComp.t OrderedType.coq_Compare

  val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool
 end

module ModPathOTNew :
 sig
  type t = ModPathComp.t

  val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool

  val compare : ModPathComp.t -> ModPathComp.t -> comparison
 end

module ModPathSet :
 sig
  module Raw :
   sig
    type elt = ModPathComp.t

    type tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree * ModPathComp.t * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : ModPathComp.t -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : ModPathComp.t list -> tree -> ModPathComp.t list

    val elements : tree -> ModPathComp.t list

    val rev_elements_aux : ModPathComp.t list -> tree -> ModPathComp.t list

    val rev_elements : tree -> ModPathComp.t list

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
      ModPathComp.t -> (enumeration -> comparison) -> enumeration ->
      comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> ModPathComp.t -> tree -> bool

    val subsetr : (tree -> bool) -> ModPathComp.t -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : ModPathComp.t -> tree

    val create : t -> ModPathComp.t -> t -> tree

    val assert_false : t -> ModPathComp.t -> t -> tree

    val bal : t -> ModPathComp.t -> t -> tree

    val add : ModPathComp.t -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> (t, elt) prod

    val merge : tree -> tree -> tree

    val remove : ModPathComp.t -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : ModPathComp.t -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> (t, t) prod

    val ltb_tree : ModPathComp.t -> tree -> bool

    val gtb_tree : ModPathComp.t -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = ModPathComp.t

          val compare : ModPathComp.t -> ModPathComp.t -> comparison

          val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool
         end

        module TO :
         sig
          type t = ModPathComp.t

          val compare : ModPathComp.t -> ModPathComp.t -> comparison

          val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool
         end
       end

      val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool

      val lt_dec : ModPathComp.t -> ModPathComp.t -> sumbool

      val eqb : ModPathComp.t -> ModPathComp.t -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = ModPathComp.t

            val compare : ModPathComp.t -> ModPathComp.t -> comparison

            val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool
           end

          module TO :
           sig
            type t = ModPathComp.t

            val compare : ModPathComp.t -> ModPathComp.t -> comparison

            val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool
           end
         end

        val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool

        val lt_dec : ModPathComp.t -> ModPathComp.t -> sumbool

        val eqb : ModPathComp.t -> ModPathComp.t -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * ModPathComp.t * t
    | R_bal_1 of t * ModPathComp.t * t * Int.Z_as_Int.t * tree
       * ModPathComp.t * tree
    | R_bal_2 of t * ModPathComp.t * t * Int.Z_as_Int.t * tree
       * ModPathComp.t * tree
    | R_bal_3 of t * ModPathComp.t * t * Int.Z_as_Int.t * tree
       * ModPathComp.t * tree * Int.Z_as_Int.t * tree * ModPathComp.t * 
       tree
    | R_bal_4 of t * ModPathComp.t * t
    | R_bal_5 of t * ModPathComp.t * t * Int.Z_as_Int.t * tree
       * ModPathComp.t * tree
    | R_bal_6 of t * ModPathComp.t * t * Int.Z_as_Int.t * tree
       * ModPathComp.t * tree
    | R_bal_7 of t * ModPathComp.t * t * Int.Z_as_Int.t * tree
       * ModPathComp.t * tree * Int.Z_as_Int.t * tree * ModPathComp.t * 
       tree
    | R_bal_8 of t * ModPathComp.t * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
       * ModPathComp.t * tree * (t, elt) prod * coq_R_remove_min * t * 
       elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * 
       tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree * t * elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t
       * tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree * t * elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * 
       tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * 
       tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree * t * bool * 
       t * tree * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * 
       tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * 
       tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree * t * bool * 
       t * tree * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * ModPathComp.t * 
       tree * Int.Z_as_Int.t * tree * ModPathComp.t * tree * t * bool * 
       t * tree * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = ModPathComp.t

    val compare : ModPathComp.t -> ModPathComp.t -> comparison

    val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool
   end

  type elt = ModPathComp.t

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

module ModPathSetFact :
 sig
  val eqb : ModPathComp.t -> ModPathComp.t -> bool
 end

module ModPathSetOrdProp :
 sig
  module ME :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = ModPathComp.t

        val compare : ModPathComp.t -> ModPathComp.t -> comparison

        val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool
       end

      module TO :
       sig
        type t = ModPathComp.t

        val compare : ModPathComp.t -> ModPathComp.t -> comparison

        val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool
       end
     end

    val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool

    val lt_dec : ModPathComp.t -> ModPathComp.t -> sumbool

    val eqb : ModPathComp.t -> ModPathComp.t -> bool
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
        val eqb : ModPathComp.t -> ModPathComp.t -> bool
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
      val eqb : ModPathComp.t -> ModPathComp.t -> bool
     end

    val coq_In_dec : ModPathSet.elt -> ModPathSet.t -> sumbool

    val of_list : ModPathSet.elt list -> ModPathSet.t

    val to_list : ModPathSet.t -> ModPathSet.elt list

    val fold_rec :
      (ModPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> ModPathSet.t -> (ModPathSet.t
      -> __ -> 'a2) -> (ModPathSet.elt -> 'a1 -> ModPathSet.t -> ModPathSet.t
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (ModPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> ModPathSet.t -> (ModPathSet.t
      -> ModPathSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (ModPathSet.elt
      -> 'a1 -> ModPathSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (ModPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> ModPathSet.t -> 'a2 ->
      (ModPathSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (ModPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> (ModPathSet.t -> ModPathSet.t
      -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (ModPathSet.elt -> 'a1 ->
      ModPathSet.t -> __ -> 'a2 -> 'a2) -> ModPathSet.t -> 'a2

    val fold_rel :
      (ModPathSet.elt -> 'a1 -> 'a1) -> (ModPathSet.elt -> 'a2 -> 'a2) -> 'a1
      -> 'a2 -> ModPathSet.t -> 'a3 -> (ModPathSet.elt -> 'a1 -> 'a2 -> __ ->
      'a3 -> 'a3) -> 'a3

    val set_induction :
      (ModPathSet.t -> __ -> 'a1) -> (ModPathSet.t -> ModPathSet.t -> 'a1 ->
      ModPathSet.elt -> __ -> __ -> 'a1) -> ModPathSet.t -> 'a1

    val set_induction_bis :
      (ModPathSet.t -> ModPathSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
      (ModPathSet.elt -> ModPathSet.t -> __ -> 'a1 -> 'a1) -> ModPathSet.t ->
      'a1

    val cardinal_inv_2 : ModPathSet.t -> nat -> ModPathSet.elt

    val cardinal_inv_2b : ModPathSet.t -> ModPathSet.elt
   end

  val gtb : ModPathComp.t -> ModPathComp.t -> bool

  val leb : ModPathComp.t -> ModPathComp.t -> bool

  val elements_lt : ModPathComp.t -> ModPathSet.t -> ModPathComp.t list

  val elements_ge : ModPathComp.t -> ModPathSet.t -> ModPathComp.t list

  val set_induction_max :
    (ModPathSet.t -> __ -> 'a1) -> (ModPathSet.t -> ModPathSet.t -> 'a1 ->
    ModPathComp.t -> __ -> __ -> 'a1) -> ModPathSet.t -> 'a1

  val set_induction_min :
    (ModPathSet.t -> __ -> 'a1) -> (ModPathSet.t -> ModPathSet.t -> 'a1 ->
    ModPathComp.t -> __ -> __ -> 'a1) -> ModPathSet.t -> 'a1
 end

module ModPathSetProp :
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb : ModPathComp.t -> ModPathComp.t -> bool
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
    val eqb : ModPathComp.t -> ModPathComp.t -> bool
   end

  val coq_In_dec : ModPathSet.elt -> ModPathSet.t -> sumbool

  val of_list : ModPathSet.elt list -> ModPathSet.t

  val to_list : ModPathSet.t -> ModPathSet.elt list

  val fold_rec :
    (ModPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> ModPathSet.t -> (ModPathSet.t ->
    __ -> 'a2) -> (ModPathSet.elt -> 'a1 -> ModPathSet.t -> ModPathSet.t ->
    __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (ModPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> ModPathSet.t -> (ModPathSet.t ->
    ModPathSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (ModPathSet.elt -> 'a1
    -> ModPathSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_nodep :
    (ModPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> ModPathSet.t -> 'a2 ->
    (ModPathSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_weak :
    (ModPathSet.elt -> 'a1 -> 'a1) -> 'a1 -> (ModPathSet.t -> ModPathSet.t ->
    'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (ModPathSet.elt -> 'a1 -> ModPathSet.t
    -> __ -> 'a2 -> 'a2) -> ModPathSet.t -> 'a2

  val fold_rel :
    (ModPathSet.elt -> 'a1 -> 'a1) -> (ModPathSet.elt -> 'a2 -> 'a2) -> 'a1
    -> 'a2 -> ModPathSet.t -> 'a3 -> (ModPathSet.elt -> 'a1 -> 'a2 -> __ ->
    'a3 -> 'a3) -> 'a3

  val set_induction :
    (ModPathSet.t -> __ -> 'a1) -> (ModPathSet.t -> ModPathSet.t -> 'a1 ->
    ModPathSet.elt -> __ -> __ -> 'a1) -> ModPathSet.t -> 'a1

  val set_induction_bis :
    (ModPathSet.t -> ModPathSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
    (ModPathSet.elt -> ModPathSet.t -> __ -> 'a1 -> 'a1) -> ModPathSet.t ->
    'a1

  val cardinal_inv_2 : ModPathSet.t -> nat -> ModPathSet.elt

  val cardinal_inv_2b : ModPathSet.t -> ModPathSet.elt
 end

module ModPathSetDecide :
 sig
  module F :
   sig
    val eqb : ModPathComp.t -> ModPathComp.t -> bool
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

module ModPathSetExtraOrdProp :
 sig
  module P :
   sig
    val coq_Exists_dec : ModPathSet.t -> (ModPathComp.t -> sumbool) -> sumbool
   end

  val above : ModPathComp.t -> ModPathSet.t -> bool

  val below : ModPathComp.t -> ModPathSet.t -> bool
 end

module ModPathSetExtraDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a1 -> (Int.Z_as_Int.t -> ModPathSet.Raw.tree -> 'a1 -> ModPathComp.t
      -> ModPathSet.Raw.tree -> 'a1 -> 'a1) -> ModPathSet.Raw.tree -> 'a1

    val tree_rec :
      'a1 -> (Int.Z_as_Int.t -> ModPathSet.Raw.tree -> 'a1 -> ModPathComp.t
      -> ModPathSet.Raw.tree -> 'a1 -> 'a1) -> ModPathSet.Raw.tree -> 'a1

    val tree_caset_nodep :
      'a1 -> (Int.Z_as_Int.t -> ModPathSet.Raw.tree -> 'a1 -> ModPathComp.t
      -> ModPathSet.Raw.tree -> 'a1 -> 'a1) -> ModPathSet.Raw.tree -> 'a1

    val tree_rect_nodep :
      'a1 -> (Int.Z_as_Int.t -> ModPathSet.Raw.tree -> 'a1 -> ModPathComp.t
      -> ModPathSet.Raw.tree -> 'a1 -> 'a1) -> ModPathSet.Raw.tree -> 'a1

    val tree_rec_nodep :
      'a1 -> (Int.Z_as_Int.t -> ModPathSet.Raw.tree -> 'a1 -> ModPathComp.t
      -> ModPathSet.Raw.tree -> 'a1 -> 'a1) -> ModPathSet.Raw.tree -> 'a1

    val lt_tree_dec : ModPathComp.t -> ModPathSet.Raw.tree -> sumbool

    val gt_tree_dec : ModPathComp.t -> ModPathSet.Raw.tree -> sumbool

    val bst_dec : ModPathSet.Raw.tree -> sumbool
   end
 end

module ModPathMap :
 sig
  module E :
   sig
    type t = ModPathComp.t

    val compare :
      ModPathComp.t -> ModPathComp.t -> ModPathComp.t OrderedType.coq_Compare

    val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool
   end

  module Raw :
   sig
    type key = ModPathComp.t

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

    val mem : ModPathComp.t -> 'a1 tree -> bool

    val find : ModPathComp.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : ModPathComp.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : ModPathComp.t -> 'a1 tree -> 'a1 triple

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
      ('a1 -> 'a1 -> bool) -> ModPathComp.t -> 'a1 -> ('a1 enumeration ->
      bool) -> 'a1 enumeration -> bool

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
          type t = ModPathComp.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool

        val lt_dec : ModPathComp.t -> ModPathComp.t -> sumbool

        val eqb : ModPathComp.t -> ModPathComp.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = ModPathComp.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool

          val lt_dec : ModPathComp.t -> ModPathComp.t -> sumbool

          val eqb : ModPathComp.t -> ModPathComp.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = ModPathComp.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool

          val lt_dec : ModPathComp.t -> ModPathComp.t -> sumbool

          val eqb : ModPathComp.t -> ModPathComp.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = ModPathComp.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : ModPathComp.t -> ModPathComp.t -> sumbool

            val lt_dec : ModPathComp.t -> ModPathComp.t -> sumbool

            val eqb : ModPathComp.t -> ModPathComp.t -> bool
           end
         end

        type key = ModPathComp.t

        type 'elt t = (ModPathComp.t, 'elt) prod list

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
        ModPathComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> bool ->
        'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
        -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool ->
        'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        ModPathComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> bool ->
        'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
        -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool ->
        'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        ModPathComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        ModPathComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

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
        ModPathComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        ModPathComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

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
        ModPathComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
        -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        ModPathComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
        -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
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

  type key = ModPathComp.t

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

module ModPathMapFact :
 sig
  module F :
   sig
    val eqb : ModPathComp.t -> ModPathComp.t -> bool

    val coq_In_dec : 'a1 ModPathMap.t -> ModPathMap.key -> sumbool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3

  val of_list : (ModPathMap.key, 'a1) prod list -> 'a1 ModPathMap.t

  val to_list : 'a1 ModPathMap.t -> (ModPathMap.key, 'a1) prod list

  val fold_rec :
    (ModPathMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 ModPathMap.t -> ('a1
    ModPathMap.t -> __ -> 'a3) -> (ModPathMap.key -> 'a1 -> 'a2 -> 'a1
    ModPathMap.t -> 'a1 ModPathMap.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_bis :
    (ModPathMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 ModPathMap.t -> ('a1
    ModPathMap.t -> 'a1 ModPathMap.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
    (ModPathMap.key -> 'a1 -> 'a2 -> 'a1 ModPathMap.t -> __ -> __ -> 'a3 ->
    'a3) -> 'a3

  val fold_rec_nodep :
    (ModPathMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 ModPathMap.t -> 'a3
    -> (ModPathMap.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (ModPathMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 ModPathMap.t -> 'a1
    ModPathMap.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (ModPathMap.key -> 'a1
    -> 'a2 -> 'a1 ModPathMap.t -> __ -> 'a3 -> 'a3) -> 'a1 ModPathMap.t -> 'a3

  val fold_rel :
    (ModPathMap.key -> 'a1 -> 'a2 -> 'a2) -> (ModPathMap.key -> 'a1 -> 'a3 ->
    'a3) -> 'a2 -> 'a3 -> 'a1 ModPathMap.t -> 'a4 -> (ModPathMap.key -> 'a1
    -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

  val map_induction :
    ('a1 ModPathMap.t -> __ -> 'a2) -> ('a1 ModPathMap.t -> 'a1 ModPathMap.t
    -> 'a2 -> ModPathMap.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 ModPathMap.t
    -> 'a2

  val map_induction_bis :
    ('a1 ModPathMap.t -> 'a1 ModPathMap.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
    (ModPathMap.key -> 'a1 -> 'a1 ModPathMap.t -> __ -> 'a2 -> 'a2) -> 'a1
    ModPathMap.t -> 'a2

  val cardinal_inv_2 : 'a1 ModPathMap.t -> nat -> (ModPathMap.key, 'a1) prod

  val cardinal_inv_2b : 'a1 ModPathMap.t -> (ModPathMap.key, 'a1) prod

  val filter :
    (ModPathMap.key -> 'a1 -> bool) -> 'a1 ModPathMap.t -> 'a1 ModPathMap.t

  val for_all : (ModPathMap.key -> 'a1 -> bool) -> 'a1 ModPathMap.t -> bool

  val exists_ : (ModPathMap.key -> 'a1 -> bool) -> 'a1 ModPathMap.t -> bool

  val partition :
    (ModPathMap.key -> 'a1 -> bool) -> 'a1 ModPathMap.t -> ('a1 ModPathMap.t,
    'a1 ModPathMap.t) prod

  val update : 'a1 ModPathMap.t -> 'a1 ModPathMap.t -> 'a1 ModPathMap.t

  val restrict : 'a1 ModPathMap.t -> 'a1 ModPathMap.t -> 'a1 ModPathMap.t

  val diff : 'a1 ModPathMap.t -> 'a1 ModPathMap.t -> 'a1 ModPathMap.t

  val coq_Partition_In :
    'a1 ModPathMap.t -> 'a1 ModPathMap.t -> 'a1 ModPathMap.t ->
    ModPathMap.key -> sumbool

  val update_dec :
    'a1 ModPathMap.t -> 'a1 ModPathMap.t -> ModPathMap.key -> 'a1 -> sumbool

  val filter_dom :
    (ModPathMap.key -> bool) -> 'a1 ModPathMap.t -> 'a1 ModPathMap.t

  val filter_range : ('a1 -> bool) -> 'a1 ModPathMap.t -> 'a1 ModPathMap.t

  val for_all_dom : (ModPathMap.key -> bool) -> 'a1 ModPathMap.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 ModPathMap.t -> bool

  val exists_dom : (ModPathMap.key -> bool) -> 'a1 ModPathMap.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 ModPathMap.t -> bool

  val partition_dom :
    (ModPathMap.key -> bool) -> 'a1 ModPathMap.t -> ('a1 ModPathMap.t, 'a1
    ModPathMap.t) prod

  val partition_range :
    ('a1 -> bool) -> 'a1 ModPathMap.t -> ('a1 ModPathMap.t, 'a1 ModPathMap.t)
    prod
 end

module ModPathMapExtraFact :
 sig
 end

module ModPathMapDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a2 -> ('a1 ModPathMap.Raw.tree -> 'a2 -> ModPathMap.Raw.key -> 'a1 ->
      'a1 ModPathMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      ModPathMap.Raw.tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 ModPathMap.Raw.tree -> 'a2 -> ModPathMap.Raw.key -> 'a1 ->
      'a1 ModPathMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      ModPathMap.Raw.tree -> 'a2

    val tree_caset_nodep :
      'a2 -> ('a1 ModPathMap.Raw.tree -> 'a2 -> ModPathMap.Raw.key -> 'a1 ->
      'a1 ModPathMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      ModPathMap.Raw.tree -> 'a2

    val tree_rect_nodep :
      'a2 -> ('a1 ModPathMap.Raw.tree -> 'a2 -> ModPathMap.Raw.key -> 'a1 ->
      'a1 ModPathMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      ModPathMap.Raw.tree -> 'a2

    val tree_rec_nodep :
      'a2 -> ('a1 ModPathMap.Raw.tree -> 'a2 -> ModPathMap.Raw.key -> 'a1 ->
      'a1 ModPathMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      ModPathMap.Raw.tree -> 'a2

    val lt_tree_dec : ModPathComp.t -> 'a1 ModPathMap.Raw.tree -> sumbool

    val gt_tree_dec : ModPathComp.t -> 'a1 ModPathMap.Raw.tree -> sumbool

    val bst_dec : 'a1 ModPathMap.Raw.tree -> sumbool
   end
 end

val modpath_eq_dec : modpath -> modpath -> sumbool

val modpath_EqDec : modpath coq_EqDec

module KernameComp :
 sig
  type t = kername

  val compare :
    (modpath, String.t) prod -> (modpath, String.t) prod -> comparison
 end

module Kername :
 sig
  type t = kername

  val compare :
    (modpath, String.t) prod -> (modpath, String.t) prod -> comparison

  module OT :
   sig
    type t = KernameComp.t

    val compare :
      KernameComp.t -> KernameComp.t -> KernameComp.t OrderedType.coq_Compare

    val eq_dec : KernameComp.t -> KernameComp.t -> sumbool
   end

  val eqb : (modpath, String.t) prod -> (modpath, String.t) prod -> bool

  val reflect_kername : kername coq_ReflectEq

  val eq_dec : t -> t -> sumbool
 end

module KernameMap :
 sig
  module E :
   sig
    type t = KernameComp.t

    val compare :
      KernameComp.t -> KernameComp.t -> KernameComp.t OrderedType.coq_Compare

    val eq_dec : KernameComp.t -> KernameComp.t -> sumbool
   end

  module Raw :
   sig
    type key = KernameComp.t

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

    val mem : KernameComp.t -> 'a1 tree -> bool

    val find : KernameComp.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : KernameComp.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : KernameComp.t -> 'a1 tree -> 'a1 triple

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
      ('a1 -> 'a1 -> bool) -> KernameComp.t -> 'a1 -> ('a1 enumeration ->
      bool) -> 'a1 enumeration -> bool

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
          type t = KernameComp.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : KernameComp.t -> KernameComp.t -> sumbool

        val lt_dec : KernameComp.t -> KernameComp.t -> sumbool

        val eqb : KernameComp.t -> KernameComp.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = KernameComp.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : KernameComp.t -> KernameComp.t -> sumbool

          val lt_dec : KernameComp.t -> KernameComp.t -> sumbool

          val eqb : KernameComp.t -> KernameComp.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = KernameComp.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : KernameComp.t -> KernameComp.t -> sumbool

          val lt_dec : KernameComp.t -> KernameComp.t -> sumbool

          val eqb : KernameComp.t -> KernameComp.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = KernameComp.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : KernameComp.t -> KernameComp.t -> sumbool

            val lt_dec : KernameComp.t -> KernameComp.t -> sumbool

            val eqb : KernameComp.t -> KernameComp.t -> bool
           end
         end

        type key = KernameComp.t

        type 'elt t = (KernameComp.t, 'elt) prod list

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
        KernameComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> bool ->
        'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
        -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool ->
        'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        KernameComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> bool ->
        'a1 coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __
        -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool ->
        'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Int.Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        KernameComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        KernameComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

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
        KernameComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        KernameComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t ->
        __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

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
        KernameComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
        -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        KernameComp.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
        triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1
        tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
        -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Int.Z_as_Int.t -> __ -> __ -> __ -> 'a1
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

  type key = KernameComp.t

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

module KernameMapFact :
 sig
  module F :
   sig
    val eqb : KernameComp.t -> KernameComp.t -> bool

    val coq_In_dec : 'a1 KernameMap.t -> KernameMap.key -> sumbool
   end

  val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) prod -> 'a3

  val of_list : (KernameMap.key, 'a1) prod list -> 'a1 KernameMap.t

  val to_list : 'a1 KernameMap.t -> (KernameMap.key, 'a1) prod list

  val fold_rec :
    (KernameMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 KernameMap.t -> ('a1
    KernameMap.t -> __ -> 'a3) -> (KernameMap.key -> 'a1 -> 'a2 -> 'a1
    KernameMap.t -> 'a1 KernameMap.t -> __ -> __ -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_bis :
    (KernameMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 KernameMap.t -> ('a1
    KernameMap.t -> 'a1 KernameMap.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 ->
    (KernameMap.key -> 'a1 -> 'a2 -> 'a1 KernameMap.t -> __ -> __ -> 'a3 ->
    'a3) -> 'a3

  val fold_rec_nodep :
    (KernameMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 KernameMap.t -> 'a3
    -> (KernameMap.key -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val fold_rec_weak :
    (KernameMap.key -> 'a1 -> 'a2 -> 'a2) -> 'a2 -> ('a1 KernameMap.t -> 'a1
    KernameMap.t -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3 -> (KernameMap.key -> 'a1
    -> 'a2 -> 'a1 KernameMap.t -> __ -> 'a3 -> 'a3) -> 'a1 KernameMap.t -> 'a3

  val fold_rel :
    (KernameMap.key -> 'a1 -> 'a2 -> 'a2) -> (KernameMap.key -> 'a1 -> 'a3 ->
    'a3) -> 'a2 -> 'a3 -> 'a1 KernameMap.t -> 'a4 -> (KernameMap.key -> 'a1
    -> 'a2 -> 'a3 -> __ -> 'a4 -> 'a4) -> 'a4

  val map_induction :
    ('a1 KernameMap.t -> __ -> 'a2) -> ('a1 KernameMap.t -> 'a1 KernameMap.t
    -> 'a2 -> KernameMap.key -> 'a1 -> __ -> __ -> 'a2) -> 'a1 KernameMap.t
    -> 'a2

  val map_induction_bis :
    ('a1 KernameMap.t -> 'a1 KernameMap.t -> __ -> 'a2 -> 'a2) -> 'a2 ->
    (KernameMap.key -> 'a1 -> 'a1 KernameMap.t -> __ -> 'a2 -> 'a2) -> 'a1
    KernameMap.t -> 'a2

  val cardinal_inv_2 : 'a1 KernameMap.t -> nat -> (KernameMap.key, 'a1) prod

  val cardinal_inv_2b : 'a1 KernameMap.t -> (KernameMap.key, 'a1) prod

  val filter :
    (KernameMap.key -> 'a1 -> bool) -> 'a1 KernameMap.t -> 'a1 KernameMap.t

  val for_all : (KernameMap.key -> 'a1 -> bool) -> 'a1 KernameMap.t -> bool

  val exists_ : (KernameMap.key -> 'a1 -> bool) -> 'a1 KernameMap.t -> bool

  val partition :
    (KernameMap.key -> 'a1 -> bool) -> 'a1 KernameMap.t -> ('a1 KernameMap.t,
    'a1 KernameMap.t) prod

  val update : 'a1 KernameMap.t -> 'a1 KernameMap.t -> 'a1 KernameMap.t

  val restrict : 'a1 KernameMap.t -> 'a1 KernameMap.t -> 'a1 KernameMap.t

  val diff : 'a1 KernameMap.t -> 'a1 KernameMap.t -> 'a1 KernameMap.t

  val coq_Partition_In :
    'a1 KernameMap.t -> 'a1 KernameMap.t -> 'a1 KernameMap.t ->
    KernameMap.key -> sumbool

  val update_dec :
    'a1 KernameMap.t -> 'a1 KernameMap.t -> KernameMap.key -> 'a1 -> sumbool

  val filter_dom :
    (KernameMap.key -> bool) -> 'a1 KernameMap.t -> 'a1 KernameMap.t

  val filter_range : ('a1 -> bool) -> 'a1 KernameMap.t -> 'a1 KernameMap.t

  val for_all_dom : (KernameMap.key -> bool) -> 'a1 KernameMap.t -> bool

  val for_all_range : ('a1 -> bool) -> 'a1 KernameMap.t -> bool

  val exists_dom : (KernameMap.key -> bool) -> 'a1 KernameMap.t -> bool

  val exists_range : ('a1 -> bool) -> 'a1 KernameMap.t -> bool

  val partition_dom :
    (KernameMap.key -> bool) -> 'a1 KernameMap.t -> ('a1 KernameMap.t, 'a1
    KernameMap.t) prod

  val partition_range :
    ('a1 -> bool) -> 'a1 KernameMap.t -> ('a1 KernameMap.t, 'a1 KernameMap.t)
    prod
 end

module KernameMapExtraFact :
 sig
 end

module KernameMapDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a2 -> ('a1 KernameMap.Raw.tree -> 'a2 -> KernameMap.Raw.key -> 'a1 ->
      'a1 KernameMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      KernameMap.Raw.tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 KernameMap.Raw.tree -> 'a2 -> KernameMap.Raw.key -> 'a1 ->
      'a1 KernameMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      KernameMap.Raw.tree -> 'a2

    val tree_caset_nodep :
      'a2 -> ('a1 KernameMap.Raw.tree -> 'a2 -> KernameMap.Raw.key -> 'a1 ->
      'a1 KernameMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      KernameMap.Raw.tree -> 'a2

    val tree_rect_nodep :
      'a2 -> ('a1 KernameMap.Raw.tree -> 'a2 -> KernameMap.Raw.key -> 'a1 ->
      'a1 KernameMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      KernameMap.Raw.tree -> 'a2

    val tree_rec_nodep :
      'a2 -> ('a1 KernameMap.Raw.tree -> 'a2 -> KernameMap.Raw.key -> 'a1 ->
      'a1 KernameMap.Raw.tree -> 'a2 -> Int.Z_as_Int.t -> 'a2) -> 'a1
      KernameMap.Raw.tree -> 'a2

    val lt_tree_dec : KernameComp.t -> 'a1 KernameMap.Raw.tree -> sumbool

    val gt_tree_dec : KernameComp.t -> 'a1 KernameMap.Raw.tree -> sumbool

    val bst_dec : 'a1 KernameMap.Raw.tree -> sumbool
   end
 end

val eq_constant : kername -> kername -> bool

module KernameSet :
 sig
  module Raw :
   sig
    type elt = kername

    type tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree * kername * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : kername -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : kername list -> tree -> kername list

    val elements : tree -> kername list

    val rev_elements_aux : kername list -> tree -> kername list

    val rev_elements : tree -> kername list

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
      kername -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> kername -> tree -> bool

    val subsetr : (tree -> bool) -> kername -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : kername -> tree

    val create : t -> kername -> t -> tree

    val assert_false : t -> kername -> t -> tree

    val bal : t -> kername -> t -> tree

    val add : kername -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> (t, elt) prod

    val merge : tree -> tree -> tree

    val remove : kername -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : kername -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> (t, t) prod

    val ltb_tree : kername -> tree -> bool

    val gtb_tree : kername -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = kername

          val compare : kername -> kername -> comparison

          val eq_dec : kername -> kername -> sumbool
         end

        module TO :
         sig
          type t = kername

          val compare : kername -> kername -> comparison

          val eq_dec : kername -> kername -> sumbool
         end
       end

      val eq_dec : kername -> kername -> sumbool

      val lt_dec : kername -> kername -> sumbool

      val eqb : kername -> kername -> bool
     end

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = kername

            val compare : kername -> kername -> comparison

            val eq_dec : kername -> kername -> sumbool
           end

          module TO :
           sig
            type t = kername

            val compare : kername -> kername -> comparison

            val eq_dec : kername -> kername -> sumbool
           end
         end

        val eq_dec : kername -> kername -> sumbool

        val lt_dec : kername -> kername -> sumbool

        val eqb : kername -> kername -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * kername * t
    | R_bal_1 of t * kername * t * Int.Z_as_Int.t * tree * kername * tree
    | R_bal_2 of t * kername * t * Int.Z_as_Int.t * tree * kername * tree
    | R_bal_3 of t * kername * t * Int.Z_as_Int.t * tree * kername * 
       tree * Int.Z_as_Int.t * tree * kername * tree
    | R_bal_4 of t * kername * t
    | R_bal_5 of t * kername * t * Int.Z_as_Int.t * tree * kername * tree
    | R_bal_6 of t * kername * t * Int.Z_as_Int.t * tree * kername * tree
    | R_bal_7 of t * kername * t * Int.Z_as_Int.t * tree * kername * 
       tree * Int.Z_as_Int.t * tree * kername * tree
    | R_bal_8 of t * kername * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * kername
       * tree * (t, elt) prod * coq_R_remove_min * t * elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
       * Int.Z_as_Int.t * tree * kername * tree * t * elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
       * Int.Z_as_Int.t * tree * kername * tree * t * elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
       * Int.Z_as_Int.t * tree * kername * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
       * Int.Z_as_Int.t * tree * kername * tree * t * bool * t * tree
       * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
       * Int.Z_as_Int.t * tree * kername * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
       * Int.Z_as_Int.t * tree * kername * tree * t * bool * t * tree
       * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * kername * tree
       * Int.Z_as_Int.t * tree * kername * tree * t * bool * t * tree
       * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = kername

    val compare : kername -> kername -> comparison

    val eq_dec : kername -> kername -> sumbool
   end

  type elt = kername

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

module KernameSetFact :
 sig
  val eqb : kername -> kername -> bool
 end

module KernameSetOrdProp :
 sig
  module ME :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = kername

        val compare : kername -> kername -> comparison

        val eq_dec : kername -> kername -> sumbool
       end

      module TO :
       sig
        type t = kername

        val compare : kername -> kername -> comparison

        val eq_dec : kername -> kername -> sumbool
       end
     end

    val eq_dec : kername -> kername -> sumbool

    val lt_dec : kername -> kername -> sumbool

    val eqb : kername -> kername -> bool
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
        val eqb : kername -> kername -> bool
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
      val eqb : kername -> kername -> bool
     end

    val coq_In_dec : KernameSet.elt -> KernameSet.t -> sumbool

    val of_list : KernameSet.elt list -> KernameSet.t

    val to_list : KernameSet.t -> KernameSet.elt list

    val fold_rec :
      (KernameSet.elt -> 'a1 -> 'a1) -> 'a1 -> KernameSet.t -> (KernameSet.t
      -> __ -> 'a2) -> (KernameSet.elt -> 'a1 -> KernameSet.t -> KernameSet.t
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (KernameSet.elt -> 'a1 -> 'a1) -> 'a1 -> KernameSet.t -> (KernameSet.t
      -> KernameSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (KernameSet.elt
      -> 'a1 -> KernameSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (KernameSet.elt -> 'a1 -> 'a1) -> 'a1 -> KernameSet.t -> 'a2 ->
      (KernameSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (KernameSet.elt -> 'a1 -> 'a1) -> 'a1 -> (KernameSet.t -> KernameSet.t
      -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (KernameSet.elt -> 'a1 ->
      KernameSet.t -> __ -> 'a2 -> 'a2) -> KernameSet.t -> 'a2

    val fold_rel :
      (KernameSet.elt -> 'a1 -> 'a1) -> (KernameSet.elt -> 'a2 -> 'a2) -> 'a1
      -> 'a2 -> KernameSet.t -> 'a3 -> (KernameSet.elt -> 'a1 -> 'a2 -> __ ->
      'a3 -> 'a3) -> 'a3

    val set_induction :
      (KernameSet.t -> __ -> 'a1) -> (KernameSet.t -> KernameSet.t -> 'a1 ->
      KernameSet.elt -> __ -> __ -> 'a1) -> KernameSet.t -> 'a1

    val set_induction_bis :
      (KernameSet.t -> KernameSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
      (KernameSet.elt -> KernameSet.t -> __ -> 'a1 -> 'a1) -> KernameSet.t ->
      'a1

    val cardinal_inv_2 : KernameSet.t -> nat -> KernameSet.elt

    val cardinal_inv_2b : KernameSet.t -> KernameSet.elt
   end

  val gtb : kername -> kername -> bool

  val leb : kername -> kername -> bool

  val elements_lt : kername -> KernameSet.t -> kername list

  val elements_ge : kername -> KernameSet.t -> kername list

  val set_induction_max :
    (KernameSet.t -> __ -> 'a1) -> (KernameSet.t -> KernameSet.t -> 'a1 ->
    kername -> __ -> __ -> 'a1) -> KernameSet.t -> 'a1

  val set_induction_min :
    (KernameSet.t -> __ -> 'a1) -> (KernameSet.t -> KernameSet.t -> 'a1 ->
    kername -> __ -> __ -> 'a1) -> KernameSet.t -> 'a1
 end

module KernameSetProp :
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb : kername -> kername -> bool
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
    val eqb : kername -> kername -> bool
   end

  val coq_In_dec : KernameSet.elt -> KernameSet.t -> sumbool

  val of_list : KernameSet.elt list -> KernameSet.t

  val to_list : KernameSet.t -> KernameSet.elt list

  val fold_rec :
    (KernameSet.elt -> 'a1 -> 'a1) -> 'a1 -> KernameSet.t -> (KernameSet.t ->
    __ -> 'a2) -> (KernameSet.elt -> 'a1 -> KernameSet.t -> KernameSet.t ->
    __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (KernameSet.elt -> 'a1 -> 'a1) -> 'a1 -> KernameSet.t -> (KernameSet.t ->
    KernameSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (KernameSet.elt -> 'a1
    -> KernameSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_nodep :
    (KernameSet.elt -> 'a1 -> 'a1) -> 'a1 -> KernameSet.t -> 'a2 ->
    (KernameSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_weak :
    (KernameSet.elt -> 'a1 -> 'a1) -> 'a1 -> (KernameSet.t -> KernameSet.t ->
    'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (KernameSet.elt -> 'a1 -> KernameSet.t
    -> __ -> 'a2 -> 'a2) -> KernameSet.t -> 'a2

  val fold_rel :
    (KernameSet.elt -> 'a1 -> 'a1) -> (KernameSet.elt -> 'a2 -> 'a2) -> 'a1
    -> 'a2 -> KernameSet.t -> 'a3 -> (KernameSet.elt -> 'a1 -> 'a2 -> __ ->
    'a3 -> 'a3) -> 'a3

  val set_induction :
    (KernameSet.t -> __ -> 'a1) -> (KernameSet.t -> KernameSet.t -> 'a1 ->
    KernameSet.elt -> __ -> __ -> 'a1) -> KernameSet.t -> 'a1

  val set_induction_bis :
    (KernameSet.t -> KernameSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
    (KernameSet.elt -> KernameSet.t -> __ -> 'a1 -> 'a1) -> KernameSet.t ->
    'a1

  val cardinal_inv_2 : KernameSet.t -> nat -> KernameSet.elt

  val cardinal_inv_2b : KernameSet.t -> KernameSet.elt
 end

module KernameSetDecide :
 sig
  module F :
   sig
    val eqb : kername -> kername -> bool
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

module KernameSetExtraOrdProp :
 sig
  module P :
   sig
    val coq_Exists_dec : KernameSet.t -> (kername -> sumbool) -> sumbool
   end

  val above : kername -> KernameSet.t -> bool

  val below : kername -> KernameSet.t -> bool
 end

module KernameSetExtraDecide :
 sig
  module Raw :
   sig
    val tree_rect :
      'a1 -> (Int.Z_as_Int.t -> KernameSet.Raw.tree -> 'a1 -> kername ->
      KernameSet.Raw.tree -> 'a1 -> 'a1) -> KernameSet.Raw.tree -> 'a1

    val tree_rec :
      'a1 -> (Int.Z_as_Int.t -> KernameSet.Raw.tree -> 'a1 -> kername ->
      KernameSet.Raw.tree -> 'a1 -> 'a1) -> KernameSet.Raw.tree -> 'a1

    val tree_caset_nodep :
      'a1 -> (Int.Z_as_Int.t -> KernameSet.Raw.tree -> 'a1 -> kername ->
      KernameSet.Raw.tree -> 'a1 -> 'a1) -> KernameSet.Raw.tree -> 'a1

    val tree_rect_nodep :
      'a1 -> (Int.Z_as_Int.t -> KernameSet.Raw.tree -> 'a1 -> kername ->
      KernameSet.Raw.tree -> 'a1 -> 'a1) -> KernameSet.Raw.tree -> 'a1

    val tree_rec_nodep :
      'a1 -> (Int.Z_as_Int.t -> KernameSet.Raw.tree -> 'a1 -> kername ->
      KernameSet.Raw.tree -> 'a1 -> 'a1) -> KernameSet.Raw.tree -> 'a1

    val lt_tree_dec : kername -> KernameSet.Raw.tree -> sumbool

    val gt_tree_dec : kername -> KernameSet.Raw.tree -> sumbool

    val bst_dec : KernameSet.Raw.tree -> sumbool
   end
 end

type inductive = { inductive_mind : kername; inductive_ind : nat }

val inductive_mind : inductive -> kername

val inductive_ind : inductive -> nat

val coq_NoConfusionPackage_inductive : inductive coq_NoConfusionPackage

val string_of_inductive : inductive -> String.t

val eq_inductive_def : inductive -> inductive -> bool

val reflect_eq_inductive : inductive coq_ReflectEq

type projection = { proj_ind : inductive; proj_npars : nat; proj_arg : nat }

val proj_ind : projection -> inductive

val proj_npars : projection -> nat

val proj_arg : projection -> nat

val eq_projection : projection -> projection -> bool

val reflect_eq_projection : projection coq_ReflectEq

type global_reference =
| VarRef of ident
| ConstRef of kername
| IndRef of inductive
| ConstructRef of inductive * nat

val global_reference_rect :
  (ident -> 'a1) -> (kername -> 'a1) -> (inductive -> 'a1) -> (inductive ->
  nat -> 'a1) -> global_reference -> 'a1

val global_reference_rec :
  (ident -> 'a1) -> (kername -> 'a1) -> (inductive -> 'a1) -> (inductive ->
  nat -> 'a1) -> global_reference -> 'a1

val coq_NoConfusionPackage_global_reference :
  global_reference coq_NoConfusionPackage

val string_of_gref : global_reference -> String.t

val gref_eqb : global_reference -> global_reference -> bool

val grep_reflect_eq : global_reference coq_ReflectEq

val gref_eq_dec : global_reference -> global_reference -> sumbool

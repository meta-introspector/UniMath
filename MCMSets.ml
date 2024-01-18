open BinInt
open Classes
open Datatypes
open Equalities
open List
open MSetInterface
open MSetList
open Orders
open Specif

type __ = Obj.t

module type IsLeibniz =
 functor (T:Eq) ->
 sig
 end

module UsualIsLeibniz =
 functor (T:UsualEq) ->
 struct
 end

module type IsLtIrrel =
 functor (T:EqLt) ->
 sig
 end

module MSets =
 struct
  module type UsualSets =
   sig
    module E :
     UsualOrderedType

    type elt = E.t

    type t

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val partition : (elt -> bool) -> t -> (t, t) prod

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val eq_dec : t -> t -> sumbool

    val compare : t -> t -> comparison

    val min_elt : t -> elt option

    val max_elt : t -> elt option
   end

  module type WDecideOnSig =
   functor (E:DecidableType) ->
   functor (M:sig
    type elt = E.t

    type t

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val partition : (elt -> bool) -> t -> (t, t) prod

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val eq_dec : t -> t -> sumbool
   end) ->
   sig
    module F :
     sig
      val eqb : E.t -> E.t -> bool
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

  module type WDecideSig =
   functor (M:WSets) ->
   sig
    module F :
     sig
      val eqb : M.E.t -> M.E.t -> bool
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

  module type DecideSig =
   functor (M:WSets) ->
   sig
    module F :
     sig
      val eqb : M.E.t -> M.E.t -> bool
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

  module type WFactsOnSig =
   functor (E:DecidableType) ->
   functor (M:sig
    type elt = E.t

    type t

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val partition : (elt -> bool) -> t -> (t, t) prod

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val eq_dec : t -> t -> sumbool
   end) ->
   sig
    val eqb : E.t -> E.t -> bool
   end

  module type WFactsSig =
   functor (M:WSets) ->
   sig
    val eqb : M.E.t -> M.E.t -> bool
   end

  module type FactsSig =
   functor (M:WSets) ->
   sig
    val eqb : M.E.t -> M.E.t -> bool
   end

  module type WPropertiesOnSig =
   functor (E:DecidableType) ->
   functor (M:sig
    type elt = E.t

    type t

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val partition : (elt -> bool) -> t -> (t, t) prod

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val eq_dec : t -> t -> sumbool
   end) ->
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : E.t -> E.t -> bool
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
      val eqb : E.t -> E.t -> bool
     end

    val coq_In_dec : M.elt -> M.t -> sumbool

    val of_list : M.elt list -> M.t

    val to_list : M.t -> M.elt list

    val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
      'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

    val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
      'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
      -> M.t -> 'a1

    val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
      -> 'a1) -> M.t -> 'a1

    val cardinal_inv_2 : M.t -> nat -> M.elt

    val cardinal_inv_2b : M.t -> M.elt
   end

  module type WPropertiesSig =
   functor (M:WSets) ->
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : M.E.t -> M.E.t -> bool
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
      val eqb : M.E.t -> M.E.t -> bool
     end

    val coq_In_dec : M.elt -> M.t -> sumbool

    val of_list : M.elt list -> M.t

    val to_list : M.t -> M.elt list

    val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
      'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

    val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
      'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
      -> M.t -> 'a1

    val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
      -> 'a1) -> M.t -> 'a1

    val cardinal_inv_2 : M.t -> nat -> M.elt

    val cardinal_inv_2b : M.t -> M.elt
   end

  module type PropertiesSig =
   functor (M:WSets) ->
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : M.E.t -> M.E.t -> bool
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
      val eqb : M.E.t -> M.E.t -> bool
     end

    val coq_In_dec : M.elt -> M.t -> sumbool

    val of_list : M.elt list -> M.t

    val to_list : M.t -> M.elt list

    val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
      'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

    val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
      'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
      -> M.t -> 'a1

    val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
      -> 'a1) -> M.t -> 'a1

    val cardinal_inv_2 : M.t -> nat -> M.elt

    val cardinal_inv_2b : M.t -> M.elt
   end

  module type OrdPropertiesSig =
   functor (M:Sets) ->
   sig
    module ME :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = M.E.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end
       end

      val eq_dec : M.E.t -> M.E.t -> sumbool

      val lt_dec : M.E.t -> M.E.t -> sumbool

      val eqb : M.E.t -> M.E.t -> bool
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
          val eqb : M.E.t -> M.E.t -> bool
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
        val eqb : M.E.t -> M.E.t -> bool
       end

      val coq_In_dec : M.elt -> M.t -> sumbool

      val of_list : M.elt list -> M.t

      val to_list : M.t -> M.elt list

      val fold_rec :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt
        -> 'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ ->
        'a2 -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2)
        -> 'a2

      val fold_rec_nodep :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
        'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

      val fold_rel :
        (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t
        -> 'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
        -> M.t -> 'a1

      val set_induction_bis :
        (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
        -> 'a1) -> M.t -> 'a1

      val cardinal_inv_2 : M.t -> nat -> M.elt

      val cardinal_inv_2b : M.t -> M.elt
     end

    val gtb : M.E.t -> M.E.t -> bool

    val leb : M.E.t -> M.E.t -> bool

    val elements_lt : M.E.t -> M.t -> M.E.t list

    val elements_ge : M.E.t -> M.t -> M.E.t list

    val set_induction_max :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.E.t -> __ -> __ -> 'a1)
      -> M.t -> 'a1

    val set_induction_min :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.E.t -> __ -> __ -> 'a1)
      -> M.t -> 'a1
   end

  module WExtraPropertiesOn =
   functor (E:DecidableType) ->
   functor (W:sig
    type elt = E.t

    type t

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val partition : (elt -> bool) -> t -> (t, t) prod

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val eq_dec : t -> t -> sumbool
   end) ->
   functor (WProperties:sig
    module Dec :
     sig
      module F :
       sig
        val eqb : E.t -> E.t -> bool
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
      val eqb : E.t -> E.t -> bool
     end

    val coq_In_dec : W.elt -> W.t -> sumbool

    val of_list : W.elt list -> W.t

    val to_list : W.t -> W.elt list

    val fold_rec :
      (W.elt -> 'a1 -> 'a1) -> 'a1 -> W.t -> (W.t -> __ -> 'a2) -> (W.elt ->
      'a1 -> W.t -> W.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (W.elt -> 'a1 -> 'a1) -> 'a1 -> W.t -> (W.t -> W.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (W.elt -> 'a1 -> W.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (W.elt -> 'a1 -> 'a1) -> 'a1 -> W.t -> 'a2 -> (W.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (W.elt -> 'a1 -> 'a1) -> 'a1 -> (W.t -> W.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (W.elt -> 'a1 -> W.t -> __ -> 'a2 -> 'a2) -> W.t -> 'a2

    val fold_rel :
      (W.elt -> 'a1 -> 'a1) -> (W.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> W.t ->
      'a3 -> (W.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (W.t -> __ -> 'a1) -> (W.t -> W.t -> 'a1 -> W.elt -> __ -> __ -> 'a1)
      -> W.t -> 'a1

    val set_induction_bis :
      (W.t -> W.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (W.elt -> W.t -> __ -> 'a1
      -> 'a1) -> W.t -> 'a1

    val cardinal_inv_2 : W.t -> nat -> W.elt

    val cardinal_inv_2b : W.t -> W.elt
   end) ->
   struct
    (** val coq_Exists_dec : W.t -> (E.t -> sumbool) -> sumbool **)

    let coq_Exists_dec s p_dec =
      coq_Exists_dec (W.elements s) p_dec
   end

  module type WExtraPropertiesOnSig =
   functor (E:DecidableType) ->
   functor (W:sig
    type elt = E.t

    type t

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val equal : t -> t -> bool

    val subset : t -> t -> bool

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val partition : (elt -> bool) -> t -> (t, t) prod

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val eq_dec : t -> t -> sumbool
   end) ->
   functor (WProperties:sig
    module Dec :
     sig
      module F :
       sig
        val eqb : E.t -> E.t -> bool
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
      val eqb : E.t -> E.t -> bool
     end

    val coq_In_dec : W.elt -> W.t -> sumbool

    val of_list : W.elt list -> W.t

    val to_list : W.t -> W.elt list

    val fold_rec :
      (W.elt -> 'a1 -> 'a1) -> 'a1 -> W.t -> (W.t -> __ -> 'a2) -> (W.elt ->
      'a1 -> W.t -> W.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (W.elt -> 'a1 -> 'a1) -> 'a1 -> W.t -> (W.t -> W.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (W.elt -> 'a1 -> W.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (W.elt -> 'a1 -> 'a1) -> 'a1 -> W.t -> 'a2 -> (W.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (W.elt -> 'a1 -> 'a1) -> 'a1 -> (W.t -> W.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (W.elt -> 'a1 -> W.t -> __ -> 'a2 -> 'a2) -> W.t -> 'a2

    val fold_rel :
      (W.elt -> 'a1 -> 'a1) -> (W.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> W.t ->
      'a3 -> (W.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (W.t -> __ -> 'a1) -> (W.t -> W.t -> 'a1 -> W.elt -> __ -> __ -> 'a1)
      -> W.t -> 'a1

    val set_induction_bis :
      (W.t -> W.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (W.elt -> W.t -> __ -> 'a1
      -> 'a1) -> W.t -> 'a1

    val cardinal_inv_2 : W.t -> nat -> W.elt

    val cardinal_inv_2b : W.t -> W.elt
   end) ->
   sig
    val coq_Exists_dec : W.t -> (E.t -> sumbool) -> sumbool
   end

  module ExtraOrdProperties =
   functor (M:Sets) ->
   functor (MOrdProperties:sig
    module ME :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = M.E.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end
       end

      val eq_dec : M.E.t -> M.E.t -> sumbool

      val lt_dec : M.E.t -> M.E.t -> sumbool

      val eqb : M.E.t -> M.E.t -> bool
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
          val eqb : M.E.t -> M.E.t -> bool
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
        val eqb : M.E.t -> M.E.t -> bool
       end

      val coq_In_dec : M.elt -> M.t -> sumbool

      val of_list : M.elt list -> M.t

      val to_list : M.t -> M.elt list

      val fold_rec :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt
        -> 'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ ->
        'a2 -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2)
        -> 'a2

      val fold_rec_nodep :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
        'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

      val fold_rel :
        (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t
        -> 'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
        -> M.t -> 'a1

      val set_induction_bis :
        (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
        -> 'a1) -> M.t -> 'a1

      val cardinal_inv_2 : M.t -> nat -> M.elt

      val cardinal_inv_2b : M.t -> M.elt
     end

    val gtb : M.E.t -> M.E.t -> bool

    val leb : M.E.t -> M.E.t -> bool

    val elements_lt : M.E.t -> M.t -> M.E.t list

    val elements_ge : M.E.t -> M.t -> M.E.t list

    val set_induction_max :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.E.t -> __ -> __ -> 'a1)
      -> M.t -> 'a1

    val set_induction_min :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.E.t -> __ -> __ -> 'a1)
      -> M.t -> 'a1
   end) ->
   struct
    module P = WExtraPropertiesOn(M.E)(M)(MOrdProperties.P)

    (** val above : M.E.t -> M.t -> bool **)

    let above x s =
      M.for_all (fun y ->
        match MOrdProperties.ME.lt_dec y x with
        | Coq_left -> Coq_true
        | Coq_right -> Coq_false) s

    (** val below : M.E.t -> M.t -> bool **)

    let below x s =
      M.for_all (fun y ->
        match MOrdProperties.ME.lt_dec x y with
        | Coq_left -> Coq_true
        | Coq_right -> Coq_false) s
   end

  module type ExtraOrdPropertiesSig =
   functor (M:Sets) ->
   functor (MOrdProperties:sig
    module ME :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = M.E.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> sumbool
         end
       end

      val eq_dec : M.E.t -> M.E.t -> sumbool

      val lt_dec : M.E.t -> M.E.t -> sumbool

      val eqb : M.E.t -> M.E.t -> bool
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
          val eqb : M.E.t -> M.E.t -> bool
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
        val eqb : M.E.t -> M.E.t -> bool
       end

      val coq_In_dec : M.elt -> M.t -> sumbool

      val of_list : M.elt list -> M.t

      val to_list : M.t -> M.elt list

      val fold_rec :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt
        -> 'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_bis :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ ->
        'a2 -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2)
        -> 'a2

      val fold_rec_nodep :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
        'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
        'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

      val fold_rel :
        (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t
        -> 'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
        -> M.t -> 'a1

      val set_induction_bis :
        (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
        -> 'a1) -> M.t -> 'a1

      val cardinal_inv_2 : M.t -> nat -> M.elt

      val cardinal_inv_2b : M.t -> M.elt
     end

    val gtb : M.E.t -> M.E.t -> bool

    val leb : M.E.t -> M.E.t -> bool

    val elements_lt : M.E.t -> M.t -> M.E.t list

    val elements_ge : M.E.t -> M.t -> M.E.t list

    val set_induction_max :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.E.t -> __ -> __ -> 'a1)
      -> M.t -> 'a1

    val set_induction_min :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.E.t -> __ -> __ -> 'a1)
      -> M.t -> 'a1
   end) ->
   sig
    module P :
     sig
      val coq_Exists_dec : M.t -> (M.E.t -> sumbool) -> sumbool
     end

    val above : M.E.t -> M.t -> bool

    val below : M.E.t -> M.t -> bool
   end
 end

module MSetAVL =
 struct
  module type MakeSig =
   functor (T:OrderedType) ->
   sig
    module Raw :
     sig
      type elt = T.t

      type tree =
      | Leaf
      | Node of Int.Z_as_Int.t * tree * T.t * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : T.t -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : T.t list -> tree -> T.t list

      val elements : tree -> T.t list

      val rev_elements_aux : T.t list -> tree -> T.t list

      val rev_elements : tree -> T.t list

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
        T.t -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> T.t -> tree -> bool

      val subsetr : (tree -> bool) -> T.t -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Int.Z_as_Int.t

      val singleton : T.t -> tree

      val create : t -> T.t -> t -> tree

      val assert_false : t -> T.t -> t -> tree

      val bal : t -> T.t -> t -> tree

      val add : T.t -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> (t, elt) prod

      val merge : tree -> tree -> tree

      val remove : T.t -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : T.t -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> (t, t) prod

      val ltb_tree : T.t -> tree -> bool

      val gtb_tree : T.t -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = T.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : T.t -> T.t -> sumbool

        val lt_dec : T.t -> T.t -> sumbool

        val eqb : T.t -> T.t -> bool
       end

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = T.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end

            module TO :
             sig
              type t = OTF.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end
           end

          val eq_dec : T.t -> T.t -> sumbool

          val lt_dec : T.t -> T.t -> sumbool

          val eqb : T.t -> T.t -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * T.t * t
      | R_bal_1 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_2 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_3 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_4 of t * T.t * t
      | R_bal_5 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_6 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_7 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_8 of t * T.t * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * T.t * 
         tree * (t, elt) prod * coq_R_remove_min * t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = T.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    type elt = T.t

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

  module Decide =
   functor (T:OrderedType) ->
   functor (M:sig
    module Raw :
     sig
      type elt = T.t

      type tree =
      | Leaf
      | Node of Int.Z_as_Int.t * tree * T.t * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : T.t -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : T.t list -> tree -> T.t list

      val elements : tree -> T.t list

      val rev_elements_aux : T.t list -> tree -> T.t list

      val rev_elements : tree -> T.t list

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
        T.t -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> T.t -> tree -> bool

      val subsetr : (tree -> bool) -> T.t -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Int.Z_as_Int.t

      val singleton : T.t -> tree

      val create : t -> T.t -> t -> tree

      val assert_false : t -> T.t -> t -> tree

      val bal : t -> T.t -> t -> tree

      val add : T.t -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> (t, elt) prod

      val merge : tree -> tree -> tree

      val remove : T.t -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : T.t -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> (t, t) prod

      val ltb_tree : T.t -> tree -> bool

      val gtb_tree : T.t -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = T.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : T.t -> T.t -> sumbool

        val lt_dec : T.t -> T.t -> sumbool

        val eqb : T.t -> T.t -> bool
       end

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = T.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end

            module TO :
             sig
              type t = OTF.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end
           end

          val eq_dec : T.t -> T.t -> sumbool

          val lt_dec : T.t -> T.t -> sumbool

          val eqb : T.t -> T.t -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * T.t * t
      | R_bal_1 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_2 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_3 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_4 of t * T.t * t
      | R_bal_5 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_6 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_7 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_8 of t * T.t * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * T.t * 
         tree * (t, elt) prod * coq_R_remove_min * t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = T.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    type elt = T.t

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
   end) ->
   struct
    module Raw =
     struct
      (** val tree_rect :
          'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
          'a1 -> 'a1) -> M.Raw.tree -> 'a1 **)

      let rec tree_rect f f0 = function
      | M.Raw.Leaf -> f
      | M.Raw.Node (t1, t2, t3, t4) ->
        f0 t1 t2 (tree_rect f f0 t2) t3 t4 (tree_rect f f0 t4)

      (** val tree_rec :
          'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
          'a1 -> 'a1) -> M.Raw.tree -> 'a1 **)

      let rec tree_rec f f0 = function
      | M.Raw.Leaf -> f
      | M.Raw.Node (t1, t2, t3, t4) ->
        f0 t1 t2 (tree_rec f f0 t2) t3 t4 (tree_rec f f0 t4)

      (** val tree_caset_nodep :
          'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
          'a1 -> 'a1) -> M.Raw.tree -> 'a1 **)

      let rec tree_caset_nodep f f0 = function
      | M.Raw.Leaf -> f
      | M.Raw.Node (t1, t2, t3, t4) ->
        f0 t1 t2 (tree_caset_nodep f f0 t2) t3 t4 (tree_caset_nodep f f0 t4)

      (** val tree_rect_nodep :
          'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
          'a1 -> 'a1) -> M.Raw.tree -> 'a1 **)

      let rec tree_rect_nodep f f0 = function
      | M.Raw.Leaf -> f
      | M.Raw.Node (t1, t2, t3, t4) ->
        f0 t1 t2 (tree_rect_nodep f f0 t2) t3 t4 (tree_rect_nodep f f0 t4)

      (** val tree_rec_nodep :
          'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
          'a1 -> 'a1) -> M.Raw.tree -> 'a1 **)

      let rec tree_rec_nodep f f0 = function
      | M.Raw.Leaf -> f
      | M.Raw.Node (t1, t2, t3, t4) ->
        f0 t1 t2 (tree_rec_nodep f f0 t2) t3 t4 (tree_rec_nodep f f0 t4)

      (** val lt_tree_dec : T.t -> M.Raw.tree -> sumbool **)

      let rec lt_tree_dec x = function
      | M.Raw.Leaf -> Coq_left
      | M.Raw.Node (_, l, n, r) ->
        (match T.compare n x with
         | Lt ->
           (match lt_tree_dec x l with
            | Coq_left -> lt_tree_dec x r
            | Coq_right -> Coq_right)
         | _ -> Coq_right)

      (** val gt_tree_dec : T.t -> M.Raw.tree -> sumbool **)

      let rec gt_tree_dec x = function
      | M.Raw.Leaf -> Coq_left
      | M.Raw.Node (_, l, n, r) ->
        (match T.compare n x with
         | Gt ->
           (match gt_tree_dec x l with
            | Coq_left -> gt_tree_dec x r
            | Coq_right -> Coq_right)
         | _ -> Coq_right)

      (** val bst_dec : M.Raw.tree -> sumbool **)

      let rec bst_dec = function
      | M.Raw.Leaf -> Coq_left
      | M.Raw.Node (_, l, n, r) ->
        (match bst_dec l with
         | Coq_left ->
           (match bst_dec r with
            | Coq_left ->
              (match lt_tree_dec n l with
               | Coq_left -> gt_tree_dec n r
               | Coq_right -> Coq_right)
            | Coq_right -> Coq_right)
         | Coq_right -> Coq_right)
     end
   end

  module type DecideSig =
   functor (T:OrderedType) ->
   functor (M:sig
    module Raw :
     sig
      type elt = T.t

      type tree =
      | Leaf
      | Node of Int.Z_as_Int.t * tree * T.t * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : T.t -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : T.t list -> tree -> T.t list

      val elements : tree -> T.t list

      val rev_elements_aux : T.t list -> tree -> T.t list

      val rev_elements : tree -> T.t list

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
        T.t -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> T.t -> tree -> bool

      val subsetr : (tree -> bool) -> T.t -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Int.Z_as_Int.t

      val singleton : T.t -> tree

      val create : t -> T.t -> t -> tree

      val assert_false : t -> T.t -> t -> tree

      val bal : t -> T.t -> t -> tree

      val add : T.t -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> (t, elt) prod

      val merge : tree -> tree -> tree

      val remove : T.t -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : T.t -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> (t, t) prod

      val ltb_tree : T.t -> tree -> bool

      val gtb_tree : T.t -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = T.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : T.t -> T.t -> sumbool

        val lt_dec : T.t -> T.t -> sumbool

        val eqb : T.t -> T.t -> bool
       end

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = T.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end

            module TO :
             sig
              type t = OTF.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end
           end

          val eq_dec : T.t -> T.t -> sumbool

          val lt_dec : T.t -> T.t -> sumbool

          val eqb : T.t -> T.t -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * T.t * t
      | R_bal_1 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_2 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_3 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_4 of t * T.t * t
      | R_bal_5 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_6 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_7 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_8 of t * T.t * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * T.t * 
         tree * (t, elt) prod * coq_R_remove_min * t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = T.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    type elt = T.t

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
   end) ->
   sig
    module Raw :
     sig
      val tree_rect :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_rec :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_caset_nodep :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_rect_nodep :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_rec_nodep :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val lt_tree_dec : T.t -> M.Raw.tree -> sumbool

      val gt_tree_dec : T.t -> M.Raw.tree -> sumbool

      val bst_dec : M.Raw.tree -> sumbool
     end
   end

  module LtIrrel =
   functor (T:OrderedType) ->
   functor (M:sig
    module Raw :
     sig
      type elt = T.t

      type tree =
      | Leaf
      | Node of Int.Z_as_Int.t * tree * T.t * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : T.t -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : T.t list -> tree -> T.t list

      val elements : tree -> T.t list

      val rev_elements_aux : T.t list -> tree -> T.t list

      val rev_elements : tree -> T.t list

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
        T.t -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> T.t -> tree -> bool

      val subsetr : (tree -> bool) -> T.t -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Int.Z_as_Int.t

      val singleton : T.t -> tree

      val create : t -> T.t -> t -> tree

      val assert_false : t -> T.t -> t -> tree

      val bal : t -> T.t -> t -> tree

      val add : T.t -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> (t, elt) prod

      val merge : tree -> tree -> tree

      val remove : T.t -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : T.t -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> (t, t) prod

      val ltb_tree : T.t -> tree -> bool

      val gtb_tree : T.t -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = T.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : T.t -> T.t -> sumbool

        val lt_dec : T.t -> T.t -> sumbool

        val eqb : T.t -> T.t -> bool
       end

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = T.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end

            module TO :
             sig
              type t = OTF.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end
           end

          val eq_dec : T.t -> T.t -> sumbool

          val lt_dec : T.t -> T.t -> sumbool

          val eqb : T.t -> T.t -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * T.t * t
      | R_bal_1 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_2 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_3 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_4 of t * T.t * t
      | R_bal_5 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_6 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_7 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_8 of t * T.t * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * T.t * 
         tree * (t, elt) prod * coq_R_remove_min * t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = T.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    type elt = T.t

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
   end) ->
   functor (TIrrel:sig
   end) ->
   struct
    module Raw =
     struct
     end
   end

  module type LtIrrelSig =
   functor (T:OrderedType) ->
   functor (M:sig
    module Raw :
     sig
      type elt = T.t

      type tree =
      | Leaf
      | Node of Int.Z_as_Int.t * tree * T.t * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : T.t -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : T.t list -> tree -> T.t list

      val elements : tree -> T.t list

      val rev_elements_aux : T.t list -> tree -> T.t list

      val rev_elements : tree -> T.t list

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
        T.t -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> T.t -> tree -> bool

      val subsetr : (tree -> bool) -> T.t -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Int.Z_as_Int.t

      val singleton : T.t -> tree

      val create : t -> T.t -> t -> tree

      val assert_false : t -> T.t -> t -> tree

      val bal : t -> T.t -> t -> tree

      val add : T.t -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> (t, elt) prod

      val merge : tree -> tree -> tree

      val remove : T.t -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : T.t -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> (t, t) prod

      val ltb_tree : T.t -> tree -> bool

      val gtb_tree : T.t -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = T.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : T.t -> T.t -> sumbool

        val lt_dec : T.t -> T.t -> sumbool

        val eqb : T.t -> T.t -> bool
       end

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = T.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end

            module TO :
             sig
              type t = OTF.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end
           end

          val eq_dec : T.t -> T.t -> sumbool

          val lt_dec : T.t -> T.t -> sumbool

          val eqb : T.t -> T.t -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * T.t * t
      | R_bal_1 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_2 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_3 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_4 of t * T.t * t
      | R_bal_5 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_6 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_7 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_8 of t * T.t * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * T.t * 
         tree * (t, elt) prod * coq_R_remove_min * t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = T.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    type elt = T.t

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
   end) ->
   functor (TIrrel:sig
   end) ->
   sig
    module Raw :
     sig
     end
   end

  module DecideWithLeibniz =
   functor (T:OrderedType) ->
   functor (M:sig
    module Raw :
     sig
      type elt = T.t

      type tree =
      | Leaf
      | Node of Int.Z_as_Int.t * tree * T.t * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : T.t -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : T.t list -> tree -> T.t list

      val elements : tree -> T.t list

      val rev_elements_aux : T.t list -> tree -> T.t list

      val rev_elements : tree -> T.t list

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
        T.t -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> T.t -> tree -> bool

      val subsetr : (tree -> bool) -> T.t -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Int.Z_as_Int.t

      val singleton : T.t -> tree

      val create : t -> T.t -> t -> tree

      val assert_false : t -> T.t -> t -> tree

      val bal : t -> T.t -> t -> tree

      val add : T.t -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> (t, elt) prod

      val merge : tree -> tree -> tree

      val remove : T.t -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : T.t -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> (t, t) prod

      val ltb_tree : T.t -> tree -> bool

      val gtb_tree : T.t -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = T.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : T.t -> T.t -> sumbool

        val lt_dec : T.t -> T.t -> sumbool

        val eqb : T.t -> T.t -> bool
       end

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = T.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end

            module TO :
             sig
              type t = OTF.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end
           end

          val eq_dec : T.t -> T.t -> sumbool

          val lt_dec : T.t -> T.t -> sumbool

          val eqb : T.t -> T.t -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * T.t * t
      | R_bal_1 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_2 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_3 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_4 of t * T.t * t
      | R_bal_5 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_6 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_7 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_8 of t * T.t * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * T.t * 
         tree * (t, elt) prod * coq_R_remove_min * t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = T.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    type elt = T.t

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
   end) ->
   functor (L:sig
   end) ->
   functor (I:sig
   end) ->
   functor (D:sig
    module Raw :
     sig
      val tree_rect :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_rec :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_caset_nodep :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_rect_nodep :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_rec_nodep :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val lt_tree_dec : T.t -> M.Raw.tree -> sumbool

      val gt_tree_dec : T.t -> M.Raw.tree -> sumbool

      val bst_dec : M.Raw.tree -> sumbool
     end
   end) ->
   functor (MI:sig
    module Raw :
     sig
     end
   end) ->
   struct
    module Raw =
     struct
      (** val tree_dec : M.Raw.tree -> M.Raw.tree -> sumbool **)

      let tree_dec x y =
        D.Raw.tree_rect (fun x0 ->
          match x0 with
          | M.Raw.Leaf -> Coq_left
          | M.Raw.Node (_, _, _, _) -> Coq_right) (fun t0 _ x0 t1 _ x1 x2 ->
          match x2 with
          | M.Raw.Leaf -> Coq_right
          | M.Raw.Node (t2, t3, t4, t5) ->
            (match Z.eq_dec t0 t2 with
             | Coq_left ->
               (match x0 t3 with
                | Coq_left ->
                  (match T.eq_dec t1 t4 with
                   | Coq_left -> x1 t5
                   | Coq_right -> Coq_right)
                | Coq_right -> Coq_right)
             | Coq_right -> Coq_right)) x y

      (** val tree_EqDec : M.Raw.tree coq_EqDec **)

      let tree_EqDec =
        tree_dec

      (** val t_EqDec : M.Raw.t coq_EqDec **)

      let t_EqDec =
        tree_EqDec
     end

    (** val t_dec : M.t -> M.t -> sumbool **)

    let t_dec x y =
      Raw.tree_dec (M.this x) (M.this y)

    (** val t_EqDec : M.t coq_EqDec **)

    let t_EqDec =
      t_dec
   end

  module type DecideWithLeibnizSig =
   functor (T:OrderedType) ->
   functor (M:sig
    module Raw :
     sig
      type elt = T.t

      type tree =
      | Leaf
      | Node of Int.Z_as_Int.t * tree * T.t * tree

      val empty : tree

      val is_empty : tree -> bool

      val mem : T.t -> tree -> bool

      val min_elt : tree -> elt option

      val max_elt : tree -> elt option

      val choose : tree -> elt option

      val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

      val elements_aux : T.t list -> tree -> T.t list

      val elements : tree -> T.t list

      val rev_elements_aux : T.t list -> tree -> T.t list

      val rev_elements : tree -> T.t list

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
        T.t -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_cont :
        tree -> (enumeration -> comparison) -> enumeration -> comparison

      val compare_end : enumeration -> comparison

      val compare : tree -> tree -> comparison

      val equal : tree -> tree -> bool

      val subsetl : (tree -> bool) -> T.t -> tree -> bool

      val subsetr : (tree -> bool) -> T.t -> tree -> bool

      val subset : tree -> tree -> bool

      type t = tree

      val height : t -> Int.Z_as_Int.t

      val singleton : T.t -> tree

      val create : t -> T.t -> t -> tree

      val assert_false : t -> T.t -> t -> tree

      val bal : t -> T.t -> t -> tree

      val add : T.t -> tree -> tree

      val join : tree -> elt -> t -> t

      val remove_min : tree -> elt -> t -> (t, elt) prod

      val merge : tree -> tree -> tree

      val remove : T.t -> tree -> tree

      val concat : tree -> tree -> tree

      type triple = { t_left : t; t_in : bool; t_right : t }

      val t_left : triple -> t

      val t_in : triple -> bool

      val t_right : triple -> t

      val split : T.t -> tree -> triple

      val inter : tree -> tree -> tree

      val diff : tree -> tree -> tree

      val union : tree -> tree -> tree

      val filter : (elt -> bool) -> tree -> tree

      val partition : (elt -> bool) -> t -> (t, t) prod

      val ltb_tree : T.t -> tree -> bool

      val gtb_tree : T.t -> tree -> bool

      val isok : tree -> bool

      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = T.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : T.t -> T.t -> sumbool

        val lt_dec : T.t -> T.t -> sumbool

        val eqb : T.t -> T.t -> bool
       end

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = T.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end

            module TO :
             sig
              type t = OTF.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end
           end

          val eq_dec : T.t -> T.t -> sumbool

          val lt_dec : T.t -> T.t -> sumbool

          val eqb : T.t -> T.t -> bool
         end
       end

      val flatten_e : enumeration -> elt list

      type coq_R_bal =
      | R_bal_0 of t * T.t * t
      | R_bal_1 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_2 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_3 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_4 of t * T.t * t
      | R_bal_5 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_6 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_7 of t * T.t * t * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree
      | R_bal_8 of t * T.t * t

      type coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree * T.t * 
         tree * (t, elt) prod * coq_R_remove_min * t * elt

      type coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * elt

      type coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_inter * tree * coq_R_inter

      type coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_diff * tree * coq_R_diff

      type coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
      | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * T.t * tree
         * Int.Z_as_Int.t * tree * T.t * tree * t * bool * t * tree
         * coq_R_union * tree * coq_R_union
     end

    module E :
     sig
      type t = T.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    type elt = T.t

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
   end) ->
   functor (L:sig
   end) ->
   functor (I:sig
   end) ->
   functor (D:sig
    module Raw :
     sig
      val tree_rect :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_rec :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_caset_nodep :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_rect_nodep :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val tree_rec_nodep :
        'a1 -> (Int.Z_as_Int.t -> M.Raw.tree -> 'a1 -> T.t -> M.Raw.tree ->
        'a1 -> 'a1) -> M.Raw.tree -> 'a1

      val lt_tree_dec : T.t -> M.Raw.tree -> sumbool

      val gt_tree_dec : T.t -> M.Raw.tree -> sumbool

      val bst_dec : M.Raw.tree -> sumbool
     end
   end) ->
   functor (MI:sig
    module Raw :
     sig
     end
   end) ->
   sig
    module Raw :
     sig
      val tree_dec : M.Raw.tree -> M.Raw.tree -> sumbool

      val tree_EqDec : M.Raw.tree coq_EqDec

      val t_EqDec : M.Raw.t coq_EqDec
     end

    val t_dec : M.t -> M.t -> sumbool

    val t_EqDec : M.t coq_EqDec
   end
 end

module MSetList =
 struct
  module type MakeSig =
   functor (T:OrderedType) ->
   sig
    module Raw :
     sig
      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = T.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : T.t -> T.t -> sumbool

        val lt_dec : T.t -> T.t -> sumbool

        val eqb : T.t -> T.t -> bool
       end

      module ML :
       sig
       end

      type elt = T.t

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : T.t -> T.t list -> bool

      val add : T.t -> T.t list -> T.t list

      val singleton : elt -> elt list

      val remove : T.t -> T.t list -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : T.t list -> T.t list -> bool

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

      val compare : T.t list -> T.t list -> comparison

      val inf : T.t -> T.t list -> bool

      val isok : T.t list -> bool

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = T.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end

            module TO :
             sig
              type t = OTF.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end
           end

          val eq_dec : T.t -> T.t -> sumbool

          val lt_dec : T.t -> T.t -> sumbool

          val eqb : T.t -> T.t -> bool
         end
       end
     end

    module E :
     sig
      type t = T.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    type elt = T.t

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

  module type MakeWithLeibnizSig =
   functor (X:OrderedTypeWithLeibniz) ->
   sig
    module E :
     sig
      type t = X.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> sumbool
     end

    module Raw :
     sig
      module MX :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> sumbool
           end
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end

      module ML :
       sig
       end

      type elt = X.t

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : X.t -> X.t list -> bool

      val add : X.t -> X.t list -> X.t list

      val singleton : elt -> elt list

      val remove : X.t -> X.t list -> t

      val union : t -> t -> t

      val inter : t -> t -> t

      val diff : t -> t -> t

      val equal : t -> t -> bool

      val subset : X.t list -> X.t list -> bool

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

      val compare : X.t list -> X.t list -> comparison

      val inf : X.t -> X.t list -> bool

      val isok : X.t list -> bool

      module L :
       sig
        module MO :
         sig
          module OrderTac :
           sig
            module OTF :
             sig
              type t = X.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end

            module TO :
             sig
              type t = OTF.t

              val compare : t -> t -> comparison

              val eq_dec : t -> t -> sumbool
             end
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end
       end
     end

    type elt = X.t

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
 end

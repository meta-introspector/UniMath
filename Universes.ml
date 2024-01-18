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
let __ = let rec f _ = Obj.repr f in Obj.repr f

type valuation = { valuation_mono : (String.t -> positive);
                   valuation_poly : (nat -> nat) }

(** val valuation_mono : valuation -> String.t -> positive **)

let valuation_mono v =
  v.valuation_mono

(** val valuation_poly : valuation -> nat -> nat **)

let valuation_poly v =
  v.valuation_poly

type 'a coq_Evaluable = valuation -> 'a -> nat

(** val coq_val : 'a1 coq_Evaluable -> valuation -> 'a1 -> nat **)

let coq_val evaluable =
  evaluable

module Level =
 struct
  type t_ =
  | Coq_lzero
  | Coq_level of String.t
  | Coq_lvar of nat

  (** val t__rect : 'a1 -> (String.t -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1 **)

  let t__rect f f0 f1 = function
  | Coq_lzero -> f
  | Coq_level t1 -> f0 t1
  | Coq_lvar n -> f1 n

  (** val t__rec : 'a1 -> (String.t -> 'a1) -> (nat -> 'a1) -> t_ -> 'a1 **)

  let t__rec f f0 f1 = function
  | Coq_lzero -> f
  | Coq_level t1 -> f0 t1
  | Coq_lvar n -> f1 n

  (** val coq_NoConfusionPackage_t_ : t_ coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_t_ =
    Build_NoConfusionPackage

  type t = t_

  (** val is_set : t -> bool **)

  let is_set = function
  | Coq_lzero -> Coq_true
  | _ -> Coq_false

  (** val is_var : t -> bool **)

  let is_var = function
  | Coq_lvar _ -> Coq_true
  | _ -> Coq_false

  (** val coq_Evaluable : t coq_Evaluable **)

  let coq_Evaluable v = function
  | Coq_lzero -> O
  | Coq_level s -> Pos.to_nat (v.valuation_mono s)
  | Coq_lvar x -> v.valuation_poly x

  (** val compare : t -> t -> comparison **)

  let compare l1 l2 =
    match l1 with
    | Coq_lzero -> (match l2 with
                    | Coq_lzero -> Eq
                    | _ -> Lt)
    | Coq_level s1 ->
      (match l2 with
       | Coq_lzero -> Gt
       | Coq_level s2 -> StringOT.compare s1 s2
       | Coq_lvar _ -> Lt)
    | Coq_lvar n ->
      (match l2 with
       | Coq_lvar m -> PeanoNat.Nat.compare n m
       | _ -> Gt)

  (** val lt__sig_pack : t -> t -> (t * t) * __ **)

  let lt__sig_pack x x0 =
    (x,x0),__

  (** val lt__Signature : t -> t -> (t * t) * __ **)

  let lt__Signature x x0 =
    (x,x0),__

  (** val eq_level : t_ -> t_ -> bool **)

  let eq_level l1 l2 =
    match l1 with
    | Coq_lzero -> (match l2 with
                    | Coq_lzero -> Coq_true
                    | _ -> Coq_false)
    | Coq_level s1 ->
      (match l2 with
       | Coq_level s2 -> eqb IdentOT.reflect_eq_string s1 s2
       | _ -> Coq_false)
    | Coq_lvar n1 ->
      (match l2 with
       | Coq_lvar n2 -> eqb reflect_nat n1 n2
       | _ -> Coq_false)

  (** val reflect_level : t coq_ReflectEq **)

  let reflect_level =
    eq_level

  (** val eqb : t_ -> t_ -> bool **)

  let eqb =
    eq_level

  (** val eqb_spec : t -> t -> reflect **)

  let eqb_spec l l' =
    reflectProp_reflect (eqb l l')

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    eq_dec (coq_ReflectEq_EqDec reflect_level)
 end

module LevelSet = MSetAVL.Make(Level)

module LevelSetFact = WFactsOn(Level)(LevelSet)

module LevelSetOrdProp = OrdProperties(LevelSet)

module LevelSetProp = LevelSetOrdProp.P

module LevelSetDecide = LevelSetProp.Dec

module LevelSetExtraOrdProp =
 MCMSets.MSets.ExtraOrdProperties(LevelSet)(LevelSetOrdProp)

module LevelSetExtraDecide = MCMSets.MSetAVL.Decide(Level)(LevelSet)

module LS = LevelSet

(** val coq_LevelSet_pair : LevelSet.elt -> LevelSet.elt -> LevelSet.t **)

let coq_LevelSet_pair x y =
  LevelSet.add y (LevelSet.singleton x)

module PropLevel =
 struct
  type t =
  | Coq_lSProp
  | Coq_lProp

  (** val t_rect : 'a1 -> 'a1 -> t -> 'a1 **)

  let t_rect f f0 = function
  | Coq_lSProp -> f
  | Coq_lProp -> f0

  (** val t_rec : 'a1 -> 'a1 -> t -> 'a1 **)

  let t_rec f f0 = function
  | Coq_lSProp -> f
  | Coq_lProp -> f0

  (** val coq_NoConfusionPackage_t : t coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_t =
    Build_NoConfusionPackage

  (** val t_eqdec : t -> t -> t dec_eq **)

  let t_eqdec x y =
    match x with
    | Coq_lSProp ->
      (match y with
       | Coq_lSProp -> Coq_left
       | Coq_lProp -> Coq_right)
    | Coq_lProp ->
      (match y with
       | Coq_lSProp -> Coq_right
       | Coq_lProp -> Coq_left)

  (** val t_EqDec : t coq_EqDec **)

  let t_EqDec =
    t_eqdec

  (** val compare : t -> t -> comparison **)

  let compare l1 l2 =
    match l1 with
    | Coq_lSProp -> (match l2 with
                     | Coq_lSProp -> Eq
                     | Coq_lProp -> Lt)
    | Coq_lProp -> (match l2 with
                    | Coq_lSProp -> Gt
                    | Coq_lProp -> Eq)

  (** val lt__rect : 'a1 -> t -> t -> 'a1 **)

  let lt__rect f _ _ =
    f

  (** val lt__rec : 'a1 -> t -> t -> 'a1 **)

  let lt__rec f _ _ =
    f
 end

module LevelExpr =
 struct
  type t = (Level.t, nat) prod

  (** val coq_Evaluable : t coq_Evaluable **)

  let coq_Evaluable v l =
    add (snd l) (coq_val Level.coq_Evaluable v (fst l))

  (** val succ : t -> (Level.t, nat) prod **)

  let succ l =
    Coq_pair ((fst l), (S (snd l)))

  (** val get_level : t -> Level.t **)

  let get_level =
    fst

  (** val get_noprop : t -> Level.t option **)

  let get_noprop e =
    Some (fst e)

  (** val is_level : t -> bool **)

  let is_level = function
  | Coq_pair (_, n) -> (match n with
                        | O -> Coq_true
                        | S _ -> Coq_false)

  (** val make : Level.t -> t **)

  let make l =
    Coq_pair (l, O)

  (** val set : t **)

  let set =
    Coq_pair (Level.Coq_lzero, O)

  (** val type1 : t **)

  let type1 =
    Coq_pair (Level.Coq_lzero, (S O))

  (** val from_kernel_repr : (Level.t, bool) prod -> t **)

  let from_kernel_repr e =
    Coq_pair ((fst e), (match snd e with
                        | Coq_true -> S O
                        | Coq_false -> O))

  (** val to_kernel_repr : t -> (Level.t, bool) prod **)

  let to_kernel_repr = function
  | Coq_pair (l, b) ->
    Coq_pair (l, (match b with
                  | O -> Coq_false
                  | S _ -> Coq_true))

  (** val compare : t -> t -> comparison **)

  let compare x y =
    let Coq_pair (l1, b1) = x in
    let Coq_pair (l2, b2) = y in
    (match Level.compare l1 l2 with
     | Eq -> PeanoNat.Nat.compare b1 b2
     | x0 -> x0)

  (** val reflect_t : t coq_ReflectEq **)

  let reflect_t =
    reflect_prod Level.reflect_level reflect_nat

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    eq_dec (coq_ReflectEq_EqDec reflect_t)
 end

module LevelExprSet = MakeWithLeibniz(LevelExpr)

module LevelExprSetFact = WFactsOn(LevelExpr)(LevelExprSet)

module LevelExprSetOrdProp = OrdProperties(LevelExprSet)

module LevelExprSetProp = LevelExprSetOrdProp.P

module LevelExprSetDecide = LevelExprSetProp.Dec

module LevelExprSetExtraOrdProp =
 MCMSets.MSets.ExtraOrdProperties(LevelExprSet)(LevelExprSetOrdProp)

(** val levelexprset_reflect : LevelExprSet.t coq_ReflectEq **)

let levelexprset_reflect =
  LevelExprSet.equal

(** val levelexprset_eq_dec : LevelExprSet.t coq_EqDec **)

let levelexprset_eq_dec =
  eq_dec (coq_ReflectEq_EqDec levelexprset_reflect)

type nonEmptyLevelExprSet =
  LevelExprSet.t
  (* singleton inductive, whose constructor was Build_nonEmptyLevelExprSet *)

(** val t_set : nonEmptyLevelExprSet -> LevelExprSet.t **)

let t_set n =
  n

(** val coq_NoConfusionPackage_nonEmptyLevelExprSet :
    nonEmptyLevelExprSet coq_NoConfusionPackage **)

let coq_NoConfusionPackage_nonEmptyLevelExprSet =
  Build_NoConfusionPackage

module NonEmptySetFacts =
 struct
  (** val singleton : LevelExpr.t -> nonEmptyLevelExprSet **)

  let singleton =
    LevelExprSet.singleton

  (** val add :
      LevelExpr.t -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet **)

  let add e u =
    LevelExprSet.add e (t_set u)

  (** val add_list :
      LevelExpr.t list -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet **)

  let add_list =
    fold_left (fun u e -> add e u)

  (** val to_nonempty_list :
      nonEmptyLevelExprSet -> (LevelExpr.t, LevelExpr.t list) prod **)

  let to_nonempty_list u =
    let filtered_var = LevelExprSet.elements (t_set u) in
    (match filtered_var with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (e, l) -> Coq_pair (e, l))

  (** val map :
      (LevelExpr.t -> LevelExpr.t) -> nonEmptyLevelExprSet ->
      nonEmptyLevelExprSet **)

  let map f u =
    let Coq_pair (e, l) = to_nonempty_list u in
    add_list (map f l) (singleton (f e))

  (** val non_empty_union :
      nonEmptyLevelExprSet -> nonEmptyLevelExprSet -> nonEmptyLevelExprSet **)

  let non_empty_union u v =
    LevelExprSet.union (t_set u) (t_set v)
 end

module LevelAlgExpr =
 struct
  type t = nonEmptyLevelExprSet

  (** val levelexprset_reflect : t coq_ReflectEq **)

  let levelexprset_reflect x y =
    eqb levelexprset_reflect (t_set x) (t_set y)

  (** val eq_dec_univ0 : t coq_EqDec **)

  let eq_dec_univ0 =
    eq_dec (coq_ReflectEq_EqDec levelexprset_reflect)

  (** val make : LevelExpr.t -> t **)

  let make =
    NonEmptySetFacts.singleton

  (** val make' : Level.t -> nonEmptyLevelExprSet **)

  let make' l =
    NonEmptySetFacts.singleton (LevelExpr.make l)

  (** val exprs : t -> (LevelExpr.t, LevelExpr.t list) prod **)

  let exprs =
    NonEmptySetFacts.to_nonempty_list

  (** val coq_Evaluable : t coq_Evaluable **)

  let coq_Evaluable v u =
    let Coq_pair (e, u0) = exprs u in
    fold_left (fun n e0 ->
      PeanoNat.Nat.max (coq_val LevelExpr.coq_Evaluable v e0) n) u0
      (coq_val LevelExpr.coq_Evaluable v e)

  (** val is_levels : t -> bool **)

  let is_levels u =
    LevelExprSet.for_all LevelExpr.is_level (t_set u)

  (** val is_level : t -> bool **)

  let is_level u =
    match PeanoNat.Nat.eqb (LevelExprSet.cardinal (t_set u)) (S O) with
    | Coq_true -> is_levels u
    | Coq_false -> Coq_false

  (** val succ : t -> t **)

  let succ =
    NonEmptySetFacts.map LevelExpr.succ

  (** val sup : t -> t -> t **)

  let sup =
    NonEmptySetFacts.non_empty_union

  (** val get_is_level : t -> Level.t option **)

  let get_is_level u =
    match LevelExprSet.elements (t_set u) with
    | Coq_nil -> None
    | Coq_cons (e, l0) ->
      let Coq_pair (l, n) = e in
      (match n with
       | O -> (match l0 with
               | Coq_nil -> Some l
               | Coq_cons (_, _) -> None)
       | S _ -> None)
 end

type concreteUniverses =
| UProp
| USProp
| UType of nat

(** val concreteUniverses_rect :
    'a1 -> 'a1 -> (nat -> 'a1) -> concreteUniverses -> 'a1 **)

let concreteUniverses_rect f f0 f1 = function
| UProp -> f
| USProp -> f0
| UType i -> f1 i

(** val concreteUniverses_rec :
    'a1 -> 'a1 -> (nat -> 'a1) -> concreteUniverses -> 'a1 **)

let concreteUniverses_rec f f0 f1 = function
| UProp -> f
| USProp -> f0
| UType i -> f1 i

(** val coq_NoConfusionPackage_concreteUniverses :
    concreteUniverses coq_NoConfusionPackage **)

let coq_NoConfusionPackage_concreteUniverses =
  Build_NoConfusionPackage

(** val concreteUniverses_eqdec :
    concreteUniverses -> concreteUniverses -> concreteUniverses dec_eq **)

let concreteUniverses_eqdec x y =
  match x with
  | UProp -> (match y with
              | UProp -> Coq_left
              | _ -> Coq_right)
  | USProp -> (match y with
               | USProp -> Coq_left
               | _ -> Coq_right)
  | UType i ->
    (match y with
     | UType i0 -> eq_dec_point i (coq_EqDec_EqDecPoint nat_EqDec i) i0
     | _ -> Coq_right)

(** val concreteUniverses_EqDec : concreteUniverses coq_EqDec **)

let concreteUniverses_EqDec =
  concreteUniverses_eqdec

(** val cuniv_sup :
    concreteUniverses -> concreteUniverses -> concreteUniverses **)

let cuniv_sup u1 u2 =
  match u1 with
  | UProp -> (match u2 with
              | UType _ -> u2
              | _ -> UProp)
  | USProp -> (match u2 with
               | UType _ -> u2
               | x -> x)
  | UType v ->
    (match u2 with
     | UType v' -> UType (PeanoNat.Nat.max v v')
     | _ -> u1)

(** val cuniv_of_product :
    concreteUniverses -> concreteUniverses -> concreteUniverses **)

let cuniv_of_product domsort rangsort = match rangsort with
| UType _ -> cuniv_sup domsort rangsort
| _ -> rangsort

(** val cuniv_sup_not_uproplevel :
    concreteUniverses -> concreteUniverses -> (nat, __) sigT **)

let cuniv_sup_not_uproplevel u u' =
  match u with
  | UType i ->
    (match u' with
     | UType i0 -> Coq_existT ((PeanoNat.Nat.max i i0), __)
     | _ -> Coq_existT (i, __))
  | _ -> assert false (* absurd case *)

type allowed_eliminations =
| IntoSProp
| IntoPropSProp
| IntoSetPropSProp
| IntoAny

(** val allowed_eliminations_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> allowed_eliminations -> 'a1 **)

let allowed_eliminations_rect f f0 f1 f2 = function
| IntoSProp -> f
| IntoPropSProp -> f0
| IntoSetPropSProp -> f1
| IntoAny -> f2

(** val allowed_eliminations_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> allowed_eliminations -> 'a1 **)

let allowed_eliminations_rec f f0 f1 f2 = function
| IntoSProp -> f
| IntoPropSProp -> f0
| IntoSetPropSProp -> f1
| IntoAny -> f2

(** val coq_NoConfusionPackage_allowed_eliminations :
    allowed_eliminations coq_NoConfusionPackage **)

let coq_NoConfusionPackage_allowed_eliminations =
  Build_NoConfusionPackage

(** val allowed_eliminations_eqdec :
    allowed_eliminations -> allowed_eliminations -> allowed_eliminations
    dec_eq **)

let allowed_eliminations_eqdec x y =
  match x with
  | IntoSProp -> (match y with
                  | IntoSProp -> Coq_left
                  | _ -> Coq_right)
  | IntoPropSProp -> (match y with
                      | IntoPropSProp -> Coq_left
                      | _ -> Coq_right)
  | IntoSetPropSProp ->
    (match y with
     | IntoSetPropSProp -> Coq_left
     | _ -> Coq_right)
  | IntoAny -> (match y with
                | IntoAny -> Coq_left
                | _ -> Coq_right)

(** val allowed_eliminations_EqDec : allowed_eliminations coq_EqDec **)

let allowed_eliminations_EqDec =
  allowed_eliminations_eqdec

module Universe =
 struct
  type t_ =
  | Coq_lProp
  | Coq_lSProp
  | Coq_lType of LevelAlgExpr.t

  (** val t__rect : 'a1 -> 'a1 -> (LevelAlgExpr.t -> 'a1) -> t_ -> 'a1 **)

  let t__rect f f0 f1 = function
  | Coq_lProp -> f
  | Coq_lSProp -> f0
  | Coq_lType t1 -> f1 t1

  (** val t__rec : 'a1 -> 'a1 -> (LevelAlgExpr.t -> 'a1) -> t_ -> 'a1 **)

  let t__rec f f0 f1 = function
  | Coq_lProp -> f
  | Coq_lSProp -> f0
  | Coq_lType t1 -> f1 t1

  (** val coq_NoConfusionPackage_t_ : t_ coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_t_ =
    Build_NoConfusionPackage

  module Coq__1 = struct
   type t = t_
  end
  include Coq__1

  (** val eqb : t -> t -> bool **)

  let eqb u1 u2 =
    match u1 with
    | Coq_lProp -> (match u2 with
                    | Coq_lProp -> Coq_true
                    | _ -> Coq_false)
    | Coq_lSProp -> (match u2 with
                     | Coq_lSProp -> Coq_true
                     | _ -> Coq_false)
    | Coq_lType e1 ->
      (match u2 with
       | Coq_lType e2 -> eqb LevelAlgExpr.levelexprset_reflect e1 e2
       | _ -> Coq_false)

  (** val reflect_eq_universe : t coq_ReflectEq **)

  let reflect_eq_universe =
    eqb

  (** val eq_dec_univ : t coq_EqDec **)

  let eq_dec_univ =
    eq_dec (coq_ReflectEq_EqDec reflect_eq_universe)

  (** val make : Level.t -> t **)

  let make l =
    Coq_lType (LevelAlgExpr.make (LevelExpr.make l))

  (** val of_expr : LevelExpr.t -> t_ **)

  let of_expr e =
    Coq_lType (LevelAlgExpr.make e)

  (** val add_to_exprs : LevelExpr.t -> t -> t **)

  let add_to_exprs e u = match u with
  | Coq_lType l -> Coq_lType (NonEmptySetFacts.add e l)
  | _ -> u

  (** val add_list_to_exprs : LevelExpr.t list -> t -> t **)

  let add_list_to_exprs es u = match u with
  | Coq_lType l -> Coq_lType (NonEmptySetFacts.add_list es l)
  | _ -> u

  (** val is_levels : t -> bool **)

  let is_levels = function
  | Coq_lType l -> LevelAlgExpr.is_levels l
  | _ -> Coq_true

  (** val is_level : t -> bool **)

  let is_level = function
  | Coq_lType l -> LevelAlgExpr.is_level l
  | _ -> Coq_true

  (** val is_sprop : t -> bool **)

  let is_sprop = function
  | Coq_lSProp -> Coq_true
  | _ -> Coq_false

  (** val is_prop : t -> bool **)

  let is_prop = function
  | Coq_lProp -> Coq_true
  | _ -> Coq_false

  (** val is_type_sort : t -> bool **)

  let is_type_sort = function
  | Coq_lType _ -> Coq_true
  | _ -> Coq_false

  (** val type0 : t **)

  let type0 =
    make Level.Coq_lzero

  (** val type1 : t **)

  let type1 =
    Coq_lType (LevelAlgExpr.make LevelExpr.type1)

  (** val of_levels : (PropLevel.t, Level.t) sum -> t **)

  let of_levels = function
  | Coq_inl t0 ->
    (match t0 with
     | PropLevel.Coq_lSProp -> Coq_lSProp
     | PropLevel.Coq_lProp -> Coq_lProp)
  | Coq_inr l0 -> Coq_lType (LevelAlgExpr.make' l0)

  (** val from_kernel_repr :
      (Level.t, bool) prod -> (Level.t, bool) prod list -> t **)

  let from_kernel_repr e es =
    Coq_lType
      (NonEmptySetFacts.add_list (map LevelExpr.from_kernel_repr es)
        (LevelAlgExpr.make (LevelExpr.from_kernel_repr e)))

  (** val super : t -> t **)

  let super = function
  | Coq_lType l0 -> Coq_lType (LevelAlgExpr.succ l0)
  | _ -> type1

  (** val sup : t -> t -> t **)

  let sup u v =
    match u with
    | Coq_lProp -> (match v with
                    | Coq_lSProp -> Coq_lProp
                    | _ -> v)
    | Coq_lSProp -> (match v with
                     | Coq_lProp -> Coq_lProp
                     | _ -> v)
    | Coq_lType l1 ->
      (match v with
       | Coq_lType l2 -> Coq_lType (LevelAlgExpr.sup l1 l2)
       | _ -> u)

  (** val get_univ_exprs : t -> LevelAlgExpr.t **)

  let get_univ_exprs = function
  | Coq_lType t0 -> t0
  | _ -> assert false (* absurd case *)

  (** val sort_of_product : t -> t -> t **)

  let sort_of_product domsort rangsort =
    match match is_prop rangsort with
          | Coq_true -> Coq_true
          | Coq_false -> is_sprop rangsort with
    | Coq_true -> rangsort
    | Coq_false -> sup domsort rangsort

  (** val get_is_level : t -> Level.t option **)

  let get_is_level = function
  | Coq_lType l -> LevelAlgExpr.get_is_level l
  | _ -> None

  (** val to_cuniv : valuation -> t_ -> concreteUniverses **)

  let to_cuniv v = function
  | Coq_lProp -> UProp
  | Coq_lSProp -> USProp
  | Coq_lType l -> UType (coq_val LevelAlgExpr.coq_Evaluable v l)

  (** val lt__sig_pack : t -> t -> (t * t) * __ **)

  let lt__sig_pack x x0 =
    (x,x0),__

  (** val lt__Signature : t -> t -> (t * t) * __ **)

  let lt__Signature x x0 =
    (x,x0),__

  module OT =
   struct
    type t = Coq__1.t

    (** val compare : t -> t -> comparison **)

    let compare x y =
      match x with
      | Coq_lProp -> (match y with
                      | Coq_lProp -> Eq
                      | _ -> Lt)
      | Coq_lSProp ->
        (match y with
         | Coq_lProp -> Gt
         | Coq_lSProp -> Eq
         | Coq_lType _ -> Lt)
      | Coq_lType x0 ->
        (match y with
         | Coq_lType y0 -> LevelExprSet.compare (t_set x0) (t_set y0)
         | _ -> Gt)

    (** val eq_dec : t -> t -> sumbool **)

    let eq_dec x y =
      match x with
      | Coq_lProp -> (match y with
                      | Coq_lProp -> Coq_left
                      | _ -> Coq_right)
      | Coq_lSProp -> (match y with
                       | Coq_lSProp -> Coq_left
                       | _ -> Coq_right)
      | Coq_lType t0 ->
        (match y with
         | Coq_lType t1 -> LevelAlgExpr.eq_dec_univ0 t0 t1
         | _ -> Coq_right)
   end

  module OTOrig = Backport_OT(OT)
 end

module UniverseMap = FMapAVL.Make(Universe.OTOrig)

module UniverseMapFact = FMapFacts.WProperties(UniverseMap)

module UniverseMapExtraFact =
 MCFSets.FSets.WFactsExtra_fun(Universe.OTOrig)(UniverseMap)(UniverseMapFact.F)

module UniverseMapDecide =
 MCFSets.FMapAVL.Decide(Universe.OTOrig)(UniverseMap)

(** val is_propositional : Universe.t -> bool **)

let is_propositional u =
  match Universe.is_prop u with
  | Coq_true -> Coq_true
  | Coq_false -> Universe.is_sprop u

(** val is_prop_and_is_sprop_val_false :
    Universe.t -> valuation -> (nat, __) sigT **)

let is_prop_and_is_sprop_val_false u v =
  match u with
  | Universe.Coq_lType t0 ->
    Coq_existT ((coq_val LevelAlgExpr.coq_Evaluable v t0), __)
  | _ -> assert false (* absurd case *)

(** val is_not_prop_and_is_not_sprop :
    Universe.t -> (LevelAlgExpr.t, __) sigT **)

let is_not_prop_and_is_not_sprop = function
| Universe.Coq_lType t0 -> Coq_existT (t0, __)
| _ -> assert false (* absurd case *)

module ConstraintType =
 struct
  type t_ =
  | Le of coq_Z
  | Eq

  (** val t__rect : (coq_Z -> 'a1) -> 'a1 -> t_ -> 'a1 **)

  let t__rect f f0 = function
  | Le z -> f z
  | Eq -> f0

  (** val t__rec : (coq_Z -> 'a1) -> 'a1 -> t_ -> 'a1 **)

  let t__rec f f0 = function
  | Le z -> f z
  | Eq -> f0

  (** val coq_NoConfusionPackage_t_ : t_ coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_t_ =
    Build_NoConfusionPackage

  (** val t__eqdec : t_ -> t_ -> t_ dec_eq **)

  let t__eqdec x y =
    match x with
    | Le z ->
      (match y with
       | Le z0 -> eq_dec_point z (coq_EqDec_EqDecPoint coq_Z_EqDec z) z0
       | Eq -> Coq_right)
    | Eq -> (match y with
             | Le _ -> Coq_right
             | Eq -> Coq_left)

  (** val t__EqDec : t_ coq_EqDec **)

  let t__EqDec =
    t__eqdec

  type t = t_

  (** val coq_Le0 : t_ **)

  let coq_Le0 =
    Le Z0

  (** val coq_Lt : t_ **)

  let coq_Lt =
    Le (Zpos Coq_xH)

  (** val lt__sig_pack : t -> t -> (t * t) * __ **)

  let lt__sig_pack x x0 =
    (x,x0),__

  (** val lt__Signature : t -> t -> (t * t) * __ **)

  let lt__Signature x x0 =
    (x,x0),__

  (** val compare : t -> t -> comparison **)

  let compare x y =
    match x with
    | Le n -> (match y with
               | Le m -> Z.compare n m
               | Eq -> Lt)
    | Eq -> (match y with
             | Le _ -> Gt
             | Eq -> Datatypes.Eq)

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec x y =
    match x with
    | Le z -> (match y with
               | Le z0 -> Z.eq_dec z z0
               | Eq -> Coq_right)
    | Eq -> (match y with
             | Le _ -> Coq_right
             | Eq -> Coq_left)
 end

module UnivConstraint =
 struct
  type t = ((Level.t, ConstraintType.t) prod, Level.t) prod

  (** val make : Level.t -> ConstraintType.t -> Level.t -> t **)

  let make l1 ct l2 =
    Coq_pair ((Coq_pair (l1, ct)), l2)

  (** val compare : t -> t -> comparison **)

  let compare pat pat0 =
    let Coq_pair (p, l2) = pat in
    let Coq_pair (l1, t0) = p in
    let Coq_pair (p0, l2') = pat0 in
    let Coq_pair (l1', t') = p0 in
    (match Level.compare l1 l1' with
     | Eq ->
       (match ConstraintType.compare t0 t' with
        | Eq -> Level.compare l2 l2'
        | x -> x)
     | x -> x)

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec x y =
    let Coq_pair (a, b) = x in
    let Coq_pair (p, t0) = y in
    (match eq_dec
             (prod_eqdec (coq_ReflectEq_EqDec Level.reflect_level)
               ConstraintType.t__EqDec) a p with
     | Coq_left -> eq_dec (coq_ReflectEq_EqDec Level.reflect_level) b t0
     | Coq_right -> Coq_right)
 end

module ConstraintSet = MSetAVL.Make(UnivConstraint)

module ConstraintSetFact = WFactsOn(UnivConstraint)(ConstraintSet)

module ConstraintSetOrdProp = OrdProperties(ConstraintSet)

module ConstraintSetProp = ConstraintSetOrdProp.P

module CS = ConstraintSet

module ConstraintSetDecide = ConstraintSetProp.Dec

module ConstraintSetExtraOrdProp =
 MCMSets.MSets.ExtraOrdProperties(ConstraintSet)(ConstraintSetOrdProp)

module ConstraintSetExtraDecide =
 MCMSets.MSetAVL.Decide(UnivConstraint)(ConstraintSet)

(** val is_declared_cstr_levels : LevelSet.t -> UnivConstraint.t -> bool **)

let is_declared_cstr_levels levels0 = function
| Coq_pair (p, l2) ->
  let Coq_pair (l1, _) = p in
  (match LevelSet.mem l1 levels0 with
   | Coq_true -> LevelSet.mem l2 levels0
   | Coq_false -> Coq_false)

module Instance =
 struct
  type t = Level.t list

  (** val empty : t **)

  let empty =
    Coq_nil

  (** val is_empty : t -> bool **)

  let is_empty = function
  | Coq_nil -> Coq_true
  | Coq_cons (_, _) -> Coq_false

  (** val eqb : t -> t -> bool **)

  let eqb i j =
    forallb2 Level.eqb i j

  (** val equal_upto : (Level.t -> Level.t -> bool) -> t -> t -> bool **)

  let equal_upto =
    forallb2
 end

module UContext =
 struct
  type t = (name list, (Instance.t, ConstraintSet.t) prod) prod

  (** val make' :
      Instance.t -> ConstraintSet.t -> (Instance.t, ConstraintSet.t) prod **)

  let make' x x0 =
    Coq_pair (x, x0)

  (** val make : name list -> (Instance.t, ConstraintSet.t) prod -> t **)

  let make ids inst_ctrs =
    Coq_pair (ids, inst_ctrs)

  (** val empty : t **)

  let empty =
    Coq_pair (Coq_nil, (Coq_pair (Instance.empty, ConstraintSet.empty)))

  (** val instance : t -> Instance.t **)

  let instance x =
    fst (snd x)

  (** val constraints : t -> ConstraintSet.t **)

  let constraints x =
    snd (snd x)

  (** val dest : t -> (name list, (Instance.t, ConstraintSet.t) prod) prod **)

  let dest x =
    x
 end

module AUContext =
 struct
  type t = (name list, ConstraintSet.t) prod

  (** val make : name list -> ConstraintSet.t -> t **)

  let make ids ctrs =
    Coq_pair (ids, ctrs)

  (** val repr : t -> UContext.t **)

  let repr = function
  | Coq_pair (u, cst) ->
    Coq_pair (u, (Coq_pair ((mapi (fun i _ -> Level.Coq_lvar i) u), cst)))

  (** val levels : t -> LevelSet.t **)

  let levels uctx =
    LevelSetProp.of_list (fst (snd (repr uctx)))

  (** val inter : t -> t -> t **)

  let inter au av =
    let prefix =
      fst
        (fst
          (split_prefix (coq_EqDec_ReflectEq name_EqDec) (fst au) (fst av)))
    in
    let lvls =
      fold_left_i (fun s i _ -> LevelSet.add (Level.Coq_lvar i) s) prefix
        LevelSet.empty
    in
    let filter0 = ConstraintSet.filter (is_declared_cstr_levels lvls) in
    make prefix (ConstraintSet.union (filter0 (snd au)) (filter0 (snd av)))
 end

module ContextSet =
 struct
  type t = (LevelSet.t, ConstraintSet.t) prod

  (** val levels : t -> LevelSet.t **)

  let levels =
    fst

  (** val constraints : t -> ConstraintSet.t **)

  let constraints =
    snd

  (** val empty : t **)

  let empty =
    Coq_pair (LevelSet.empty, ConstraintSet.empty)

  (** val is_empty : t -> bool **)

  let is_empty uctx =
    match LevelSet.is_empty (fst uctx) with
    | Coq_true -> ConstraintSet.is_empty (snd uctx)
    | Coq_false -> Coq_false

  (** val equal : t -> t -> bool **)

  let equal x y =
    match LevelSet.equal (fst x) (fst y) with
    | Coq_true -> ConstraintSet.equal (snd x) (snd y)
    | Coq_false -> Coq_false

  (** val subset : t -> t -> bool **)

  let subset x y =
    match LevelSet.subset (levels x) (levels y) with
    | Coq_true -> ConstraintSet.subset (constraints x) (constraints y)
    | Coq_false -> Coq_false

  (** val inter : t -> t -> t **)

  let inter x y =
    Coq_pair ((LevelSet.inter (levels x) (levels y)),
      (ConstraintSet.inter (constraints x) (constraints y)))

  (** val union : t -> t -> t **)

  let union x y =
    Coq_pair ((LevelSet.union (levels x) (levels y)),
      (ConstraintSet.union (constraints x) (constraints y)))

  (** val subsetP : t -> t -> reflect **)

  let subsetP s s' =
    let b = subset s s' in
    (match b with
     | Coq_true -> ReflectT
     | Coq_false -> ReflectF)
 end

module Variance =
 struct
  type t =
  | Irrelevant
  | Covariant
  | Invariant

  (** val t_rect : 'a1 -> 'a1 -> 'a1 -> t -> 'a1 **)

  let t_rect f f0 f1 = function
  | Irrelevant -> f
  | Covariant -> f0
  | Invariant -> f1

  (** val t_rec : 'a1 -> 'a1 -> 'a1 -> t -> 'a1 **)

  let t_rec f f0 f1 = function
  | Irrelevant -> f
  | Covariant -> f0
  | Invariant -> f1

  (** val coq_NoConfusionPackage_t : t coq_NoConfusionPackage **)

  let coq_NoConfusionPackage_t =
    Build_NoConfusionPackage

  (** val t_eqdec : t -> t -> t dec_eq **)

  let t_eqdec x y =
    match x with
    | Irrelevant -> (match y with
                     | Irrelevant -> Coq_left
                     | _ -> Coq_right)
    | Covariant -> (match y with
                    | Covariant -> Coq_left
                    | _ -> Coq_right)
    | Invariant -> (match y with
                    | Invariant -> Coq_left
                    | _ -> Coq_right)

  (** val t_EqDec : t coq_EqDec **)

  let t_EqDec =
    t_eqdec
 end

type universes_decl =
| Monomorphic_ctx
| Polymorphic_ctx of AUContext.t

(** val universes_decl_rect :
    'a1 -> (AUContext.t -> 'a1) -> universes_decl -> 'a1 **)

let universes_decl_rect f f0 = function
| Monomorphic_ctx -> f
| Polymorphic_ctx cst -> f0 cst

(** val universes_decl_rec :
    'a1 -> (AUContext.t -> 'a1) -> universes_decl -> 'a1 **)

let universes_decl_rec f f0 = function
| Monomorphic_ctx -> f
| Polymorphic_ctx cst -> f0 cst

(** val coq_NoConfusionPackage_universes_decl :
    universes_decl coq_NoConfusionPackage **)

let coq_NoConfusionPackage_universes_decl =
  Build_NoConfusionPackage

(** val levels_of_udecl : universes_decl -> LevelSet.t **)

let levels_of_udecl = function
| Monomorphic_ctx -> LevelSet.empty
| Polymorphic_ctx ctx -> AUContext.levels ctx

(** val constraints_of_udecl : universes_decl -> ConstraintSet.t **)

let constraints_of_udecl = function
| Monomorphic_ctx -> ConstraintSet.empty
| Polymorphic_ctx ctx -> snd (snd (AUContext.repr ctx))

(** val leqb_universe_n_ :
    checker_flags -> (bool -> LevelAlgExpr.t -> LevelAlgExpr.t -> bool) ->
    bool -> Universe.t_ -> Universe.t_ -> bool **)

let leqb_universe_n_ cf leqb_levelalg_n b s s' =
  match s with
  | Universe.Coq_lProp ->
    (match s' with
     | Universe.Coq_lProp -> negb b
     | Universe.Coq_lSProp -> Coq_false
     | Universe.Coq_lType _ -> cf.prop_sub_type)
  | Universe.Coq_lSProp ->
    (match s' with
     | Universe.Coq_lSProp -> negb b
     | _ -> Coq_false)
  | Universe.Coq_lType u ->
    (match s' with
     | Universe.Coq_lType u' -> leqb_levelalg_n b u u'
     | _ -> Coq_false)

(** val allowed_eliminations_subset :
    allowed_eliminations -> allowed_eliminations -> bool **)

let allowed_eliminations_subset a a' =
  match a with
  | IntoSProp -> Coq_true
  | IntoPropSProp -> (match a' with
                      | IntoSProp -> Coq_false
                      | _ -> Coq_true)
  | IntoSetPropSProp ->
    (match a' with
     | IntoSProp -> Coq_false
     | IntoPropSProp -> Coq_false
     | _ -> Coq_true)
  | IntoAny -> (match a' with
                | IntoAny -> Coq_true
                | _ -> Coq_false)

(** val fresh_level : Level.t **)

let fresh_level =
  Level.Coq_level (String.String (Coq_x5f, (String.String (Coq_x5f,
    (String.String (Coq_x6d, (String.String (Coq_x65, (String.String
    (Coq_x74, (String.String (Coq_x61, (String.String (Coq_x63,
    (String.String (Coq_x6f, (String.String (Coq_x71, (String.String
    (Coq_x5f, (String.String (Coq_x66, (String.String (Coq_x72,
    (String.String (Coq_x65, (String.String (Coq_x73, (String.String
    (Coq_x68, (String.String (Coq_x5f, (String.String (Coq_x6c,
    (String.String (Coq_x65, (String.String (Coq_x76, (String.String
    (Coq_x65, (String.String (Coq_x6c, (String.String (Coq_x5f,
    (String.String (Coq_x5f,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))

(** val fresh_universe : Universe.t **)

let fresh_universe =
  Universe.make fresh_level

type 'a coq_UnivSubst = Instance.t -> 'a -> 'a

(** val subst_instance : 'a1 coq_UnivSubst -> Instance.t -> 'a1 -> 'a1 **)

let subst_instance univSubst =
  univSubst

(** val subst_instance_level : Level.t coq_UnivSubst **)

let subst_instance_level u l = match l with
| Level.Coq_lvar n -> nth n u Level.Coq_lzero
| _ -> l

(** val subst_instance_cstr : UnivConstraint.t coq_UnivSubst **)

let subst_instance_cstr u c =
  Coq_pair ((Coq_pair ((subst_instance_level u (fst (fst c))),
    (snd (fst c)))), (subst_instance_level u (snd c)))

(** val subst_instance_cstrs : ConstraintSet.t coq_UnivSubst **)

let subst_instance_cstrs u ctrs =
  ConstraintSet.fold (fun c -> ConstraintSet.add (subst_instance_cstr u c))
    ctrs ConstraintSet.empty

(** val subst_instance_level_expr : LevelExpr.t coq_UnivSubst **)

let subst_instance_level_expr u e = match e with
| Coq_pair (t0, b) ->
  (match t0 with
   | Level.Coq_lvar n ->
     (match nth_error u n with
      | Some l -> Coq_pair (l, b)
      | None -> Coq_pair (Level.Coq_lzero, b))
   | _ -> e)

(** val subst_instance_univ0 : LevelAlgExpr.t coq_UnivSubst **)

let subst_instance_univ0 u =
  NonEmptySetFacts.map (subst_instance_level_expr u)

(** val subst_instance_univ : Universe.t coq_UnivSubst **)

let subst_instance_univ u e = match e with
| Universe.Coq_lType l ->
  Universe.Coq_lType (subst_instance subst_instance_univ0 u l)
| _ -> e

(** val subst_instance_instance : Instance.t coq_UnivSubst **)

let subst_instance_instance u u' =
  map (subst_instance_level u) u'

(** val closedu_level : nat -> Level.t -> bool **)

let closedu_level k = function
| Level.Coq_lvar n -> PeanoNat.Nat.ltb n k
| _ -> Coq_true

(** val closedu_level_expr : nat -> LevelExpr.t -> bool **)

let closedu_level_expr k s =
  closedu_level k (LevelExpr.get_level s)

(** val closedu_universe_levels : nat -> LevelAlgExpr.t -> bool **)

let closedu_universe_levels k u =
  LevelExprSet.for_all (closedu_level_expr k) (t_set u)

(** val closedu_universe : nat -> Universe.t -> bool **)

let closedu_universe k = function
| Universe.Coq_lType l -> closedu_universe_levels k l
| _ -> Coq_true

(** val closedu_instance : nat -> Instance.t -> bool **)

let closedu_instance k u =
  forallb (closedu_level k) u

(** val string_of_level : Level.t -> String.t **)

let string_of_level = function
| Level.Coq_lzero ->
  String.String (Coq_x53, (String.String (Coq_x65, (String.String (Coq_x74,
    String.EmptyString)))))
| Level.Coq_level s -> s
| Level.Coq_lvar n ->
  String.append (String.String (Coq_x6c, (String.String (Coq_x76,
    (String.String (Coq_x61, (String.String (Coq_x72,
    String.EmptyString)))))))) (string_of_nat n)

(** val string_of_level_expr : LevelExpr.t -> String.t **)

let string_of_level_expr = function
| Coq_pair (l, n) ->
  String.append (string_of_level l)
    (match n with
     | O -> String.EmptyString
     | S _ ->
       String.append (String.String (Coq_x2b, String.EmptyString))
         (string_of_nat n))

(** val string_of_sort : Universe.t -> String.t **)

let string_of_sort = function
| Universe.Coq_lProp ->
  String.String (Coq_x50, (String.String (Coq_x72, (String.String (Coq_x6f,
    (String.String (Coq_x70, String.EmptyString)))))))
| Universe.Coq_lSProp ->
  String.String (Coq_x53, (String.String (Coq_x50, (String.String (Coq_x72,
    (String.String (Coq_x6f, (String.String (Coq_x70,
    String.EmptyString)))))))))
| Universe.Coq_lType l ->
  String.append (String.String (Coq_x54, (String.String (Coq_x79,
    (String.String (Coq_x70, (String.String (Coq_x65, (String.String
    (Coq_x28, String.EmptyString))))))))))
    (String.append
      (string_of_list string_of_level_expr (LevelExprSet.elements (t_set l)))
      (String.String (Coq_x29, String.EmptyString)))

(** val string_of_universe_instance : Level.t list -> String.t **)

let string_of_universe_instance u =
  string_of_list string_of_level u

type universes_entry =
| Monomorphic_entry of ContextSet.t
| Polymorphic_entry of UContext.t

(** val universes_entry_rect :
    (ContextSet.t -> 'a1) -> (UContext.t -> 'a1) -> universes_entry -> 'a1 **)

let universes_entry_rect f f0 = function
| Monomorphic_entry ctx -> f ctx
| Polymorphic_entry ctx -> f0 ctx

(** val universes_entry_rec :
    (ContextSet.t -> 'a1) -> (UContext.t -> 'a1) -> universes_entry -> 'a1 **)

let universes_entry_rec f f0 = function
| Monomorphic_entry ctx -> f ctx
| Polymorphic_entry ctx -> f0 ctx

(** val coq_NoConfusionPackage_universes_entry :
    universes_entry coq_NoConfusionPackage **)

let coq_NoConfusionPackage_universes_entry =
  Build_NoConfusionPackage

(** val universes_entry_of_decl : universes_decl -> universes_entry **)

let universes_entry_of_decl = function
| Monomorphic_ctx -> Monomorphic_entry ContextSet.empty
| Polymorphic_ctx ctx -> Polymorphic_entry (AUContext.repr ctx)

(** val polymorphic_instance : universes_decl -> Instance.t **)

let polymorphic_instance = function
| Monomorphic_ctx -> Instance.empty
| Polymorphic_ctx c -> fst (snd (AUContext.repr c))

(** val abstract_instance : universes_decl -> Instance.t **)

let abstract_instance = function
| Monomorphic_ctx -> Instance.empty
| Polymorphic_ctx auctx -> UContext.instance (AUContext.repr auctx)

(** val print_universe_instance : Level.t list -> String.t **)

let print_universe_instance u = match u with
| Coq_nil -> String.EmptyString
| Coq_cons (_, _) ->
  String.append (String.String (Coq_x40, (String.String (Coq_x7b,
    String.EmptyString))))
    (String.append
      (print_list string_of_level (String.String (Coq_x20,
        String.EmptyString)) u) (String.String (Coq_x7d, String.EmptyString)))

(** val print_lset : LevelSet.t -> String.t **)

let print_lset t0 =
  print_list string_of_level (String.String (Coq_x20, String.EmptyString))
    (LevelSet.elements t0)

(** val print_constraint_type : ConstraintType.t_ -> String.t **)

let print_constraint_type = function
| ConstraintType.Le n ->
  (match Z.eqb n Z0 with
   | Coq_true ->
     String.String (Coq_x3c, (String.String (Coq_x3d, String.EmptyString)))
   | Coq_false ->
     (match Z.eqb n (Zpos Coq_xH) with
      | Coq_true -> String.String (Coq_x3c, String.EmptyString)
      | Coq_false ->
        (match Z.ltb n Z0 with
         | Coq_true ->
           String.append (String.String (Coq_x3c, (String.String (Coq_x3d,
             String.EmptyString))))
             (String.append (string_of_nat (Z.to_nat (Z.abs n)))
               (String.String (Coq_x20, (String.String (Coq_x2b,
               (String.String (Coq_x20, String.EmptyString)))))))
         | Coq_false ->
           String.append (String.String (Coq_x20, (String.String (Coq_x2b,
             (String.String (Coq_x20, String.EmptyString))))))
             (String.append (string_of_nat (Z.to_nat n)) (String.String
               (Coq_x20, (String.String (Coq_x3c, (String.String (Coq_x3d,
               (String.String (Coq_x20, String.EmptyString))))))))))))
| ConstraintType.Eq -> String.String (Coq_x3d, String.EmptyString)

(** val print_constraint_set : ConstraintSet.t -> String.t **)

let print_constraint_set t0 =
  print_list (fun pat ->
    let Coq_pair (y, l2) = pat in
    let Coq_pair (l1, d) = y in
    String.append (string_of_level l1)
      (String.append (String.String (Coq_x20, String.EmptyString))
        (String.append (print_constraint_type d)
          (String.append (String.String (Coq_x20, String.EmptyString))
            (string_of_level l2))))) (String.String (Coq_x20, (String.String
    (Coq_x2f, (String.String (Coq_x5c, (String.String (Coq_x20,
    String.EmptyString)))))))) (ConstraintSet.elements t0)

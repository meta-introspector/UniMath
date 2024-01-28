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

(** val compare_ident : String.t -> String.t -> comparison **)

let compare_ident =
  StringOT.compare

type ident = String.t

type qualid = String.t

type dirpath = ident list

module IdentOT = StringOT

module IdentOTOrig = OrdersAlt.Backport_OT(IdentOT)

module IdentSet = Make(IdentOT)

module IdentSetFact = WFactsOn(IdentOT)(IdentSet)

module IdentSetOrdProp = OrdProperties(IdentSet)

module IdentSetProp = IdentSetOrdProp.P

module IdentSetDecide = IdentSetProp.Dec

module IdentSetExtraOrdProp =
 MCMSets.MSets.ExtraOrdProperties(IdentSet)(IdentSetOrdProp)

module IdentSetExtraDecide = MCMSets.MSetAVL.Decide(IdentOT)(IdentSet)

module IdentMap = FMapAVL.Make(IdentOTOrig)

module IdentMapFact = FMapFacts.WProperties(IdentMap)

module IdentMapExtraFact =
 MCFSets.FSets.WFactsExtra_fun(IdentOTOrig)(IdentMap)(IdentMapFact.F)

module IdentMapDecide = MCFSets.FMapAVL.Decide(IdentOTOrig)(IdentMap)

module DirPathOT = ListOrderedType(IdentOT)

module DirPathOTOrig = OrdersAlt.Backport_OT(DirPathOT)

module DirPathSet = Make(DirPathOT)

module DirPathSetFact = WFactsOn(DirPathOT)(DirPathSet)

module DirPathSetOrdProp = OrdProperties(DirPathSet)

module DirPathSetProp = DirPathSetOrdProp.P

module DirPathSetDecide = DirPathSetProp.Dec

module DirPathSetExtraOrdProp =
 MCMSets.MSets.ExtraOrdProperties(DirPathSet)(DirPathSetOrdProp)

module DirPathSetExtraDecide = MCMSets.MSetAVL.Decide(DirPathOT)(DirPathSet)

module DirPathMap = FMapAVL.Make(DirPathOTOrig)

module DirPathMapFact = FMapFacts.WProperties(DirPathMap)

module DirPathMapExtraFact =
 MCFSets.FSets.WFactsExtra_fun(DirPathOTOrig)(DirPathMap)(DirPathMapFact.F)

module DirPathMapDecide = MCFSets.FMapAVL.Decide(DirPathOTOrig)(DirPathMap)

(** val dirpath_eqdec : dirpath coq_EqDec **)

let dirpath_eqdec =
  DirPathOT.eq_dec

(** val string_of_dirpath : dirpath -> String.t **)

let string_of_dirpath dp =
  String.concat (String.String (Coq_x2e, String.EmptyString)) (rev dp)

type modpath =
| MPfile of dirpath
| MPbound of dirpath * ident * nat
| MPdot of modpath * ident

(** val modpath_rect :
    (dirpath -> 'a1) -> (dirpath -> ident -> nat -> 'a1) -> (modpath -> 'a1
    -> ident -> 'a1) -> modpath -> 'a1 **)

let rec modpath_rect f f0 f1 = function
| MPfile dp -> f dp
| MPbound (dp, id, i) -> f0 dp id i
| MPdot (mp, id) -> f1 mp (modpath_rect f f0 f1 mp) id

(** val modpath_rec :
    (dirpath -> 'a1) -> (dirpath -> ident -> nat -> 'a1) -> (modpath -> 'a1
    -> ident -> 'a1) -> modpath -> 'a1 **)

let rec modpath_rec f f0 f1 = function
| MPfile dp -> f dp
| MPbound (dp, id, i) -> f0 dp id i
| MPdot (mp, id) -> f1 mp (modpath_rec f f0 f1 mp) id

(** val coq_NoConfusionPackage_modpath : modpath coq_NoConfusionPackage **)

let coq_NoConfusionPackage_modpath =
  Build_NoConfusionPackage

(** val string_of_modpath : modpath -> String.t **)

let rec string_of_modpath = function
| MPfile dp -> string_of_dirpath dp
| MPbound (dp, id, n) ->
  String.append (string_of_dirpath dp)
    (String.append (String.String (Coq_x2e, String.EmptyString))
      (String.append id
        (String.append (String.String (Coq_x2e, String.EmptyString))
          (string_of_nat n))))
| MPdot (mp0, id) ->
  String.append (string_of_modpath mp0)
    (String.append (String.String (Coq_x2e, String.EmptyString)) id)

type kername = (modpath, ident) prod

(** val string_of_kername : kername -> String.t **)

let string_of_kername kn =
  String.append (string_of_modpath (fst kn))
    (String.append (String.String (Coq_x2e, String.EmptyString)) (snd kn))

module ModPathComp =
 struct
  type t = modpath

  (** val mpbound_compare :
      DirPathOT.t -> String.t -> nat -> DirPathOT.t -> String.t -> nat ->
      comparison **)

  let mpbound_compare dp id k dp' id' k' =
    match DirPathOT.compare dp dp' with
    | Eq ->
      (match IdentOT.compare id id' with
       | Eq -> Nat.compare k k'
       | x -> x)
    | x -> x

  (** val compare : modpath -> modpath -> comparison **)

  let rec compare mp mp' =
    match mp with
    | MPfile dp ->
      (match mp' with
       | MPfile dp' -> DirPathOT.compare dp dp'
       | _ -> Gt)
    | MPbound (dp, id, k) ->
      (match mp' with
       | MPfile _ -> Lt
       | MPbound (dp', id', k') -> mpbound_compare dp id k dp' id' k'
       | MPdot (_, _) -> Gt)
    | MPdot (mp0, id) ->
      (match mp' with
       | MPdot (mp'0, id') ->
         (match compare mp0 mp'0 with
          | Eq -> IdentOT.compare id id'
          | x -> x)
       | _ -> Lt)
 end

module ModPathOT = OrderedTypeAlt.OrderedType_from_Alt(ModPathComp)

module ModPathOTNew = OrdersAlt.Update_OT(ModPathOT)

module ModPathSet = Make(ModPathOTNew)

module ModPathSetFact = WFactsOn(ModPathOTNew)(ModPathSet)

module ModPathSetOrdProp = OrdProperties(ModPathSet)

module ModPathSetProp = ModPathSetOrdProp.P

module ModPathSetDecide = ModPathSetProp.Dec

module ModPathSetExtraOrdProp =
 MCMSets.MSets.ExtraOrdProperties(ModPathSet)(ModPathSetOrdProp)

module ModPathSetExtraDecide =
 MCMSets.MSetAVL.Decide(ModPathOTNew)(ModPathSet)

module ModPathMap = FMapAVL.Make(ModPathOT)

module ModPathMapFact = FMapFacts.WProperties(ModPathMap)

module ModPathMapExtraFact =
 MCFSets.FSets.WFactsExtra_fun(ModPathOT)(ModPathMap)(ModPathMapFact.F)

module ModPathMapDecide = MCFSets.FMapAVL.Decide(ModPathOT)(ModPathMap)

(** val modpath_eq_dec : modpath -> modpath -> sumbool **)

let modpath_eq_dec x y =
  let filtered_var = ModPathComp.compare x y in
  (match filtered_var with
   | Eq -> Coq_left
   | _ -> Coq_right)

(** val modpath_EqDec : modpath coq_EqDec **)

let modpath_EqDec =
  modpath_eq_dec

module KernameComp =
 struct
  type t = kername

  (** val compare :
      (modpath, String.t) prod -> (modpath, String.t) prod -> comparison **)

  let compare kn kn' =
    let Coq_pair (mp, id) = kn in
    let Coq_pair (mp', id') = kn' in
    (match ModPathComp.compare mp mp' with
     | Eq -> IdentOT.compare id id'
     | x -> x)
 end

module Kername =
 struct
  type t = kername

  (** val compare :
      (modpath, String.t) prod -> (modpath, String.t) prod -> comparison **)

  let compare kn kn' =
    let Coq_pair (mp, id) = kn in
    let Coq_pair (mp', id') = kn' in
    (match ModPathComp.compare mp mp' with
     | Eq -> IdentOT.compare id id'
     | x -> x)

  module OT = OrderedTypeAlt.OrderedType_from_Alt(KernameComp)

  (** val eqb :
      (modpath, String.t) prod -> (modpath, String.t) prod -> bool **)

  let eqb kn kn' =
    match compare kn kn' with
    | Eq -> Coq_true
    | _ -> Coq_false

  (** val reflect_kername : kername coq_ReflectEq **)

  let reflect_kername =
    eqb

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    eq_dec (coq_ReflectEq_EqDec reflect_kername)
 end

module KernameMap = FMapAVL.Make(Kername.OT)

module KernameMapFact = FMapFacts.WProperties(KernameMap)

module KernameMapExtraFact =
 MCFSets.FSets.WFactsExtra_fun(Kername.OT)(KernameMap)(KernameMapFact.F)

module KernameMapDecide = MCFSets.FMapAVL.Decide(Kername.OT)(KernameMap)

(** val eq_constant : kername -> kername -> bool **)

let eq_constant =
  eqb Kername.reflect_kername

module KernameSet = Make(Kername)

module KernameSetFact = WFactsOn(Kername)(KernameSet)

module KernameSetOrdProp = OrdProperties(KernameSet)

module KernameSetProp = KernameSetOrdProp.P

module KernameSetDecide = KernameSetProp.Dec

module KernameSetExtraOrdProp =
 MCMSets.MSets.ExtraOrdProperties(KernameSet)(KernameSetOrdProp)

module KernameSetExtraDecide = MCMSets.MSetAVL.Decide(Kername)(KernameSet)

type inductive = { inductive_mind : kername; inductive_ind : nat }

(** val inductive_mind : inductive -> kername **)

let inductive_mind i =
  i.inductive_mind

(** val inductive_ind : inductive -> nat **)

let inductive_ind i =
  i.inductive_ind

(** val coq_NoConfusionPackage_inductive :
    inductive coq_NoConfusionPackage **)

let coq_NoConfusionPackage_inductive =
  Build_NoConfusionPackage

(** val string_of_inductive : inductive -> String.t **)

let string_of_inductive i =
  String.append (string_of_kername i.inductive_mind)
    (String.append (String.String (Coq_x2c, String.EmptyString))
      (string_of_nat i.inductive_ind))

(** val eq_inductive_def : inductive -> inductive -> bool **)

let eq_inductive_def i i' =
  let { inductive_mind = i0; inductive_ind = n } = i in
  let { inductive_mind = i'0; inductive_ind = n' } = i' in
  eqb (reflect_prod Kername.reflect_kername reflect_nat) (Coq_pair (i0, n))
    (Coq_pair (i'0, n'))

(** val reflect_eq_inductive : inductive coq_ReflectEq **)

let reflect_eq_inductive =
  eq_inductive_def

type projection = { proj_ind : inductive; proj_npars : nat; proj_arg : nat }

(** val proj_ind : projection -> inductive **)

let proj_ind p =
  p.proj_ind

(** val proj_npars : projection -> nat **)

let proj_npars p =
  p.proj_npars

(** val proj_arg : projection -> nat **)

let proj_arg p =
  p.proj_arg

(** val eq_projection : projection -> projection -> bool **)

let eq_projection p p' =
  eqb
    (reflect_prod (reflect_prod reflect_eq_inductive reflect_nat) reflect_nat)
    (Coq_pair ((Coq_pair (p.proj_ind, p.proj_npars)), p.proj_arg)) (Coq_pair
    ((Coq_pair (p'.proj_ind, p'.proj_npars)), p'.proj_arg))

(** val reflect_eq_projection : projection coq_ReflectEq **)

let reflect_eq_projection =
  eq_projection

type global_reference =
| VarRef of ident
| ConstRef of kername
| IndRef of inductive
| ConstructRef of inductive * nat

(** val global_reference_rect :
    (ident -> 'a1) -> (kername -> 'a1) -> (inductive -> 'a1) -> (inductive ->
    nat -> 'a1) -> global_reference -> 'a1 **)

let global_reference_rect f f0 f1 f2 = function
| VarRef i -> f i
| ConstRef k -> f0 k
| IndRef i -> f1 i
| ConstructRef (i, n) -> f2 i n

(** val global_reference_rec :
    (ident -> 'a1) -> (kername -> 'a1) -> (inductive -> 'a1) -> (inductive ->
    nat -> 'a1) -> global_reference -> 'a1 **)

let global_reference_rec f f0 f1 f2 = function
| VarRef i -> f i
| ConstRef k -> f0 k
| IndRef i -> f1 i
| ConstructRef (i, n) -> f2 i n

(** val coq_NoConfusionPackage_global_reference :
    global_reference coq_NoConfusionPackage **)

let coq_NoConfusionPackage_global_reference =
  Build_NoConfusionPackage

(** val string_of_gref : global_reference -> String.t **)

let string_of_gref = function
| VarRef v -> v
| ConstRef s -> string_of_kername s
| IndRef i ->
  let { inductive_mind = s; inductive_ind = n } = i in
  String.append (String.String (Coq_x49, (String.String (Coq_x6e,
    (String.String (Coq_x64, (String.String (Coq_x75, (String.String
    (Coq_x63, (String.String (Coq_x74, (String.String (Coq_x69,
    (String.String (Coq_x76, (String.String (Coq_x65, (String.String
    (Coq_x20, String.EmptyString))))))))))))))))))))
    (String.append (string_of_kername s)
      (String.append (String.String (Coq_x20, String.EmptyString))
        (string_of_nat n)))
| ConstructRef (i, k) ->
  let { inductive_mind = s; inductive_ind = n } = i in
  String.append (String.String (Coq_x43, (String.String (Coq_x6f,
    (String.String (Coq_x6e, (String.String (Coq_x73, (String.String
    (Coq_x74, (String.String (Coq_x72, (String.String (Coq_x75,
    (String.String (Coq_x63, (String.String (Coq_x74, (String.String
    (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x20,
    String.EmptyString))))))))))))))))))))))))
    (String.append (string_of_kername s)
      (String.append (String.String (Coq_x20, String.EmptyString))
        (String.append (string_of_nat n)
          (String.append (String.String (Coq_x20, String.EmptyString))
            (string_of_nat k)))))

(** val gref_eqb : global_reference -> global_reference -> bool **)

let gref_eqb x y =
  match x with
  | VarRef i ->
    (match y with
     | VarRef i' -> eqb IdentOT.reflect_eq_string i i'
     | _ -> Coq_false)
  | ConstRef c ->
    (match y with
     | ConstRef c' -> eqb Kername.reflect_kername c c'
     | _ -> Coq_false)
  | IndRef i ->
    (match y with
     | IndRef i' -> eqb reflect_eq_inductive i i'
     | _ -> Coq_false)
  | ConstructRef (i, k) ->
    (match y with
     | ConstructRef (i', k') ->
       (match eqb reflect_eq_inductive i i' with
        | Coq_true -> eqb reflect_nat k k'
        | Coq_false -> Coq_false)
     | _ -> Coq_false)

(** val grep_reflect_eq : global_reference coq_ReflectEq **)

let grep_reflect_eq =
  gref_eqb

(** val gref_eq_dec : global_reference -> global_reference -> sumbool **)

let gref_eq_dec gr gr' =
  eq_dec (coq_ReflectEq_EqDec grep_reflect_eq) gr gr'

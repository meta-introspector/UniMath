open PartA
open PartB
open PartC
open PartD
open Preamble
open UnivalenceAxiom

type __ = Obj.t

type hProp = (coq_UU, __ isaprop) total2

val make_hProp : 'a1 isaprop -> hProp

type hProptoType = __

val propproperty : hProp -> __ isaprop

type tildehProp = (hProp, hProptoType) total2

val make_tildehProp : hProp -> hProptoType -> tildehProp

val subtypeInjectivity_prop :
  ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2 ->
  (('a1, hProptoType) total2 paths, 'a1 paths) weq

val subtypePath_prop :
  ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2 ->
  'a1 paths -> ('a1, hProptoType) total2 paths

val impred_prop : ('a1 -> hProp) -> ('a1 -> hProptoType) isaprop

val isaprop_total2 :
  hProp -> (hProptoType -> hProp) -> (hProptoType, hProptoType) total2 isaprop

val isaprop_forall_hProp : ('a1 -> hProp) -> ('a1 -> hProptoType) isaprop

val forall_hProp : ('a1 -> hProp) -> hProp

type 'x ishinh_UUU = hProp -> ('x -> hProptoType) -> hProptoType

val isapropishinh : 'a1 ishinh_UUU isaprop

val ishinh : hProp

val hinhpr : 'a1 -> hProptoType

val hinhfun : ('a1 -> 'a2) -> hProptoType -> hProptoType

val hinhuniv : hProp -> ('a1 -> hProptoType) -> hProptoType -> hProptoType

val factor_through_squash : 'a2 isaprop -> ('a1 -> 'a2) -> hProptoType -> 'a2

val squash_to_prop : hProptoType -> 'a2 isaprop -> ('a1 -> 'a2) -> 'a2

val hinhand : hProptoType -> hProptoType -> hProptoType

val hinhuniv2 :
  hProp -> ('a1 -> 'a2 -> hProptoType) -> hProptoType -> hProptoType ->
  hProptoType

val hinhfun2 :
  ('a1 -> 'a2 -> 'a3) -> hProptoType -> hProptoType -> hProptoType

val hinhunivcor1 : hProp -> hProptoType -> hProptoType

(* val weqishinhnegtoneg : (hProptoType, 'a1 neg) weq *)

(* val weqnegtonegishinh : ('a1 neg, hProptoType neg) weq *)

(* val hinhcoprod : hProptoType -> hProptoType *)

val decidable_ishinh : 'a1 decidable -> hProptoType decidable

type ('x, 'y) image = ('y, hProptoType) total2

val make_image :
  ('a1 -> 'a2) -> 'a2 -> hProptoType -> ('a2, hProptoType) total2

val pr1image : ('a1 -> 'a2) -> ('a2, hProptoType) total2 -> 'a2

val prtoimage : ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) image

type ('x, 'y) issurjective = 'y -> hProptoType

val isapropissurjective : ('a1 -> 'a2) -> ('a1, 'a2) issurjective isaprop

val isinclpr1image : ('a1 -> 'a2) -> (('a2, hProptoType) total2, 'a2) isincl

val issurjprtoimage : ('a1 -> 'a2) -> ('a1, ('a1, 'a2) image) issurjective

val issurjcomp :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) issurjective -> ('a2, 'a3)
  issurjective -> ('a1, 'a3) issurjective

val issurjtwooutof3b :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) issurjective -> ('a2, 'a3)
  issurjective

val isweqinclandsurj :
  ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) issurjective -> ('a1, 'a2)
  isweq

val issurjectiveweq :
  ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) issurjective

val htrue : hProp

val hfalse : hProp

val hconj : hProp -> hProp -> hProp

val hdisj : hProp

val hdisj_in1 : 'a1 -> hProptoType

val hdisj_in2 : 'a2 -> hProptoType

val disjoint_disjunction :
  hProp -> hProp -> (hProptoType -> hProptoType -> empty) -> hProp

val hneg : hProp

val himpl : hProp -> hProp

val hexists : hProp

val wittohexists : 'a1 -> 'a2 -> hProptoType

val total2tohexists : ('a1, 'a2) total2 -> hProptoType

(* val weqneghexistsnegtotal2 : (hProptoType neg, ('a1, 'a2) total2 neg) weq *)

val islogeqcommhdisj : hProp -> hProp -> (hProptoType, hProptoType) logeq

val hconjtohdisj : hProp -> hProptoType -> hProptoType

val hexistsnegtonegforall : hProptoType -> ('a1 -> 'a2) neg

val forallnegtoneghexists : ('a1 -> 'a2 neg) -> hProptoType neg

val neghexisttoforallneg : hProptoType -> 'a1 -> hProptoType

(* val weqforallnegtonegexists : ('a1 -> hProptoType, hProptoType) weq *)

val tonegdirprod : hProptoType -> hProptoType

val weak_fromnegdirprod : hProp -> hProp -> hProptoType -> hProptoType dneg

val tonegcoprod : (hProptoType, hProptoType) dirprod -> hProptoType

val toneghdisj : (hProptoType, hProptoType) dirprod -> hProptoType

val fromnegcoprod : hProptoType -> (hProptoType, hProptoType) dirprod

val fromnegcoprod_prop : hProp -> hProp -> hProptoType -> hProptoType

val hdisjtoimpl : hProp -> hProptoType -> hProptoType -> hProptoType

val isdecprophdisj : 'a1 isdecprop -> 'a2 isdecprop -> hProptoType isdecprop

val isinhdneg : hProp

val inhdnegpr : 'a1 -> hProptoType

val inhdnegfun : ('a1 -> 'a2) -> hProptoType -> hProptoType

val inhdneguniv : ('a2, 'a2 dneg) isweq -> ('a1 -> 'a2) -> hProptoType -> 'a2

val inhdnegand : hProptoType -> hProptoType -> hProptoType

val hinhimplinhdneg : hProptoType -> hProptoType

val hPropUnivalence :
  hProp -> hProp -> (hProptoType -> hProptoType) -> (hProptoType ->
  hProptoType) -> hProp paths

val eqweqmaphProp :
  hProp -> hProp -> hProp paths -> (hProptoType, hProptoType) weq

val weqtopathshProp :
  hProp -> hProp -> (hProptoType, hProptoType) weq -> hProp paths

val weqpathsweqhProp :
  hProp -> hProp -> (hProptoType, hProptoType) weq -> (hProptoType,
  hProptoType) weq paths

val univfromtwoaxiomshProp :
  hProp -> hProp -> (hProp paths, (hProptoType, hProptoType) weq) isweq

val weqeqweqhProp :
  hProp -> hProp -> (hProp paths, (hProptoType, hProptoType) weq) weq

val isasethProp : hProp isaset

val weqpathsweqhProp' : hProp -> hProp -> hProp paths -> hProp paths paths

val iscontrtildehProp : tildehProp iscontr

val isaproptildehProp : tildehProp isaprop

val isasettildehProp : tildehProp isaset

val logeqweq :
  hProp -> hProp -> (hProptoType -> hProptoType) -> (hProptoType ->
  hProptoType) -> (hProptoType, hProptoType) weq

val total2_paths_hProp_equiv :
  ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2 ->
  (('a1, hProptoType) total2 paths, 'a1 paths) weq

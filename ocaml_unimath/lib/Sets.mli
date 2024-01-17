open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open UnivalenceAxiom

type __ = Obj.t

type hSet = (coq_UU, __ isaset) total2

val make_hSet : 'a1 isaset -> hSet

type pr1hSet = __

val eqset : hSet -> pr1hSet -> pr1hSet -> hProp

val neqset : hSet -> pr1hSet -> pr1hSet -> hProp

val setproperty : hSet -> __ isaset

val setdirprod : hSet -> hSet -> hSet

val setcoprod : hSet -> hSet -> hSet

val isaset_total2_hSet :
  hSet -> (pr1hSet -> hSet) -> (pr1hSet, pr1hSet) total2 isaset

val total2_hSet : hSet -> (pr1hSet -> hSet) -> hSet

val hfiber_hSet : hSet -> hSet -> (pr1hSet -> pr1hSet) -> pr1hSet -> hSet

val isaset_forall_hSet : ('a1 -> hSet) -> ('a1 -> pr1hSet) isaset

val forall_hSet : ('a1 -> hSet) -> hSet

val unitset : hSet

val dirprod_hSet_subproof : hSet -> hSet -> (pr1hSet, pr1hSet) dirprod isaset

val dirprod_hSet : hSet -> hSet -> hSet

val hPropset : hSet

val hProp_to_hSet : hProp -> hSet

val boolset : hSet

val isaprop_isInjectiveFunction :
  hSet -> hSet -> (pr1hSet -> pr1hSet) -> (pr1hSet -> pr1hSet -> pr1hSet
  paths -> pr1hSet paths) isaprop

val isInjectiveFunction : hSet -> hSet -> (pr1hSet -> pr1hSet) -> hProp

type 'x ischoicebase_uu1 = __ -> ('x -> hProptoType) -> hProptoType

val isapropischoicebase : 'a1 ischoicebase_uu1 isaprop

val ischoicebase : hProp

val ischoicebaseweqf : ('a1, 'a2) weq -> hProptoType -> hProptoType

val ischoicebaseweqb : ('a1, 'a2) weq -> hProptoType -> hProptoType

val ischoicebaseunit : hProptoType

val ischoicebasecontr : 'a1 iscontr -> hProptoType

val ischoicebaseempty : hProptoType

val ischoicebaseempty2 : 'a1 neg -> hProptoType

(* val ischoicebasecoprod : hProptoType -> hProptoType -> hProptoType *)

type 'x hsubtype = 'x -> hProp

val id_hsubtype : 'a1 hsubtype -> 'a1 -> hProp

type 'x carrier = ('x, hProptoType) total2

val make_carrier :
  'a1 hsubtype -> 'a1 -> hProptoType -> ('a1, hProptoType) total2

val pr1carrier : 'a1 hsubtype -> 'a1 carrier -> 'a1

val isaset_carrier_subset :
  hSet -> pr1hSet hsubtype -> (pr1hSet, hProptoType) total2 isaset

val carrier_subset : hSet -> pr1hSet hsubtype -> hSet

val isinclpr1carrier : 'a1 hsubtype -> ('a1 carrier, 'a1) isincl

val isasethsubtype : 'a1 hsubtype isaset

val totalsubtype : 'a1 hsubtype

(* val weqtotalsubtype : ('a1 carrier, 'a1) weq *)

val weq_subtypes :
  ('a1, 'a2) weq -> 'a1 hsubtype -> 'a2 hsubtype -> ('a1 -> (hProptoType,
  hProptoType) logeq) -> ('a1 carrier, 'a2 carrier) weq

val subtypesdirprod :
  'a1 hsubtype -> 'a2 hsubtype -> ('a1, 'a2) dirprod hsubtype

val fromdsubtypesdirprodcarrier :
  'a1 hsubtype -> 'a2 hsubtype -> ('a1, 'a2) dirprod carrier -> ('a1 carrier,
  'a2 carrier) dirprod

val tosubtypesdirprodcarrier :
  'a1 hsubtype -> 'a2 hsubtype -> ('a1 carrier, 'a2 carrier) dirprod -> ('a1,
  'a2) dirprod carrier

val weqsubtypesdirprod :
  'a1 hsubtype -> 'a2 hsubtype -> (('a1, 'a2) dirprod carrier, ('a1 carrier,
  'a2 carrier) dirprod) weq

val ishinhsubtypedirprod :
  'a1 hsubtype -> 'a2 hsubtype -> hProptoType -> hProptoType -> hProptoType

val isapropsubtype :
  'a1 hsubtype -> ('a1 -> 'a1 -> hProptoType -> hProptoType -> 'a1 paths) ->
  'a1 carrier isaprop

val squash_pairs_to_set :
  'a1 isaset -> ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths) -> hProptoType -> 'a1

val squash_to_set :
  'a2 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a1 -> 'a2 paths) -> hProptoType ->
  'a2

type 'x hrel = 'x -> 'x -> hProp

val idhrel : 'a1 hrel -> 'a1 -> 'a1 -> hProp

type 'x brel = 'x -> 'x -> bool

val idbrel : 'a1 brel -> 'a1 -> 'a1 -> bool

type 'x istrans = 'x -> 'x -> 'x -> hProptoType -> hProptoType -> hProptoType

type 'x isrefl = 'x -> hProptoType

type 'x issymm = 'x -> 'x -> hProptoType -> hProptoType

type 'x ispreorder = ('x istrans, 'x isrefl) dirprod

type 'x iseqrel = ('x ispreorder, 'x issymm) dirprod

val iseqrelconstr :
  'a1 hrel -> 'a1 istrans -> 'a1 isrefl -> 'a1 issymm -> 'a1 iseqrel

type 'x isirrefl = 'x -> hProptoType neg

type 'x isasymm = 'x -> 'x -> hProptoType -> hProptoType -> empty

type 'x iscoasymm = 'x -> 'x -> hProptoType neg -> hProptoType

type 'x istotal = 'x -> 'x -> hProptoType

type 'x isdectotal = 'x -> 'x -> (hProptoType, hProptoType) coprod

type 'x iscotrans = 'x -> 'x -> 'x -> hProptoType -> hProptoType

type 'x isdeccotrans =
  'x -> 'x -> 'x -> hProptoType -> (hProptoType, hProptoType) coprod

type 'x isdecrel = 'x -> 'x -> (hProptoType, hProptoType neg) coprod

type 'x isnegrel = 'x -> 'x -> hProptoType neg neg -> hProptoType

type 'x isantisymm = 'x -> 'x -> hProptoType -> hProptoType -> 'x paths

type 'x isPartialOrder = ('x ispreorder, 'x isantisymm) dirprod

type 'x isantisymmneg =
  'x -> 'x -> hProptoType neg -> hProptoType neg -> 'x paths

type 'x iscoantisymm =
  'x -> 'x -> hProptoType neg -> (hProptoType, 'x paths) coprod

type 'x neqchoice =
  'x -> 'x -> 'x paths neg -> (hProptoType, hProptoType) coprod

val isaprop_istrans : hSet -> pr1hSet hrel -> pr1hSet istrans isaprop

val isaprop_isrefl : hSet -> pr1hSet hrel -> pr1hSet isrefl isaprop

val isaprop_istotal : hSet -> pr1hSet hrel -> pr1hSet istotal isaprop

val isaprop_isantisymm : hSet -> pr1hSet hrel -> pr1hSet isantisymm isaprop

val isaprop_ispreorder : hSet -> pr1hSet hrel -> pr1hSet ispreorder isaprop

val isaprop_isPartialOrder :
  hSet -> pr1hSet hrel -> pr1hSet isPartialOrder isaprop

val isaset_hrel : hSet -> pr1hSet hrel isaset

val istransandirrefltoasymm :
  'a1 hrel -> 'a1 istrans -> 'a1 isirrefl -> 'a1 isasymm

val istotaltoiscoasymm : 'a1 hrel -> 'a1 istotal -> 'a1 iscoasymm

val isdecreltoisnegrel : 'a1 hrel -> 'a1 isdecrel -> 'a1 isnegrel

val isantisymmnegtoiscoantisymm :
  'a1 hrel -> 'a1 isdecrel -> 'a1 isantisymmneg -> 'a1 iscoantisymm

val rtoneq :
  'a1 hrel -> 'a1 isirrefl -> 'a1 -> 'a1 -> hProptoType -> 'a1 paths neg

type 'x hrellogeq = 'x -> 'x -> (hProptoType, hProptoType) logeq

val istranslogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 istrans -> 'a1 istrans

val isrefllogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isrefl -> 'a1 isrefl

val issymmlogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 issymm -> 'a1 issymm

val ispologeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 ispreorder -> 'a1 ispreorder

val iseqrellogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 iseqrel -> 'a1 iseqrel

val isirrefllogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isirrefl -> 'a1 isirrefl

val isasymmlogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isasymm -> 'a1 isasymm

val iscoasymmlogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 iscoasymm -> 'a1 iscoasymm

val istotallogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 istotal -> 'a1 istotal

val iscotranslogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 iscotrans -> 'a1 iscotrans

val isdecrellogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isdecrel -> 'a1 isdecrel

val isnegrellogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isnegrel -> 'a1 isnegrel

val isantisymmlogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isantisymm -> 'a1 isantisymm

val isantisymmneglogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 isantisymmneg -> 'a1 isantisymmneg

val iscoantisymmlogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 iscoantisymm -> 'a1 iscoantisymm

val neqchoicelogeqf :
  'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) ->
  'a1 neqchoice -> 'a1 neqchoice

type 'x po = ('x hrel, 'x ispreorder) total2

val make_po : 'a1 hrel -> 'a1 ispreorder -> 'a1 po

val carrierofpo : 'a1 po -> 'a1 -> 'a1 -> hProp

type coq_PreorderedSet = (hSet, pr1hSet po) total2

val coq_PreorderedSetPair : hSet -> pr1hSet po -> coq_PreorderedSet

val carrierofPreorderedSet : coq_PreorderedSet -> hSet

val coq_PreorderedSetRelation : coq_PreorderedSet -> pr1hSet hrel

type coq_PartialOrder = (pr1hSet hrel, pr1hSet isPartialOrder) total2

val make_PartialOrder :
  hSet -> pr1hSet hrel -> pr1hSet isPartialOrder -> coq_PartialOrder

val carrierofPartialOrder : hSet -> coq_PartialOrder -> pr1hSet hrel

type coq_Poset = (hSet, coq_PartialOrder) total2

val make_Poset : hSet -> coq_PartialOrder -> coq_Poset

val carrierofposet : coq_Poset -> hSet

val posetRelation : coq_Poset -> pr1hSet hrel

val isrefl_posetRelation : coq_Poset -> pr1hSet isrefl

val istrans_posetRelation : coq_Poset -> pr1hSet istrans

val isantisymm_posetRelation : coq_Poset -> pr1hSet isantisymm

type isaposetmorphism = pr1hSet -> pr1hSet -> hProptoType -> hProptoType

type posetmorphism = (pr1hSet -> pr1hSet, isaposetmorphism) total2

val make_posetmorphism :
  coq_Poset -> coq_Poset -> (pr1hSet -> pr1hSet) -> isaposetmorphism ->
  (pr1hSet -> pr1hSet, isaposetmorphism) total2

val carrierofposetmorphism :
  coq_Poset -> coq_Poset -> posetmorphism -> pr1hSet -> pr1hSet

type isdec_ordering = pr1hSet -> pr1hSet -> hProptoType decidable

val isaprop_isaposetmorphism :
  coq_Poset -> coq_Poset -> (pr1hSet -> pr1hSet) -> isaposetmorphism isaprop

val isaset_po : hSet -> pr1hSet po isaset

val isaset_PartialOrder : hSet -> coq_PartialOrder isaset

type isPosetEquivalence = (isaposetmorphism, isaposetmorphism) dirprod

val isaprop_isPosetEquivalence :
  coq_Poset -> coq_Poset -> (pr1hSet, pr1hSet) weq -> isPosetEquivalence
  isaprop

val isPosetEquivalence_idweq : coq_Poset -> isPosetEquivalence

type coq_PosetEquivalence =
  ((pr1hSet, pr1hSet) weq, isPosetEquivalence) total2

val posetUnderlyingEquivalence :
  coq_Poset -> coq_Poset -> coq_PosetEquivalence -> (pr1hSet, pr1hSet) weq

val identityPosetEquivalence : coq_Poset -> coq_PosetEquivalence

val isincl_pr1_PosetEquivalence :
  coq_Poset -> coq_Poset -> (coq_PosetEquivalence, (pr1hSet, pr1hSet) weq)
  isincl

val isinj_pr1_PosetEquivalence :
  coq_Poset -> coq_Poset -> (coq_PosetEquivalence, (pr1hSet, pr1hSet) weq)
  isInjective

type isMinimal = pr1hSet -> hProptoType

type isMaximal = pr1hSet -> hProptoType

type consecutive =
  ((hProptoType, pr1hSet paths neg) dirprod, pr1hSet -> ((hProptoType,
  pr1hSet paths neg) dirprod, (hProptoType, pr1hSet paths neg) dirprod)
  dirprod neg) dirprod

val isaprop_isMinimal : coq_Poset -> pr1hSet -> isMaximal isaprop

val isaprop_isMaximal : coq_Poset -> pr1hSet -> isMaximal isaprop

val isaprop_consecutive :
  coq_Poset -> pr1hSet -> pr1hSet -> consecutive isaprop

type 'x eqrel = ('x hrel, 'x iseqrel) total2

val make_eqrel : 'a1 hrel -> 'a1 iseqrel -> 'a1 eqrel

val eqrelconstr :
  'a1 hrel -> 'a1 istrans -> 'a1 isrefl -> 'a1 issymm -> 'a1 eqrel

val pr1eqrel : 'a1 eqrel -> 'a1 -> 'a1 -> hProp

val eqreltrans : 'a1 eqrel -> 'a1 istrans

val eqrelrefl : 'a1 eqrel -> 'a1 isrefl

val eqrelsymm : 'a1 eqrel -> 'a1 issymm

val hreldirprod : 'a1 hrel -> 'a2 hrel -> ('a1, 'a2) dirprod hrel

val istransdirprod :
  'a1 hrel -> 'a2 hrel -> 'a1 istrans -> 'a2 istrans -> ('a1, 'a2) dirprod
  istrans

val isrefldirprod :
  'a1 hrel -> 'a2 hrel -> 'a1 isrefl -> 'a2 isrefl -> ('a1, 'a2) dirprod
  isrefl

val issymmdirprod :
  'a1 hrel -> 'a2 hrel -> 'a1 issymm -> 'a2 issymm -> ('a1, 'a2) dirprod
  issymm

val eqreldirprod : 'a1 eqrel -> 'a2 eqrel -> ('a1, 'a2) dirprod eqrel

val negrel : 'a1 hrel -> 'a1 hrel

val istransnegrel : 'a1 hrel -> 'a1 iscotrans -> 'a1 istrans

val isasymmnegrel : 'a1 hrel -> 'a1 iscoasymm -> 'a1 isasymm

val iscoasymmgenrel : 'a1 hrel -> 'a1 isasymm -> 'a1 iscoasymm

val isdecnegrel : 'a1 hrel -> 'a1 isdecrel -> 'a1 isdecrel

val isnegnegrel : 'a1 hrel -> 'a1 isnegrel

val isantisymmnegrel : 'a1 hrel -> 'a1 isantisymmneg -> 'a1 isantisymm

val eqh : 'a1 isdeceq -> 'a1 hrel

val neqh : 'a1 isdeceq -> 'a1 hrel

val isrefleqh : 'a1 isdeceq -> 'a1 isrefl

val weqeqh : 'a1 isdeceq -> 'a1 -> 'a1 -> ('a1 paths, hProptoType) weq

val weqneqh : 'a1 isdeceq -> 'a1 -> 'a1 -> ('a1 paths neg, hProptoType) weq

type 'x decrel = ('x hrel, 'x isdecrel) total2

val pr1decrel : 'a1 decrel -> 'a1 hrel

val make_decrel : 'a1 hrel -> 'a1 isdecrel -> 'a1 decrel

val decreltobrel : 'a1 decrel -> 'a1 brel

val breltodecrel : 'a1 brel -> 'a1 decrel

val pathstor : 'a1 decrel -> 'a1 -> 'a1 -> bool paths -> hProptoType

val rtopaths : 'a1 decrel -> 'a1 -> 'a1 -> hProptoType -> bool paths

val pathstonegr : 'a1 decrel -> 'a1 -> 'a1 -> bool paths -> hProptoType neg

val negrtopaths : 'a1 decrel -> 'a1 -> 'a1 -> hProptoType neg -> bool paths

val ctlong :
  'a1 hrel -> 'a1 isdecrel -> 'a1 -> 'a1 -> bool paths -> hProptoType

val deceq_to_decrel : 'a1 isdeceq -> 'a1 decrel

val confirm_equal : 'a1 isdeceq -> 'a1 -> 'a1 -> bool paths -> 'a1 paths

val confirm_not_equal :
  'a1 isdeceq -> 'a1 -> 'a1 -> bool paths -> 'a1 paths neg

val resrel : 'a1 hrel -> 'a1 hsubtype -> 'a1 carrier hrel

val istransresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 istrans -> 'a1 carrier istrans

val isreflresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isrefl -> 'a1 carrier isrefl

val issymmresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 issymm -> 'a1 carrier issymm

val isporesrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 ispreorder -> 'a1 carrier ispreorder

val iseqrelresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iseqrel -> 'a1 carrier iseqrel

val isirreflresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isirrefl -> 'a1 carrier isirrefl

val isasymmresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isasymm -> 'a1 carrier isasymm

val iscoasymmresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iscoasymm -> 'a1 carrier iscoasymm

val istotalresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 istotal -> 'a1 carrier istotal

val iscotransresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iscotrans -> 'a1 carrier iscotrans

val isdecrelresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isdecrel -> 'a1 carrier isdecrel

val isnegrelresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isnegrel -> 'a1 carrier isnegrel

val isantisymmresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isantisymm -> 'a1 carrier isantisymm

val isantisymmnegresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 isantisymmneg -> 'a1 carrier isantisymmneg

val iscoantisymmresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iscoantisymm -> 'a1 carrier iscoantisymm

val neqchoiceresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 neqchoice -> 'a1 carrier neqchoice

type 'x iseqclass =
  (hProptoType, ('x -> 'x -> hProptoType -> hProptoType -> hProptoType, 'x ->
  'x -> hProptoType -> hProptoType -> hProptoType) dirprod) dirprod

val iseqclassconstr :
  'a1 hrel -> 'a1 hsubtype -> hProptoType -> ('a1 -> 'a1 -> hProptoType ->
  hProptoType -> hProptoType) -> ('a1 -> 'a1 -> hProptoType -> hProptoType ->
  hProptoType) -> 'a1 iseqclass

val eqax0 : 'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> hProptoType

val eqax1 :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> 'a1 -> 'a1 -> hProptoType ->
  hProptoType -> hProptoType

val eqax2 :
  'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> 'a1 -> 'a1 -> hProptoType ->
  hProptoType -> hProptoType

val isapropiseqclass : 'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass isaprop

val iseqclassdirprod :
  'a1 hrel -> 'a2 hrel -> 'a1 hsubtype -> 'a2 hsubtype -> 'a1 iseqclass ->
  'a2 iseqclass -> ('a1, 'a2) dirprod iseqclass

val surjectionisepitosets :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) issurjective ->
  'a3 isaset -> ('a1 -> 'a3 paths) -> 'a2 -> 'a3 paths

val isaset_set_fun_space : hSet -> ('a1 -> pr1hSet) isaset

val epiissurjectiontosets :
  ('a1 -> 'a2) -> 'a2 isaset -> (hSet -> ('a2 -> pr1hSet) -> ('a2 -> pr1hSet)
  -> ('a1 -> pr1hSet paths) -> 'a2 -> pr1hSet paths) -> ('a1, 'a2)
  issurjective

val surjective_iscontr_im :
  'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
  'a3 paths) -> ('a1, 'a2) issurjective -> 'a2 -> (('a1, 'a2) hfiber, 'a3)
  image iscontr

val univ_surj :
  'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
  'a3 paths) -> ('a1, 'a2) issurjective -> 'a2 -> 'a3

val univ_surj_ax :
  'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
  'a3 paths) -> ('a1, 'a2) issurjective -> 'a1 -> 'a3 paths

val univ_surj_unique :
  'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
  'a3 paths) -> ('a1, 'a2) issurjective -> ('a2 -> 'a3) -> ('a1 -> 'a3 paths)
  -> 'a2 -> 'a3 paths

type 'x setquot = ('x hsubtype, 'x iseqclass) total2

val make_setquot : 'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> 'a1 setquot

val pr1setquot : 'a1 hrel -> 'a1 setquot -> 'a1 hsubtype

val isinclpr1setquot : 'a1 hrel -> ('a1 setquot, 'a1 hsubtype) isincl

val isasetsetquot : 'a1 hrel -> 'a1 setquot isaset

val setquotinset : 'a1 hrel -> hSet

val setquotpr : 'a1 eqrel -> 'a1 -> 'a1 setquot

val setquotl0 : 'a1 eqrel -> 'a1 setquot -> 'a1 carrier -> 'a1 setquot paths

val issurjsetquotpr : 'a1 eqrel -> ('a1, 'a1 setquot) issurjective

val iscompsetquotpr :
  'a1 eqrel -> 'a1 -> 'a1 -> hProptoType -> 'a1 setquot paths

type ('x, 'y) iscomprelfun = 'x -> 'x -> hProptoType -> 'y paths

val iscomprelfunlogeqf :
  'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> ('a1 -> 'a2) -> ('a1, 'a2)
  iscomprelfun -> ('a1, 'a2) iscomprelfun

val isapropimeqclass :
  'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun -> 'a1
  setquot -> ('a1 carrier, pr1hSet) image isaprop

val setquotuniv :
  'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun -> 'a1
  setquot -> pr1hSet

val setquotunivcomm :
  'a1 eqrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun -> 'a1
  -> pr1hSet paths

val weqpathsinsetquot :
  'a1 eqrel -> 'a1 -> 'a1 -> (hProptoType, 'a1 setquot paths) weq

type ('x, 'y) iscomprelrelfun = 'x -> 'x -> hProptoType -> hProptoType

val iscomprelfunlogeqf1 :
  'a1 hrel -> 'a1 hrel -> 'a2 hrel -> 'a1 hrellogeq -> ('a1 -> 'a2) -> ('a1,
  'a2) iscomprelrelfun -> ('a1, 'a2) iscomprelrelfun

val iscomprelfunlogeqf2 :
  'a1 hrel -> 'a2 hrel -> 'a2 hrel -> 'a2 hrellogeq -> ('a1 -> 'a2) -> ('a1,
  'a2) iscomprelrelfun -> ('a1, 'a2) iscomprelrelfun

val setquotfun :
  'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun -> 'a1
  setquot -> 'a2 setquot

val setquotfuncomm :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun -> 'a1
  -> 'a2 setquot paths

val setquotunivprop :
  'a1 eqrel -> ('a1 setquot -> hProp) -> ('a1 -> __) -> 'a1 setquot -> __

val setquotuniv2prop :
  'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> hProp) -> ('a1 -> 'a1 ->
  hProptoType) -> 'a1 setquot -> 'a1 setquot -> hProptoType

val setquotuniv3prop :
  'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> hProp) -> ('a1
  -> 'a1 -> 'a1 -> hProptoType) -> 'a1 setquot -> 'a1 setquot -> 'a1 setquot
  -> hProptoType

val setquotuniv4prop :
  'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> 'a1 setquot ->
  hProp) -> ('a1 -> 'a1 -> 'a1 -> 'a1 -> hProptoType) -> 'a1 setquot -> 'a1
  setquot -> 'a1 setquot -> 'a1 setquot -> hProptoType

val issurjsetquotfun :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> ('a1,
  'a2) iscomprelrelfun -> ('a1 setquot, 'a2 setquot) issurjective

val isinclsetquotfun :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun ->
  ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1 setquot, 'a2 setquot)
  isincl

val setquotincl :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun ->
  ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1 setquot, 'a2 setquot)
  incl

val weqsetquotweq :
  'a1 eqrel -> 'a2 eqrel -> ('a1, 'a2) weq -> ('a1, 'a2) iscomprelrelfun ->
  ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1 setquot, 'a2 setquot) weq

val weqsetquotsurj :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> ('a1,
  'a2) iscomprelrelfun -> ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1
  setquot, 'a2 setquot) weq

val setquottodirprod :
  'a1 eqrel -> 'a2 eqrel -> ('a1, 'a2) dirprod setquot -> ('a1 setquot, 'a2
  setquot) dirprod

val dirprodtosetquot :
  'a1 hrel -> 'a2 hrel -> ('a1 setquot, 'a2 setquot) dirprod -> ('a1, 'a2)
  dirprod setquot

val weqsetquottodirprod :
  'a1 eqrel -> 'a2 eqrel -> (('a1, 'a2) dirprod setquot, ('a1 setquot, 'a2
  setquot) dirprod) weq

type ('x, 'y) iscomprelfun2 =
  'x -> 'x -> 'x -> 'x -> hProptoType -> hProptoType -> 'y paths

val iscomprelfun2if :
  'a1 hrel -> ('a1 -> 'a1 -> 'a2) -> ('a1 -> 'a1 -> 'a1 -> hProptoType -> 'a2
  paths) -> ('a1 -> 'a1 -> 'a1 -> hProptoType -> 'a2 paths) -> ('a1, 'a2)
  iscomprelfun2

val iscomprelfun2logeqf :
  'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2)
  iscomprelfun2 -> ('a1, 'a2) iscomprelfun2

val setquotuniv2_iscomprelfun :
  'a1 hrel -> hSet -> ('a1 -> 'a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun2
  -> 'a1 setquot -> 'a1 setquot -> (('a1, 'a1) dirprod, pr1hSet) iscomprelfun

val setquotuniv2 :
  'a1 hrel -> hSet -> ('a1 -> 'a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun2
  -> 'a1 setquot -> 'a1 setquot -> pr1hSet

val setquotuniv2comm :
  'a1 eqrel -> hSet -> ('a1 -> 'a1 -> pr1hSet) -> ('a1, pr1hSet)
  iscomprelfun2 -> 'a1 -> 'a1 -> pr1hSet paths

type ('x, 'y) iscomprelrelfun2 =
  'x -> 'x -> 'x -> 'x -> hProptoType -> hProptoType -> hProptoType

val iscomprelrelfun2if :
  'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1 -> 'a1 -> 'a1 ->
  hProptoType -> hProptoType) -> ('a1 -> 'a1 -> 'a1 -> hProptoType ->
  hProptoType) -> ('a1, 'a2) iscomprelrelfun2

val iscomprelrelfun2logeqf1 :
  'a1 hrel -> 'a1 hrel -> 'a2 hrel -> 'a1 hrellogeq -> ('a1 -> 'a1 -> 'a2) ->
  ('a1, 'a2) iscomprelrelfun2 -> ('a1, 'a2) iscomprelrelfun2

val iscomprelrelfun2logeqf2 :
  'a1 hrel -> 'a2 hrel -> 'a2 hrel -> 'a2 hrellogeq -> ('a1 -> 'a1 -> 'a2) ->
  ('a1, 'a2) iscomprelrelfun2 -> ('a1, 'a2) iscomprelrelfun2

val setquotfun2_iscomprelfun2 :
  'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun2
  -> 'a1 setquot -> 'a1 setquot -> ('a1, 'a2 setquot) iscomprelfun2

val setquotfun2 :
  'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun2
  -> 'a1 setquot -> 'a1 setquot -> 'a2 setquot

val setquotfun2comm :
  'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2)
  iscomprelrelfun2 -> 'a1 -> 'a1 -> 'a2 setquot paths

val isdeceqsetquot_non_constr :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot isdeceq

val setquotbooleqint :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 -> 'a1 -> bool

val setquotbooleqintcomp :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> ('a1, bool)
  iscomprelfun2

val setquotbooleq :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot -> 'a1
  setquot -> bool

val setquotbooleqtopaths :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot -> 'a1
  setquot -> bool paths -> 'a1 setquot paths

val setquotpathstobooleq :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot -> 'a1
  setquot -> 'a1 setquot paths -> bool paths

val isdeceqsetquot :
  'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot isdeceq

type 'x iscomprelrel = ('x, hProp) iscomprelfun2

val iscomprelrelif :
  'a1 hrel -> 'a1 hrel -> 'a1 issymm -> ('a1 -> 'a1 -> 'a1 -> hProptoType ->
  hProptoType -> hProptoType) -> ('a1 -> 'a1 -> 'a1 -> hProptoType ->
  hProptoType -> hProptoType) -> 'a1 iscomprelrel

val iscomprelrellogeqf1 :
  'a1 hrel -> 'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> 'a1 iscomprelrel ->
  'a1 iscomprelrel

val iscomprelrellogeqf2 :
  'a1 hrel -> 'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> 'a1 iscomprelrel ->
  'a1 iscomprelrel

val quotrel : 'a1 hrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 setquot hrel

val istransquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 istrans -> 'a1 setquot
  istrans

val issymmquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 issymm -> 'a1 setquot
  issymm

val isreflquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isrefl -> 'a1 setquot
  isrefl

val ispoquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 ispreorder -> 'a1 setquot
  ispreorder

val iseqrelquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iseqrel -> 'a1 setquot
  iseqrel

val isirreflquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isirrefl -> 'a1 setquot
  isirrefl

val isasymmquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isasymm -> 'a1 setquot
  isasymm

val iscoasymmquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscoasymm -> 'a1 setquot
  iscoasymm

val istotalquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 istotal -> 'a1 setquot
  istotal

val iscotransquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscotrans -> 'a1 setquot
  iscotrans

val isantisymmquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isantisymm -> 'a1 setquot
  isantisymm

val isantisymmnegquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isantisymmneg -> 'a1
  setquot isantisymmneg

val quotrelimpl :
  'a1 eqrel -> 'a1 hrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscomprelrel
  -> ('a1 -> 'a1 -> hProptoType -> hProptoType) -> 'a1 setquot -> 'a1 setquot
  -> hProptoType -> hProptoType

val quotrellogeq :
  'a1 eqrel -> 'a1 hrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscomprelrel
  -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) -> 'a1 setquot -> 'a1
  setquot -> (hProptoType, hProptoType) logeq

val quotdecrelint :
  'a1 hrel -> 'a1 decrel -> 'a1 iscomprelrel -> 'a1 setquot brel

val quotdecrelintlogeq :
  'a1 eqrel -> 'a1 decrel -> 'a1 iscomprelrel -> 'a1 setquot -> 'a1 setquot
  -> (hProptoType, hProptoType) logeq

val isdecquotrel :
  'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isdecrel -> 'a1 setquot
  isdecrel

val decquotrel :
  'a1 eqrel -> 'a1 decrel -> 'a1 iscomprelrel -> 'a1 setquot decrel

val reseqrel : 'a1 eqrel -> 'a1 hsubtype -> 'a1 carrier eqrel

val iseqclassresrel :
  'a1 hrel -> 'a1 hsubtype -> 'a1 hsubtype -> 'a1 iseqclass -> ('a1 ->
  hProptoType -> hProptoType) -> 'a1 carrier iseqclass

val fromsubquot :
  'a1 eqrel -> 'a1 setquot hsubtype -> 'a1 setquot carrier -> 'a1 carrier
  setquot

val tosubquot :
  'a1 eqrel -> 'a1 setquot hsubtype -> 'a1 carrier setquot -> 'a1 setquot
  carrier

val weqsubquot :
  'a1 eqrel -> 'a1 setquot hsubtype -> ('a1 setquot carrier, 'a1 carrier
  setquot) weq

val pathshrel : 'a1 -> 'a1 -> hProp

val istranspathshrel : 'a1 istrans

val isreflpathshrel : 'a1 isrefl

val issymmpathshrel : 'a1 issymm

(* val pathseqrel : 'a1 eqrel *)

type 'x pi0 = 'x setquot

(* val pi0pr : 'a1 -> 'a1 setquot *)

type ('x, 's) compfun = ('x -> 's, ('x, 's) iscomprelfun) total2

val make_compfun :
  'a1 hrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelfun -> ('a1, 'a2) compfun

val pr1compfun : 'a1 hrel -> ('a1, 'a2) compfun -> 'a1 -> 'a2

val compevmapset :
  'a1 hrel -> 'a1 -> hSet -> ('a1, pr1hSet) compfun -> pr1hSet

val compfuncomp :
  'a1 hrel -> ('a1, 'a2) compfun -> ('a2 -> 'a3) -> ('a1, 'a3) compfun

type 'x setquot2 = ('x, hSet -> ('x, pr1hSet) compfun -> pr1hSet) image

val isasetsetquot2 : 'a1 hrel -> 'a1 setquot2 isaset

val setquot2inset : 'a1 hrel -> hSet

val setquot2pr : 'a1 hrel -> 'a1 -> 'a1 setquot2

val issurjsetquot2pr : 'a1 hrel -> ('a1, 'a1 setquot2) issurjective

val iscompsetquot2pr : 'a1 hrel -> ('a1, 'a1 setquot2) iscomprelfun

val setquot2univ :
  'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun -> 'a1
  setquot2 -> pr1hSet

val setquot2univcomm :
  'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun -> 'a1
  -> pr1hSet paths

val weqpathssetquot2l1 : 'a1 eqrel -> 'a1 -> ('a1, hProp) iscomprelfun

val weqpathsinsetquot2 :
  'a1 eqrel -> 'a1 -> 'a1 -> (hProptoType, 'a1 setquot2 paths) weq

val setquottosetquot2 : 'a1 hrel -> 'a1 iseqrel -> 'a1 setquot -> 'a1 setquot2

val hSet_univalence_map : hSet -> hSet -> hSet paths -> (__, __) weq

val hSet_univalence : hSet -> hSet -> (hSet paths, (pr1hSet, pr1hSet) weq) weq

val hSet_rect :
  hSet -> hSet -> (hSet paths -> 'a1) -> (pr1hSet, pr1hSet) weq -> 'a1

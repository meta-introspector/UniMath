open NaturalNumbers
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val retract_dec :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2, 'a2) homot -> 'a1 isdeceq -> 'a2
    isdeceq **)

let retract_dec f g h i y y' =
  let d = i (g y) (g y') in
  (match d with
   | Coq_ii1 a ->
     Coq_ii1
       (pathscomp0 (idfun y) (funcomp g f y) (idfun y')
         (pathsinv0 (funcomp g f y) (idfun y) (h y))
         (pathscomp0 (f (g y)) (f (g y')) (idfun y')
           (maponpaths f (g y) (g y') a) (h y')))
   | Coq_ii2 b -> Coq_ii2 (fun p -> b (maponpaths g y y' p)))

(** val logeq_dec : ('a1, 'a2) logeq -> 'a1 decidable -> 'a2 decidable **)

let logeq_dec iff decX =
  let xtoY = iff.pr1 in
  let ytoX = iff.pr2 in
  (match decX with
   | Coq_ii1 a -> Coq_ii1 (xtoY a)
   | Coq_ii2 b -> Coq_ii2 (negf ytoX b))

(** val decidable_prop : hProp -> hProp **)

let decidable_prop x =
  make_hProp (isapropdec x.pr2)

(** val coq_LEM : hProp **)

let coq_LEM =
  forall_hProp decidable_prop

type coq_ComplementaryPair =
  (coq_UU, (coq_UU, (__, __) complementary) total2) total2

type coq_Part1 = __

type coq_Part2 = __

(** val pair_contradiction :
    coq_ComplementaryPair -> coq_Part1 -> coq_Part2 -> empty **)

let pair_contradiction c =
  c.pr2.pr2.pr1

(** val chooser : coq_ComplementaryPair -> (coq_Part1, coq_Part2) coprod **)

let chooser c =
  c.pr2.pr2.pr2

type isTrue = (coq_Part1, (coq_Part1, coq_Part2) coprod) hfiber

type isFalse = (coq_Part2, (coq_Part1, coq_Part2) coprod) hfiber

(** val trueWitness : coq_ComplementaryPair -> isTrue -> coq_Part1 **)

let trueWitness _ t =
  t.pr1

(** val falseWitness : coq_ComplementaryPair -> isFalse -> coq_Part2 **)

let falseWitness _ t =
  t.pr1

(** val complementaryDecisions :
    coq_ComplementaryPair -> (isTrue, isFalse) coprod iscontr **)

let complementaryDecisions c =
  iscontrifweqtounit
    (let w = weqcoprodsplit (fun _ -> chooser c) in
     invweq
       (weqcomp w
         (weqcoprodf (weqhfiberunit (fun x -> Coq_ii1 x) (chooser c))
           (weqhfiberunit (fun x -> Coq_ii2 x) (chooser c)))))

(** val isaprop_isTrue : coq_ComplementaryPair -> isTrue isaprop **)

let isaprop_isTrue c =
  isapropcomponent1 (isapropifcontr (complementaryDecisions c))

(** val isaprop_isFalse : coq_ComplementaryPair -> isFalse isaprop **)

let isaprop_isFalse c =
  isapropcomponent2 (isapropifcontr (complementaryDecisions c))

(** val pair_truth : coq_ComplementaryPair -> coq_Part1 -> isTrue **)

let pair_truth c _ =
  let qc = c.pr2 in
  let c0 = qc.pr2 in
  let c1 = c0.pr2 in
  (match c1 with
   | Coq_ii1 a -> { pr1 = a; pr2 = Coq_paths_refl }
   | Coq_ii2 _ -> fromempty (assert false (* absurd case *)))

(** val pair_falsehood : coq_ComplementaryPair -> coq_Part2 -> isFalse **)

let pair_falsehood c _ =
  let qc = c.pr2 in
  let c0 = qc.pr2 in
  let c1 = c0.pr2 in
  (match c1 with
   | Coq_ii1 _ -> fromempty (assert false (* absurd case *))
   | Coq_ii2 b -> { pr1 = b; pr2 = Coq_paths_refl })

(** val to_ComplementaryPair :
    ('a1, 'a1 neg) coprod -> coq_ComplementaryPair **)

let to_ComplementaryPair c =
  { pr1 = __; pr2 = { pr1 = __; pr2 = { pr1 = (fun p n -> Obj.magic n p);
    pr2 = (Obj.magic c) } } }

type 'x isolation = isFalse

(** val isaprop_isolation :
    'a1 -> 'a1 isisolated -> 'a1 -> 'a1 isolation isaprop **)

let isaprop_isolation _ is y =
  isaprop_isFalse (to_ComplementaryPair (is y))

(** val isolation_to_inequality :
    'a1 -> 'a1 isisolated -> 'a1 -> 'a1 isolation -> 'a1 paths neg **)

let isolation_to_inequality _ is y =
  Obj.magic falseWitness (to_ComplementaryPair (is y))

(** val inequality_to_isolation :
    'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths neg -> 'a1 isolation **)

let inequality_to_isolation _ i y =
  Obj.magic pair_falsehood (to_ComplementaryPair (i y))

(** val pairNegation : coq_ComplementaryPair -> coq_ComplementaryPair **)

let pairNegation c =
  { pr1 = __; pr2 = { pr1 = __; pr2 = { pr1 = (fun q p ->
    pair_contradiction c p q); pr2 = (coprodcomm (chooser c)) } } }

(** val pairConjunction :
    coq_ComplementaryPair -> coq_ComplementaryPair -> coq_ComplementaryPair **)

let pairConjunction c c' =
  let qc = c.pr2 in
  let c0 = qc.pr2 in
  let c1 = c0.pr2 in
  let qc0 = c'.pr2 in
  let c'0 = qc0.pr2 in
  let c'1 = c'0.pr2 in
  { pr1 = __; pr2 = { pr1 = __; pr2 = { pr1 = (fun _ _ -> assert false
  (* absurd case *)); pr2 =
  (match c1 with
   | Coq_ii1 a ->
     (match c'1 with
      | Coq_ii1 a0 -> Coq_ii1 (Obj.magic { pr1 = a; pr2 = a0 })
      | Coq_ii2 b -> Coq_ii2 (Obj.magic (Coq_ii2 b)))
   | Coq_ii2 b ->
     (match c'1 with
      | Coq_ii1 _ -> Coq_ii2 (Obj.magic (Coq_ii1 b))
      | Coq_ii2 b0 -> Coq_ii2 (Obj.magic (Coq_ii2 b0)))) } } }

(** val pairDisjunction :
    coq_ComplementaryPair -> coq_ComplementaryPair -> coq_ComplementaryPair **)

let pairDisjunction c c' =
  pairNegation (pairConjunction (pairNegation c) (pairNegation c'))

(** val dnegelim : ('a1, 'a2) complementary -> 'a1 dneg -> 'a1 **)

let dnegelim c _ =
  let c0 = c.pr2 in
  (match c0 with
   | Coq_ii1 a -> a
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val coq_LEM_for_sets : hProptoType -> 'a1 isaset -> 'a1 isdeceq **)

let coq_LEM_for_sets lem is x y =
  Obj.magic lem (make_hProp (is x y))

(** val isaprop_LEM : hProptoType isaprop **)

let isaprop_LEM =
  impred_isaprop (fun p -> isapropdec (propproperty p))

(** val dneg_LEM : hProp -> hProptoType -> hProptoType dneg -> hProptoType **)

let dneg_LEM p lem =
  dnegelim { pr1 = (fun p0 np -> np p0); pr2 = (Obj.magic lem p) }

(** val reversal_LEM :
    hProp -> hProp -> hProptoType -> (hProptoType neg -> hProptoType) ->
    hProptoType neg -> hProptoType **)

let reversal_LEM p _ lem f n =
  let g = negf f in let h = g n in dneg_LEM p lem h

type coq_DecidableProposition = (coq_UU, __ isdecprop) total2

(** val isdecprop_to_DecidableProposition :
    'a1 isdecprop -> coq_DecidableProposition **)

let isdecprop_to_DecidableProposition i =
  { pr1 = __; pr2 = (Obj.magic i) }

(** val decidable_to_isdecprop :
    hProp -> hProptoType decidable -> hProptoType isdecprop **)

let decidable_to_isdecprop x dec =
  isdecpropif (propproperty x) dec

(** val decidable_to_isdecprop_2 :
    'a1 isaprop -> ('a1, 'a1 neg) coprod -> 'a1 isdecprop **)

let decidable_to_isdecprop_2 =
  isdecpropif

(** val decidable_to_DecidableProposition :
    hProp -> hProptoType decidable -> coq_DecidableProposition **)

let decidable_to_DecidableProposition x dec =
  { pr1 = __; pr2 = (decidable_to_isdecprop x dec) }

(** val coq_DecidableProposition_to_isdecprop :
    coq_DecidableProposition -> __ isdecprop **)

let coq_DecidableProposition_to_isdecprop x =
  x.pr2

(** val coq_DecidableProposition_to_hProp :
    coq_DecidableProposition -> hProp **)

let coq_DecidableProposition_to_hProp x =
  { pr1 = __; pr2 = (isdecproptoisaprop x.pr2) }

(** val decidabilityProperty :
    coq_DecidableProposition -> hProptoType isdecprop **)

let decidabilityProperty x =
  x.pr2

type 'x coq_DecidableSubtype = 'x -> coq_DecidableProposition

type 'x coq_DecidableRelation = 'x -> 'x -> coq_DecidableProposition

(** val decrel_to_DecidableRelation :
    'a1 decrel -> 'a1 coq_DecidableRelation **)

let decrel_to_DecidableRelation r x y =
  let r0 = r.pr1 in
  let is = r.pr2 in
  { pr1 = __; pr2 = (isdecpropif (propproperty (r0 x y)) (is x y)) }

(** val decidableAnd :
    coq_DecidableProposition -> coq_DecidableProposition ->
    coq_DecidableProposition **)

let decidableAnd p q =
  { pr1 = __; pr2 =
    (Obj.magic isdecpropdirprod (decidabilityProperty p)
      (decidabilityProperty q)) }

(** val decidableOr :
    coq_DecidableProposition -> coq_DecidableProposition ->
    coq_DecidableProposition **)

let decidableOr p q =
  { pr1 = __; pr2 =
    (isdecprophdisj (decidabilityProperty p) (decidabilityProperty q)) }

(** val neg_isdecprop : 'a1 isdecprop -> 'a1 neg isdecprop **)

let neg_isdecprop i =
  isdecpropif isapropneg
    (let k = i.pr1 in
     match k with
     | Coq_ii1 a -> Coq_ii2 (todneg a)
     | Coq_ii2 b -> Coq_ii1 b)

(** val decidableNot :
    coq_DecidableProposition -> coq_DecidableProposition **)

let decidableNot p =
  { pr1 = __; pr2 = (Obj.magic neg_isdecprop (decidabilityProperty p)) }

(** val choice : coq_DecidableProposition -> 'a1 -> 'a1 -> 'a1 **)

let choice p yes no =
  let c = (decidabilityProperty p).pr1 in
  (match c with
   | Coq_ii1 _ -> yes
   | Coq_ii2 _ -> no)

(** val dependent_choice :
    coq_DecidableProposition -> (hProptoType -> 'a1) -> (hProptoType neg ->
    'a1) -> 'a1 **)

let dependent_choice p yes no =
  let c = (decidabilityProperty p).pr1 in
  (match c with
   | Coq_ii1 a -> yes a
   | Coq_ii2 b -> no b)

(** val choice_compute_yes :
    coq_DecidableProposition -> hProptoType -> 'a1 -> 'a1 -> 'a1 paths **)

let choice_compute_yes p _ _ _ =
  let c = (decidabilityProperty p).pr1 in
  (match c with
   | Coq_ii1 _ -> Coq_paths_refl
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val choice_compute_no :
    coq_DecidableProposition -> hProptoType neg -> 'a1 -> 'a1 -> 'a1 paths **)

let choice_compute_no p _ _ _ =
  let c = (decidabilityProperty p).pr1 in
  (match c with
   | Coq_ii1 _ -> assert false (* absurd case *)
   | Coq_ii2 _ -> Coq_paths_refl)

type 'x decidableSubtypeCarrier = ('x, hProptoType) total2

type 'x decidableSubtypeCarrier' = ('x, bool) hfiber

(** val decidableSubtypeCarrier_weq :
    'a1 coq_DecidableSubtype -> ('a1 decidableSubtypeCarrier', 'a1
    decidableSubtypeCarrier) weq **)

let decidableSubtypeCarrier_weq p =
  weqfibtototal (fun x ->
    let c = (decidabilityProperty (p x)).pr1 in
    (match c with
     | Coq_ii1 a ->
       weqiff (logeq_both_true Coq_paths_refl a)
         (isasetbool Coq_true Coq_true)
         (propproperty (coq_DecidableProposition_to_hProp (p x)))
     | Coq_ii2 b ->
       weqiff (logeq_both_false nopathsfalsetotrue b)
         (isasetbool Coq_false Coq_true)
         (propproperty (coq_DecidableProposition_to_hProp (p x)))))

(** val coq_DecidableSubtype_to_hsubtype :
    'a1 coq_DecidableSubtype -> 'a1 hsubtype **)

let coq_DecidableSubtype_to_hsubtype p x =
  coq_DecidableProposition_to_hProp (p x)

(** val coq_DecidableRelation_to_hrel :
    'a1 coq_DecidableRelation -> 'a1 hrel **)

let coq_DecidableRelation_to_hrel p x y =
  coq_DecidableProposition_to_hProp (p x y)

(** val natlth_DecidableProposition : nat coq_DecidableRelation **)

let natlth_DecidableProposition =
  decrel_to_DecidableRelation natlthdec

(** val natleh_DecidableProposition : nat coq_DecidableRelation **)

let natleh_DecidableProposition =
  decrel_to_DecidableRelation natlehdec

(** val natgth_DecidableProposition : nat coq_DecidableRelation **)

let natgth_DecidableProposition =
  decrel_to_DecidableRelation natgthdec

(** val natgeh_DecidableProposition : nat coq_DecidableRelation **)

let natgeh_DecidableProposition =
  decrel_to_DecidableRelation natgehdec

(** val nateq_DecidableProposition : nat coq_DecidableRelation **)

let nateq_DecidableProposition =
  decrel_to_DecidableRelation natdeceq

(** val natneq_DecidableProposition : nat coq_DecidableRelation **)

let natneq_DecidableProposition =
  decrel_to_DecidableRelation natdecneq

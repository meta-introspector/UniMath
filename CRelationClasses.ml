open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a crelation = __

type ('a, 'b) arrow = 'a -> 'b

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip f x y =
  f y x

type ('a, 'b) iffT = ('a -> 'b, 'b -> 'a) prod

type ('a, 'r) coq_Reflexive = 'a -> 'r

(** val reflexivity : ('a1, 'a2) coq_Reflexive -> 'a1 -> 'a2 **)

let reflexivity reflexive =
  reflexive

type ('a, 'r) complement = __

type ('a, 'r) coq_Irreflexive = ('a, ('a, 'r) complement) coq_Reflexive

type ('a, 'r) coq_Symmetric = 'a -> 'a -> 'r -> 'r

(** val symmetry : ('a1, 'a2) coq_Symmetric -> 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let symmetry symmetric =
  symmetric

type ('a, 'r) coq_Transitive = 'a -> 'a -> 'a -> 'r -> 'r -> 'r

(** val transitivity :
    ('a1, 'a2) coq_Transitive -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 **)

let transitivity transitive =
  transitive

type ('a, 'r) coq_PreOrder = { coq_PreOrder_Reflexive : ('a, 'r) coq_Reflexive;
                               coq_PreOrder_Transitive : ('a, 'r)
                                                         coq_Transitive }

(** val coq_PreOrder_Reflexive :
    ('a1, 'a2) coq_PreOrder -> ('a1, 'a2) coq_Reflexive **)

let coq_PreOrder_Reflexive preOrder =
  preOrder.coq_PreOrder_Reflexive

(** val coq_PreOrder_Transitive :
    ('a1, 'a2) coq_PreOrder -> ('a1, 'a2) coq_Transitive **)

let coq_PreOrder_Transitive preOrder =
  preOrder.coq_PreOrder_Transitive

type ('a, 'r) coq_StrictOrder = { coq_StrictOrder_Irreflexive : ('a, 'r)
                                                                coq_Irreflexive;
                                  coq_StrictOrder_Transitive : ('a, 'r)
                                                               coq_Transitive }

(** val coq_StrictOrder_Transitive :
    ('a1, 'a2) coq_StrictOrder -> ('a1, 'a2) coq_Transitive **)

let coq_StrictOrder_Transitive strictOrder =
  let { coq_StrictOrder_Irreflexive = _; coq_StrictOrder_Transitive = x } =
    strictOrder
  in
  let strictOrder_Transitive = Obj.magic x in Obj.magic strictOrder_Transitive

type ('a, 'r) coq_PER = { coq_PER_Symmetric : ('a, 'r) coq_Symmetric;
                          coq_PER_Transitive : ('a, 'r) coq_Transitive }

(** val coq_PER_Symmetric : ('a1, 'a2) coq_PER -> ('a1, 'a2) coq_Symmetric **)

let coq_PER_Symmetric pER =
  pER.coq_PER_Symmetric

(** val coq_PER_Transitive :
    ('a1, 'a2) coq_PER -> ('a1, 'a2) coq_Transitive **)

let coq_PER_Transitive pER =
  pER.coq_PER_Transitive

type ('a, 'r) coq_Equivalence = { coq_Equivalence_Reflexive : ('a, 'r)
                                                              coq_Reflexive;
                                  coq_Equivalence_Symmetric : ('a, 'r)
                                                              coq_Symmetric;
                                  coq_Equivalence_Transitive : ('a, 'r)
                                                               coq_Transitive }

(** val coq_Equivalence_Reflexive :
    ('a1, 'a2) coq_Equivalence -> ('a1, 'a2) coq_Reflexive **)

let coq_Equivalence_Reflexive equivalence =
  equivalence.coq_Equivalence_Reflexive

(** val coq_Equivalence_Symmetric :
    ('a1, 'a2) coq_Equivalence -> ('a1, 'a2) coq_Symmetric **)

let coq_Equivalence_Symmetric equivalence =
  equivalence.coq_Equivalence_Symmetric

(** val coq_Equivalence_Transitive :
    ('a1, 'a2) coq_Equivalence -> ('a1, 'a2) coq_Transitive **)

let coq_Equivalence_Transitive equivalence =
  equivalence.coq_Equivalence_Transitive

(** val coq_Equivalence_PER :
    ('a1, 'a2) coq_Equivalence -> ('a1, 'a2) coq_PER **)

let coq_Equivalence_PER h =
  { coq_PER_Symmetric = h.coq_Equivalence_Symmetric; coq_PER_Transitive =
    h.coq_Equivalence_Transitive }

type ('a, 'eqA, 'r) coq_Antisymmetric = 'a -> 'a -> 'r -> 'r -> 'eqA

(** val antisymmetry :
    ('a1, 'a2) coq_Equivalence -> ('a1, 'a2, 'a3) coq_Antisymmetric -> 'a1 ->
    'a1 -> 'a3 -> 'a3 -> 'a2 **)

let antisymmetry _ antisymmetric =
  antisymmetric

type ('a, 'r, 'x) subrelation = 'a -> 'a -> 'r -> 'x

(** val is_subrelation :
    ('a1, 'a2, 'a3) subrelation -> 'a1 -> 'a1 -> 'a2 -> 'a3 **)

let is_subrelation subrelation0 =
  subrelation0

(** val subrelation_symmetric :
    ('a1, 'a2) coq_Symmetric -> ('a1, 'a2, 'a2) subrelation **)

let subrelation_symmetric h x y h' =
  symmetry h y x h'

(** val flip_Reflexive :
    ('a1, 'a2) coq_Reflexive -> ('a1, 'a2) coq_Reflexive **)

let flip_Reflexive h =
  h

(** val flip_Symmetric :
    ('a1, 'a2) coq_Symmetric -> ('a1, 'a2) coq_Symmetric **)

let flip_Symmetric h x y h0 =
  symmetry h y x h0

(** val flip_Transitive :
    ('a1, 'a2) coq_Transitive -> ('a1, 'a2) coq_Transitive **)

let flip_Transitive h x y z h0 h' =
  transitivity h z y x h' h0

(** val flip_Antisymmetric :
    ('a1, 'a2) coq_Equivalence -> ('a1, 'a2, 'a3) coq_Antisymmetric -> ('a1,
    'a2, 'a3) coq_Antisymmetric **)

let flip_Antisymmetric _ h x y x0 x1 =
  h x y x1 x0

(** val flip_PreOrder : ('a1, 'a2) coq_PreOrder -> ('a1, 'a2) coq_PreOrder **)

let flip_PreOrder h =
  let { coq_PreOrder_Reflexive = preOrder_Reflexive;
    coq_PreOrder_Transitive = preOrder_Transitive } = h
  in
  { coq_PreOrder_Reflexive = preOrder_Reflexive; coq_PreOrder_Transitive =
  (fun x y z x0 x1 -> preOrder_Transitive z y x x1 x0) }

(** val flip_StrictOrder :
    ('a1, 'a2) coq_StrictOrder -> ('a1, 'a2) coq_StrictOrder **)

let flip_StrictOrder h =
  let { coq_StrictOrder_Irreflexive = _; coq_StrictOrder_Transitive = x } = h
  in
  let strictOrder_Transitive = Obj.magic x in
  Obj.magic { coq_StrictOrder_Irreflexive = (Obj.magic __);
    coq_StrictOrder_Transitive = (fun x0 y z x1 x2 ->
    strictOrder_Transitive z y x0 x2 x1) }

(** val flip_PER : ('a1, 'a2) coq_PER -> ('a1, 'a2) coq_PER **)

let flip_PER h =
  let { coq_PER_Symmetric = pER_Symmetric; coq_PER_Transitive =
    pER_Transitive } = h
  in
  { coq_PER_Symmetric = (fun x y x0 -> pER_Symmetric y x x0);
  coq_PER_Transitive = (fun x y z x0 x1 -> pER_Transitive z y x x1 x0) }

(** val flip_Equivalence :
    ('a1, 'a2) coq_Equivalence -> ('a1, 'a2) coq_Equivalence **)

let flip_Equivalence h =
  let { coq_Equivalence_Reflexive = equivalence_Reflexive;
    coq_Equivalence_Symmetric = equivalence_Symmetric;
    coq_Equivalence_Transitive = equivalence_Transitive } = h
  in
  { coq_Equivalence_Reflexive = equivalence_Reflexive;
  coq_Equivalence_Symmetric = (fun x y x0 -> equivalence_Symmetric y x x0);
  coq_Equivalence_Transitive = (fun x y z x0 x1 ->
  equivalence_Transitive z y x x1 x0) }

(** val eq_equivalence : ('a1, __) coq_Equivalence **)

let eq_equivalence =
  { coq_Equivalence_Reflexive = (Obj.magic __); coq_Equivalence_Symmetric =
    (Obj.magic __); coq_Equivalence_Transitive = (Obj.magic __) }

(** val iff_equivalence : (__, __) coq_Equivalence **)

let iff_equivalence =
  { coq_Equivalence_Reflexive = (Obj.magic __); coq_Equivalence_Symmetric =
    (Obj.magic __); coq_Equivalence_Transitive = (Obj.magic __) }

(** val arrow_Reflexive_obligation_1 : ('a1, 'a1) arrow **)

let arrow_Reflexive_obligation_1 x =
  x

(** val arrow_Reflexive : (__, __) arrow **)

let arrow_Reflexive =
  arrow_Reflexive_obligation_1

(** val arrow_Transitive_obligation_1 :
    ('a1, 'a2) arrow -> ('a2, 'a3) arrow -> ('a1, 'a3) arrow **)

let arrow_Transitive_obligation_1 x x0 x1 =
  x0 (x x1)

(** val arrow_Transitive :
    (__, __) arrow -> (__, __) arrow -> (__, __) arrow **)

let arrow_Transitive =
  arrow_Transitive_obligation_1

(** val iffT_Reflexive : (__, __) iffT **)

let iffT_Reflexive =
  Coq_pair ((fun x -> x), (fun x -> x))

(** val iffT_Symmetric : (__, __) iffT -> (__, __) iffT **)

let iffT_Symmetric = function
| Coq_pair (a, b) -> Coq_pair (b, a)

(** val iffT_Transitive : (__, __) iffT -> (__, __) iffT -> (__, __) iffT **)

let iffT_Transitive x = function
| Coq_pair (a, b) ->
  let Coq_pair (a0, b0) = x in
  Coq_pair ((fun x1 -> let x2 = a0 x1 in a x2), (fun x1 ->
  let x2 = b x1 in b0 x2))

type ('a, 'x0, 'x) relation_equivalence = 'a -> 'a -> ('x0, 'x) iffT

type ('a, 'r, 'x) relation_conjunction = ('r, 'x) prod

type ('a, 'r, 'x) relation_disjunction = ('r, 'x) sum

(** val relation_equivalence_equivalence :
    ('a1 crelation, ('a1, __, __) relation_equivalence) coq_Equivalence **)

let relation_equivalence_equivalence =
  { coq_Equivalence_Reflexive = (fun _ _ _ -> Coq_pair ((fun x -> x),
    (fun x -> x))); coq_Equivalence_Symmetric = (fun _ _ x x0 y0 -> Coq_pair
    ((fun x1 ->
    let x2 = x x0 in let x3 = x2 y0 in let Coq_pair (_, b) = x3 in b x1),
    (fun x1 ->
    let x2 = x x0 in let x3 = x2 y0 in let Coq_pair (a, _) = x3 in a x1)));
    coq_Equivalence_Transitive = (fun _ _ _ x x0 x1 y0 ->
    let x2 = x x1 y0 in
    let x3 = x0 x1 y0 in
    let Coq_pair (a, b) = x3 in
    let Coq_pair (a0, b0) = x2 in
    Coq_pair ((fun x4 -> let x5 = a0 x4 in a x5), (fun x4 ->
    let x5 = b x4 in b0 x5))) }

(** val relation_implication_preorder :
    ('a1 crelation, ('a1, __, __) subrelation) coq_PreOrder **)

let relation_implication_preorder =
  { coq_PreOrder_Reflexive = (fun _ _ _ x -> x); coq_PreOrder_Transitive =
    (fun _ _ _ x x0 x1 y0 x2 -> x0 x1 y0 (x x1 y0 x2)) }

type ('a, 'eqA, 'r) coq_PartialOrder =
  ('a, 'eqA, ('a, 'r, 'r) relation_conjunction) relation_equivalence

(** val partial_order_equivalence :
    ('a1, 'a2) coq_Equivalence -> ('a1, 'a3) coq_PreOrder -> ('a1, 'a2, 'a3)
    coq_PartialOrder -> ('a1, 'a2, ('a1, 'a3, 'a3) relation_conjunction)
    relation_equivalence **)

let partial_order_equivalence _ _ partialOrder =
  partialOrder

(** val partial_order_antisym :
    ('a1, 'a2) coq_Equivalence -> ('a1, 'a3) coq_PreOrder -> ('a1, 'a2, 'a3)
    coq_PartialOrder -> ('a1, 'a2, 'a3) coq_Antisymmetric **)

let partial_order_antisym _ _ h x y x0 x1 =
  let x2 = h x in
  let x3 = x2 y in let Coq_pair (_, b) = x3 in b (Coq_pair (x0, x1))

(** val coq_PartialOrder_inverse :
    ('a1, 'a2) coq_Equivalence -> ('a1, 'a3) coq_PreOrder -> ('a1, 'a2, 'a3)
    coq_PartialOrder -> ('a1, 'a2, 'a3) coq_PartialOrder **)

let coq_PartialOrder_inverse _ _ h x y =
  Coq_pair ((fun x0 -> Coq_pair
    ((let x1 = h x in
      let x2 = x1 y in
      let Coq_pair (a, _) = x2 in
      let x3 = a x0 in let Coq_pair (_, b) = x3 in b),
    (let x1 = h x in
     let x2 = x1 y in
     let Coq_pair (a, _) = x2 in
     let x3 = a x0 in let Coq_pair (a0, _) = x3 in a0))), (fun x0 ->
    let Coq_pair (a, b) = x0 in
    let x1 = h x in
    let x2 = x1 y in let Coq_pair (_, b0) = x2 in b0 (Coq_pair (b, a))))

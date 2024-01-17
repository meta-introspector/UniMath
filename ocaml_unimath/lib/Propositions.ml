open PartA
open PartB
open PartC
open PartD
open Preamble
open UnivalenceAxiom

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type hProp = (coq_UU, __ isaprop) total2

(** val make_hProp : 'a1 isaprop -> hProp **)

let make_hProp is =
  { pr1 = __; pr2 = is }

type hProptoType = __

(** val propproperty : hProp -> __ isaprop **)

let propproperty p =
  p.pr2

type tildehProp = (hProp, hProptoType) total2

(** val make_tildehProp : hProp -> hProptoType -> tildehProp **)

let make_tildehProp p p0 =
  { pr1 = p; pr2 = p0 }

(** val subtypeInjectivity_prop :
    ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2
    -> (('a1, hProptoType) total2 paths, 'a1 paths) weq **)

let subtypeInjectivity_prop b x y =
  subtypeInjectivity (fun x0 -> propproperty (b x0)) x y

(** val subtypePath_prop :
    ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2
    -> 'a1 paths -> ('a1, hProptoType) total2 paths **)

let subtypePath_prop b s s' =
  invmap (subtypeInjectivity_prop b s s')

(** val impred_prop : ('a1 -> hProp) -> ('a1 -> hProptoType) isaprop **)

let impred_prop p =
  impred (S O) (fun t -> propproperty (p t))

(** val isaprop_total2 :
    hProp -> (hProptoType -> hProp) -> (hProptoType, hProptoType) total2
    isaprop **)

let isaprop_total2 x y =
  isofhleveltotal2 (S O) (propproperty x) (fun x0 -> propproperty (y x0))

(** val isaprop_forall_hProp :
    ('a1 -> hProp) -> ('a1 -> hProptoType) isaprop **)

let isaprop_forall_hProp y =
  impred_isaprop (fun x -> propproperty (y x))

(** val forall_hProp : ('a1 -> hProp) -> hProp **)

let forall_hProp y =
  make_hProp (isaprop_forall_hProp y)

type 'x ishinh_UUU = hProp -> ('x -> hProptoType) -> hProptoType

(** val isapropishinh : 'a1 ishinh_UUU isaprop **)

let isapropishinh =
  impred (S O) (fun p -> impred (S O) (fun _ -> p.pr2))

(** val ishinh : hProp **)

let ishinh =
  make_hProp isapropishinh

(** val hinhpr : 'a1 -> hProptoType **)

let hinhpr x =
  Obj.magic (fun _ f -> f x)

(** val hinhfun : ('a1 -> 'a2) -> hProptoType -> hProptoType **)

let hinhfun f isx =
  Obj.magic (fun p yp -> Obj.magic isx p (fun x -> yp (f x)))

(** val hinhuniv :
    hProp -> ('a1 -> hProptoType) -> hProptoType -> hProptoType **)

let hinhuniv p f wit =
  Obj.magic wit p f

(** val factor_through_squash :
    'a2 isaprop -> ('a1 -> 'a2) -> hProptoType -> 'a2 **)

let factor_through_squash i f h =
  Obj.magic hinhuniv { pr1 = __; pr2 = i } f h

(** val squash_to_prop : hProptoType -> 'a2 isaprop -> ('a1 -> 'a2) -> 'a2 **)

let squash_to_prop h i f =
  Obj.magic hinhuniv { pr1 = __; pr2 = i } f h

(** val hinhand : hProptoType -> hProptoType -> hProptoType **)

let hinhand inx1 iny1 =
  Obj.magic (fun p -> ddualand (Obj.magic inx1 p) (Obj.magic iny1 p))

(** val hinhuniv2 :
    hProp -> ('a1 -> 'a2 -> hProptoType) -> hProptoType -> hProptoType ->
    hProptoType **)

let hinhuniv2 p f isx isy =
  hinhuniv p (fun xy -> f xy.pr1 xy.pr2) (hinhand isx isy)

(** val hinhfun2 :
    ('a1 -> 'a2 -> 'a3) -> hProptoType -> hProptoType -> hProptoType **)

let hinhfun2 f isx isy =
  hinhfun (fun xy -> f xy.pr1 xy.pr2) (hinhand isx isy)

(** val hinhunivcor1 : hProp -> hProptoType -> hProptoType **)

let hinhunivcor1 p =
  hinhuniv p idfun

(** val weqishinhnegtoneg : (hProptoType, 'a1 neg) weq **)

let weqishinhnegtoneg =
  let lg = { pr1 = (hinhuniv (make_hProp isapropneg) (fun nx -> nx)); pr2 =
    hinhpr }
  in
  weqimplimpl (Obj.magic lg).pr1 lg.pr2 ishinh.pr2 isapropneg

(** val weqnegtonegishinh : ('a1 neg, hProptoType neg) weq **)

let weqnegtonegishinh =
  let lg = { pr1 = (negf hinhpr); pr2 = (fun nx ->
    hinhuniv (make_hProp isapropempty) nx) }
  in
  weqimplimpl (Obj.magic lg).pr2 lg.pr1 isapropneg isapropneg

(** val hinhcoprod : hProptoType -> hProptoType **)

(* let hinhcoprod is = *)
(*   Obj.magic (fun p cP -> *)
(*     let cPX = fun x -> cP (Coq_ii1 x) in *)
(*     let cPY = fun y -> cP (Coq_ii2 y) in *)
(*     let is1P = Obj.magic is p in *)
(*     let f = sumofmaps (hinhuniv p cPX) (hinhuniv p cPY) in is1P f) *)

(** val decidable_ishinh : 'a1 decidable -> hProptoType decidable **)

let decidable_ishinh = function
| Coq_ii1 a -> Coq_ii1 (hinhpr a)
| Coq_ii2 b -> Coq_ii2 (fun p -> squash_to_prop p isapropempty b)

type ('x, 'y) image = ('y, hProptoType) total2

(** val make_image :
    ('a1 -> 'a2) -> 'a2 -> hProptoType -> ('a2, hProptoType) total2 **)

let make_image _ x x0 =
  { pr1 = x; pr2 = x0 }

(** val pr1image : ('a1 -> 'a2) -> ('a2, hProptoType) total2 -> 'a2 **)

let pr1image _ t =
  t.pr1

(** val prtoimage : ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) image **)

let prtoimage f x0 =
  make_image f (f x0) (hinhpr (make_hfiber f (f x0) x0 Coq_paths_refl))

type ('x, 'y) issurjective = 'y -> hProptoType

(** val isapropissurjective :
    ('a1 -> 'a2) -> ('a1, 'a2) issurjective isaprop **)

let isapropissurjective _ =
  impred (S O) (fun _ -> ishinh.pr2)

(** val isinclpr1image :
    ('a1 -> 'a2) -> (('a2, hProptoType) total2, 'a2) isincl **)

let isinclpr1image _ =
  isofhlevelfpr1 (S O) (fun _ -> ishinh.pr2)

(** val issurjprtoimage :
    ('a1 -> 'a2) -> ('a1, ('a1, 'a2) image) issurjective **)

let issurjprtoimage f z =
  let f' = prtoimage f in
  let ff = pr1weq (invweq (samehfibers f' (pr1image f) (isinclpr1image f) z))
  in
  hinhfun ff z.pr2

(** val issurjcomp :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) issurjective -> ('a2, 'a3)
    issurjective -> ('a1, 'a3) issurjective **)

let issurjcomp f g isf isg z =
  hinhuniv ishinh (fun ye -> hinhfun (hfibersftogf f g z ye) (isf ye.pr1))
    (isg z)

(** val issurjtwooutof3b :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) issurjective -> ('a2, 'a3)
    issurjective **)

let issurjtwooutof3b f g isgf z =
  hinhfun (hfibersgftog f g z) (isgf z)

(** val isweqinclandsurj :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> ('a1, 'a2) issurjective -> ('a1,
    'a2) isweq **)

let isweqinclandsurj _ hincl hsurj y =
  let h = make_hProp isapropiscontr in
  Obj.magic hsurj y h (fun x -> iscontraprop1 (hincl y) x)

(** val issurjectiveweq :
    ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) issurjective **)

let issurjectiveweq _ h y =
  hinhpr (h y).pr1

(** val htrue : hProp **)

let htrue =
  make_hProp isapropunit

(** val hfalse : hProp **)

let hfalse =
  make_hProp isapropempty

(** val hconj : hProp -> hProp -> hProp **)

let hconj p q =
  make_hProp (isapropdirprod p.pr2 q.pr2)

(** val hdisj : hProp **)

let hdisj =
  ishinh

(** val hdisj_in1 : 'a1 -> hProptoType **)

let hdisj_in1 x =
  hinhpr (Coq_ii1 x)

(** val hdisj_in2 : 'a2 -> hProptoType **)

let hdisj_in2 x =
  hinhpr (Coq_ii2 x)

(** val disjoint_disjunction :
    hProp -> hProp -> (hProptoType -> hProptoType -> empty) -> hProp **)

let disjoint_disjunction p q n =
  { pr1 = __; pr2 = (isapropcoprod (propproperty p) (propproperty q) n) }

(** val hneg : hProp **)

let hneg =
  make_hProp isapropneg

(** val himpl : hProp -> hProp **)

let himpl q =
  { pr1 = __; pr2 = (impred (S O) (fun _ -> q.pr2)) }

(** val hexists : hProp **)

let hexists =
  ishinh

(** val wittohexists : 'a1 -> 'a2 -> hProptoType **)

let wittohexists x is =
  hinhpr { pr1 = x; pr2 = is }

(** val total2tohexists : ('a1, 'a2) total2 -> hProptoType **)

let total2tohexists =
  hinhpr

(** val weqneghexistsnegtotal2 :
    (hProptoType neg, ('a1, 'a2) total2 neg) weq **)

let weqneghexistsnegtotal2 =
  let lg = { pr1 = (negf total2tohexists); pr2 = (fun nt2 ->
    hinhuniv hfalse nt2) }
  in
  weqimplimpl lg.pr1 (Obj.magic lg).pr2 isapropneg isapropneg

(** val islogeqcommhdisj :
    hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqcommhdisj _ _ =
  { pr1 = (hinhfun coprodcomm); pr2 = (hinhfun coprodcomm) }

(** val hconjtohdisj : hProp -> hProptoType -> hProptoType **)

let hconjtohdisj r x0 =
  let s1 = fun x1 ->
    let s2 = fun x2 ->
      match x2 with
      | Coq_ii1 a -> (Obj.magic x0).pr1 a
      | Coq_ii2 b -> (Obj.magic x0).pr2 b
    in
    hinhuniv r s2 x1
  in
  Obj.magic s1

(** val hexistsnegtonegforall : hProptoType -> ('a1 -> 'a2) neg **)

let hexistsnegtonegforall x =
  Obj.magic hinhuniv (make_hProp isapropneg) (fun t2 ->
    Obj.magic (fun f2 -> let x0 = t2.pr1 in t2.pr2 (f2 x0))) x

(** val forallnegtoneghexists : ('a1 -> 'a2 neg) -> hProptoType neg **)

let forallnegtoneghexists nf =
  Obj.magic hinhuniv hfalse (fun t2 ->
    let x = t2.pr1 in let f = t2.pr2 in Obj.magic nf x f)

(** val neghexisttoforallneg : hProptoType -> 'a1 -> hProptoType **)

let neghexisttoforallneg nhe x =
  Obj.magic (fun fx -> Obj.magic nhe (hinhpr { pr1 = x; pr2 = fx }))

(** val weqforallnegtonegexists : ('a1 -> hProptoType, hProptoType) weq **)

let weqforallnegtonegexists =
  weqimplimpl (Obj.magic forallnegtoneghexists) neghexisttoforallneg
    (impred (S O) (fun _ -> isapropneg)) isapropneg

(** val tonegdirprod : hProptoType -> hProptoType **)

let tonegdirprod =
  hinhuniv (make_hProp isapropneg) (fun c ->
    match c with
    | Coq_ii1 a -> Obj.magic (fun xy -> a xy.pr1)
    | Coq_ii2 b -> Obj.magic (fun xy -> b xy.pr2))

(** val weak_fromnegdirprod :
    hProp -> hProp -> hProptoType -> hProptoType dneg **)

let weak_fromnegdirprod _ _ npq k =
  let e = fun n -> k (hdisj_in2 n) in
  let n = fun p -> e (fun q -> Obj.magic npq { pr1 = p; pr2 = q }) in
  k (hdisj_in1 n)

(** val tonegcoprod : (hProptoType, hProptoType) dirprod -> hProptoType **)

let tonegcoprod is =
  Obj.magic (fun c ->
    match c with
    | Coq_ii1 a -> (Obj.magic is).pr1 a
    | Coq_ii2 b -> (Obj.magic is).pr2 b)

(** val toneghdisj : (hProptoType, hProptoType) dirprod -> hProptoType **)

let toneghdisj is =
  let x0 = fun _ -> weqnegtonegishinh.pr1 in Obj.magic x0 __ (tonegcoprod is)

(** val fromnegcoprod : hProptoType -> (hProptoType, hProptoType) dirprod **)

let fromnegcoprod is =
  { pr1 = (Obj.magic (fun x -> Obj.magic is (Coq_ii1 x))); pr2 =
    (Obj.magic (fun y -> Obj.magic is (Coq_ii2 y))) }

(** val fromnegcoprod_prop : hProp -> hProp -> hProptoType -> hProptoType **)

let fromnegcoprod_prop _ _ n =
  let n' = negf hinhpr (Obj.magic n) in Obj.magic fromnegcoprod n'

(** val hdisjtoimpl : hProp -> hProptoType -> hProptoType -> hProptoType **)

let hdisjtoimpl q =
  let int = impred (S O) (fun _ -> q.pr2) in
  Obj.magic hinhuniv (make_hProp int) (fun pq ->
    match pq with
    | Coq_ii1 _ -> Obj.magic (fun _ -> assert false (* absurd case *))
    | Coq_ii2 b -> Obj.magic (fun _ -> b))

(** val isdecprophdisj :
    'a1 isdecprop -> 'a2 isdecprop -> hProptoType isdecprop **)

let isdecprophdisj isx isy =
  isdecpropif hdisj.pr2
    (let c = isx.pr1 in
     match c with
     | Coq_ii1 a -> Coq_ii1 (hinhpr (Coq_ii1 a))
     | Coq_ii2 b ->
       let c0 = isy.pr1 in
       (match c0 with
        | Coq_ii1 a -> Coq_ii1 (hinhpr (Coq_ii2 a))
        | Coq_ii2 b0 ->
          Coq_ii2
            (Obj.magic toneghdisj (make_dirprod (Obj.magic b) (Obj.magic b0)))))

(** val isinhdneg : hProp **)

let isinhdneg =
  make_hProp isapropdneg

(** val inhdnegpr : 'a1 -> hProptoType **)

let inhdnegpr =
  Obj.magic todneg

(** val inhdnegfun : ('a1 -> 'a2) -> hProptoType -> hProptoType **)

let inhdnegfun f =
  Obj.magic dnegf f

(** val inhdneguniv :
    ('a2, 'a2 dneg) isweq -> ('a1 -> 'a2) -> hProptoType -> 'a2 **)

let inhdneguniv is xp inx0 =
  invmap (make_weq todneg is) (dnegf xp (Obj.magic inx0))

(** val inhdnegand : hProptoType -> hProptoType -> hProptoType **)

let inhdnegand inx0 iny0 =
  Obj.magic dneganddnegimpldneg inx0 iny0

(** val hinhimplinhdneg : hProptoType -> hProptoType **)

let hinhimplinhdneg inx1 =
  Obj.magic inx1 hfalse

(** val hPropUnivalence :
    hProp -> hProp -> (hProptoType -> hProptoType) -> (hProptoType ->
    hProptoType) -> hProp paths **)

let hPropUnivalence p q f g =
  subtypePath (fun _ -> isapropisaprop) p q
    (propositionalUnivalenceAxiom (propproperty p) (propproperty q) f g)

(** val eqweqmaphProp :
    hProp -> hProp -> hProp paths -> (hProptoType, hProptoType) weq **)

let eqweqmaphProp _ _ _ =
  idweq

(** val weqtopathshProp :
    hProp -> hProp -> (hProptoType, hProptoType) weq -> hProp paths **)

let weqtopathshProp p p' w =
  hPropUnivalence p p' (pr1weq w) (pr1weq (invweq w))

(** val weqpathsweqhProp :
    hProp -> hProp -> (hProptoType, hProptoType) weq -> (hProptoType,
    hProptoType) weq paths **)

let weqpathsweqhProp p p' w =
  proofirrelevance (isapropweqtoprop p'.pr2)
    (eqweqmaphProp p p' (weqtopathshProp p p' w)) w

(** val univfromtwoaxiomshProp :
    hProp -> hProp -> (hProp paths, (hProptoType, hProptoType) weq) isweq **)

let univfromtwoaxiomshProp p p' =
  let f = totalfun (fun xY -> eqweqmaphProp xY.pr1 xY.pr2) in
  let g = totalfun (fun xY -> weqtopathshProp xY.pr1 xY.pr2) in
  let efg = fun z2 ->
    let xY = z2.pr1 in
    let w = z2.pr2 in
    maponpaths (fun w0 -> { pr1 = xY; pr2 = w0 })
      (eqweqmaphProp xY.pr1 xY.pr2 (weqtopathshProp xY.pr1 xY.pr2 w)) w
      (weqpathsweqhProp xY.pr1 xY.pr2 w)
  in
  let h = fun a1 -> a1.pr1.pr1 in
  let egf0 = fun _ -> Coq_paths_refl in
  let egf1 = fun a1 a1' x ->
    let x' = maponpaths (fun t -> t.pr1) a1'.pr1 a1.pr1 x in
    invmaponpathsweq (make_weq h isweqpr1pr1) a1' a1 x'
  in
  let egf = fun a1 -> egf1 a1 (g (f a1)) (egf0 a1) in
  let is2 = isweq_iso f g egf efg in
  isweqtotaltofib (fun xY -> eqweqmaphProp xY.pr1 xY.pr2) is2
    (make_dirprod p p')

(** val weqeqweqhProp :
    hProp -> hProp -> (hProp paths, (hProptoType, hProptoType) weq) weq **)

let weqeqweqhProp p p' =
  make_weq (eqweqmaphProp p p') (univfromtwoaxiomshProp p p')

(** val isasethProp : hProp isaset **)

let isasethProp x x' =
  isofhlevelweqb (S O) (weqeqweqhProp x x') (isapropweqtoprop x'.pr2)

(** val weqpathsweqhProp' :
    hProp -> hProp -> hProp paths -> hProp paths paths **)

let weqpathsweqhProp' p p' e =
  let x = weqtopathshProp p p' (eqweqmaphProp p p' e) in
  (Obj.magic isasethProp p p' x e).pr1

(** val iscontrtildehProp : tildehProp iscontr **)

let iscontrtildehProp =
  { pr1 = { pr1 = htrue; pr2 = (Obj.magic Coq_tt) }; pr2 = (fun tP ->
    let p = tP.pr1 in
    let p0 = tP.pr2 in
    invmaponpathsincl (fun t -> t.pr1) (isinclpr1 (fun p1 -> p1.pr2)) { pr1 =
      p; pr2 = p0 } { pr1 = htrue; pr2 = (Obj.magic Coq_tt) }
      (hPropUnivalence p htrue (fun _ -> Obj.magic Coq_tt) (fun _ -> p0))) }

(** val isaproptildehProp : tildehProp isaprop **)

let isaproptildehProp =
  isapropifcontr iscontrtildehProp

(** val isasettildehProp : tildehProp isaset **)

let isasettildehProp =
  isasetifcontr iscontrtildehProp

(** val logeqweq :
    hProp -> hProp -> (hProptoType -> hProptoType) -> (hProptoType ->
    hProptoType) -> (hProptoType, hProptoType) weq **)

let logeqweq p q f g =
  weqimplimpl f g p.pr2 q.pr2

(** val total2_paths_hProp_equiv :
    ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2
    -> (('a1, hProptoType) total2 paths, 'a1 paths) weq **)

let total2_paths_hProp_equiv b x y =
  subtypeInjectivity (fun a -> (b a).pr2) x y


(*prop0 Propositions0.ml
*)
    let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val ishinh_irrel : 'a1 -> hProptoType -> hProptoType paths **)

let ishinh_irrel x x' =
  proofirrelevance (propproperty ishinh) (hinhpr x) x'

(** val squash_to_hProp :
    hProp -> hProptoType -> ('a1 -> hProptoType) -> hProptoType **)

let squash_to_hProp q h f =
  hinhuniv q f h

(** val hdisj_impl_1 :
    hProp -> hProp -> hProptoType -> (hProptoType -> hProptoType) ->
    hProptoType **)

let hdisj_impl_1 p _ o f =
  squash_to_hProp p o (fun x ->
    match x with
    | Coq_ii1 h -> h
    | Coq_ii2 h -> f h)

(** val hdisj_impl_2 :
    hProp -> hProp -> hProptoType -> (hProptoType -> hProptoType) ->
    hProptoType **)

let hdisj_impl_2 _ q o f =
  squash_to_hProp q o (fun x ->
    match x with
    | Coq_ii1 h -> f h
    | Coq_ii2 h -> h)

(** val weqlogeq : hProp -> hProp -> (hProp paths, hProptoType) weq **)


(** val decidable_proof_by_contradiction :
    hProp -> hProptoType decidable -> hProptoType -> hProptoType **)

let decidable_proof_by_contradiction _ dec nnp =
  match dec with
  | Coq_ii1 a -> a
  | Coq_ii2 b -> fromempty (Obj.magic nnp b)

(** val proof_by_contradiction :
    hProp -> hProptoType -> hProptoType -> hProptoType **)

let proof_by_contradiction p lem =
  decidable_proof_by_contradiction p (Obj.magic lem p)

(** val dneg_elim_to_LEM :
    (hProp -> hProptoType -> hProptoType) -> hProptoType **)

let weqnegtonegishinh =
  let lg = { pr1 = (negf hinhpr); pr2 = (fun nx ->
    hinhuniv (make_hProp isapropempty) nx) }
  in
  weqimplimpl (Obj.magic lg).pr2 lg.pr1 isapropneg isapropneg

let dneg_elim_to_LEM dne =
  Obj.magic (fun p ->
    Obj.magic dne { pr1 = __; pr2 = (isapropdec p.pr2) } (fun n ->
      let q = weqnegtonegishinh.pr1 n in
      let r = fromnegcoprod_prop p hneg (Obj.magic q) in
      (Obj.magic r).pr2 (Obj.magic r).pr1))

(** val negforall_to_existsneg :
    ('a1 -> hProp) -> hProptoType -> hProptoType -> hProptoType **)

let negforall_to_existsneg p lem nf =
  proof_by_contradiction ishinh lem
    (Obj.magic (fun c ->
      Obj.magic nf (fun x ->
        let q = neghexisttoforallneg c x in proof_by_contradiction (p x) lem q)))

(** val negimpl_to_conj :
    hProp -> hProp -> hProptoType -> hProptoType -> hProptoType **)

let negimpl_to_conj p q lem ni =
  let r = negforall_to_existsneg (fun _ -> q) lem ni in
  squash_to_hProp (hconj p hneg) r (fun x ->
    let p0 = x.pr1 in let nq = x.pr2 in Obj.magic { pr1 = p0; pr2 = nq })

(** val hrel_set : hSet -> hSet **)


(** val isaprop_assume_it_is : ('a1 -> 'a1 isaprop) -> 'a1 isaprop **)

let isaprop_assume_it_is f =
  invproofirrelevance (fun x y -> proofirrelevance (f y) x y)

(** val isaproptotal2 :
    ('a1, 'a2) isPredicate -> ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths) ->
    ('a1, 'a2) total2 isaprop **)

let isaproptotal2 _ _ =
  invproofirrelevance (fun _ _ -> Coq_paths_refl)

(** val squash_rec :
    (hProptoType -> hProp) -> ('a1 -> hProptoType) -> hProptoType ->
    hProptoType **)

let squash_rec p xp x' =
  hinhuniv (p x') xp x'

(** val logeq_if_both_true :
    hProp -> hProp -> hProptoType -> hProptoType -> hProptoType **)

let logeq_if_both_true _ _ p q =
  Obj.magic { pr1 = (fun _ -> q); pr2 = (fun _ -> p) }

(** val logeq_if_both_false :
    hProp -> hProp -> hProptoType -> hProptoType -> hProptoType **)

let logeq_if_both_false _ _ np nq =
  Obj.magic { pr1 = (fun p -> fromempty (Obj.magic np p)); pr2 = (fun q ->
    fromempty (Obj.magic nq q)) }

(** val proofirrelevance_hProp : hProp -> hProptoType isProofIrrelevant **)

let proofirrelevance_hProp x =
  proofirrelevance (propproperty x)

(** val iscontr_hProp : hProp **)

let iscontr_hProp =
  make_hProp isapropiscontr

(** val islogeqassochconj :
    hProp -> hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqassochconj _ _ _ =
  { pr1 = (fun pQR ->
    Obj.magic { pr1 = (Obj.magic pQR).pr1.pr1; pr2 = { pr1 =
      (Obj.magic pQR).pr1.pr2; pr2 = (Obj.magic pQR).pr2 } }); pr2 =
    (fun pQR ->
    Obj.magic { pr1 = { pr1 = (Obj.magic pQR).pr1; pr2 =
      (Obj.magic pQR).pr2.pr1 }; pr2 = (Obj.magic pQR).pr2.pr2 }) }

(** val islogeqcommhconj :
    hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqcommhconj _ _ =
  { pr1 = (fun pQ ->
    Obj.magic { pr1 = (Obj.magic pQ).pr2; pr2 = (Obj.magic pQ).pr1 }); pr2 =
    (fun qP ->
    Obj.magic { pr1 = (Obj.magic qP).pr2; pr2 = (Obj.magic qP).pr1 }) }

(** val islogeqassochdisj :
    hProp -> hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqassochdisj _ _ _ =
  { pr1 =
    (hinhuniv hdisj (fun hPQR ->
      match hPQR with
      | Coq_ii1 a ->
        hinhuniv hdisj (fun hPQ ->
          match hPQ with
          | Coq_ii1 a0 -> hinhpr (Coq_ii1 a0)
          | Coq_ii2 b -> hinhpr (Coq_ii2 (hinhpr (Coq_ii1 b)))) a
      | Coq_ii2 b -> hinhpr (Coq_ii2 (hinhpr (Coq_ii2 b))))); pr2 =
    (hinhuniv hdisj (fun hPQR ->
      match hPQR with
      | Coq_ii1 a -> hinhpr (Coq_ii1 (hinhpr (Coq_ii1 a)))
      | Coq_ii2 b ->
        hinhuniv hdisj (fun hQR ->
          match hQR with
          | Coq_ii1 a -> hinhpr (Coq_ii1 (hinhpr (Coq_ii2 a)))
          | Coq_ii2 b0 -> hinhpr (Coq_ii2 b0)) b)) }

(** val islogeqhconj_absorb_hdisj :
    hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqhconj_absorb_hdisj _ _ =
  { pr1 = (fun hPPQ -> (Obj.magic hPPQ).pr1); pr2 = (fun hP ->
    Obj.magic { pr1 = hP; pr2 = (hinhpr (Coq_ii1 hP)) }) }

(** val islogeqhdisj_absorb_hconj :
    hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqhdisj_absorb_hconj p _ =
  { pr1 =
    (hinhuniv p (fun hPPQ ->
      match hPPQ with
      | Coq_ii1 a -> a
      | Coq_ii2 b -> b.pr1)); pr2 = (fun hP -> hinhpr (Coq_ii1 hP)) }

(** val islogeqhfalse_hdisj : hProp -> (hProptoType, hProptoType) logeq **)

let islogeqhfalse_hdisj p =
  { pr1 =
    (hinhuniv p (fun hPPQ ->
      match hPPQ with
      | Coq_ii1 _ -> assert false (* absurd case *)
      | Coq_ii2 b -> b)); pr2 = (fun hP -> hinhpr (Coq_ii2 hP)) }

(** val islogeqhhtrue_hconj : hProp -> (hProptoType, hProptoType) logeq **)

let islogeqhhtrue_hconj _ =
  { pr1 = (fun hP -> (Obj.magic hP).pr2); pr2 = (fun hP ->
    Obj.magic { pr1 = Coq_tt; pr2 = hP }) }

(** val isassoc_hconj : hProp -> hProp -> hProp -> hProp paths **)

let isassoc_hconj p q r =
  hPropUnivalence (hconj (hconj p q) r) (hconj p (hconj q r))
    (islogeqassochconj p q r).pr1 (islogeqassochconj p q r).pr2

(** val iscomm_hconj : hProp -> hProp -> hProp paths **)

let iscomm_hconj p q =
  hPropUnivalence (hconj p q) (hconj q p) (islogeqcommhconj p q).pr1
    (islogeqcommhconj q p).pr1

(** val isassoc_hdisj : hProp -> hProp -> hProp -> hProp paths **)

let isassoc_hdisj p q r =
  hPropUnivalence hdisj hdisj (islogeqassochdisj p q r).pr1
    (islogeqassochdisj p q r).pr2

(** val iscomm_hdisj : hProp -> hProp -> hProp paths **)

let iscomm_hdisj p q =
  hPropUnivalence hdisj hdisj (islogeqcommhdisj p q).pr1
    (islogeqcommhdisj q p).pr1

(** val hconj_absorb_hdisj : hProp -> hProp -> hProp paths **)

let hconj_absorb_hdisj p q =
  hPropUnivalence (hconj p hdisj) p (islogeqhconj_absorb_hdisj p q).pr1
    (islogeqhconj_absorb_hdisj p q).pr2

(** val hdisj_absorb_hconj : hProp -> hProp -> hProp paths **)

let hdisj_absorb_hconj p q =
  hPropUnivalence hdisj p (islogeqhdisj_absorb_hconj p q).pr1
    (islogeqhdisj_absorb_hconj p q).pr2

(** val hfalse_hdisj : hProp -> hProp paths **)

let hfalse_hdisj p =
  hPropUnivalence hdisj p (islogeqhfalse_hdisj p).pr1
    (islogeqhfalse_hdisj p).pr2

(** val htrue_hconj : hProp -> hProp paths **)

let htrue_hconj p =
  hPropUnivalence (hconj htrue p) p (islogeqhhtrue_hconj p).pr1
    (islogeqhhtrue_hconj p).pr2

(** val squash_uniqueness : 'a1 -> hProptoType -> hProptoType paths **)

let squash_uniqueness x h =
  let x0 = hinhpr x in (Obj.magic propproperty ishinh x0 h).pr1

(** val coq_Unnamed_thm : 'a2 isaprop -> ('a1 -> 'a2) -> 'a1 -> 'a2 paths **)

let coq_Unnamed_thm _ _ _ =
  Coq_paths_refl

(** val factor_dep_through_squash :
    (hProptoType -> 'a2 isaprop) -> ('a1 -> 'a2) -> hProptoType -> 'a2 **)

let factor_dep_through_squash i f h =
  Obj.magic h (make_hProp (i h)) f

(** val factor_through_squash_hProp :
    hProp -> ('a1 -> hProptoType) -> hProptoType -> hProptoType **)

let factor_through_squash_hProp hQ =
  let i = hQ.pr2 in (fun f h -> Obj.magic h { pr1 = __; pr2 = i } f)

(** val funspace_isaset : 'a2 isaset -> ('a1 -> 'a2) isaset **)

let funspace_isaset is =
  Obj.magic impredfun (S (S O)) is

(** val squash_map_uniqueness :
    'a2 isaset -> (hProptoType -> 'a2) -> (hProptoType -> 'a2) -> ('a1, 'a2)
    homot -> (hProptoType, 'a2) homot **)

let squash_map_uniqueness ip g g' h =
  factor_dep_through_squash (fun y -> ip (g y) (g' y)) h

(** val squash_map_epi :
    'a2 isaset -> (hProptoType -> 'a2) -> (hProptoType -> 'a2) -> ('a1 ->
    'a2) paths -> (hProptoType -> 'a2) paths **)

let squash_map_epi ip g g' _ =
  Obj.magic funextsec g g'
    (squash_map_uniqueness (Obj.magic ip) (Obj.magic g) (Obj.magic g')
      (fun _ -> Coq_paths_refl))

(** val uniqueExists :
    'a1 -> 'a1 -> ('a1, 'a2) total2 iscontr -> 'a2 -> 'a2 -> 'a1 paths **)

let uniqueExists a b hexists ha hb =
  let h =
    proofirrelevancecontr hexists { pr1 = a; pr2 = ha } { pr1 = b; pr2 = hb }
  in
  base_paths { pr1 = a; pr2 = ha } { pr1 = b; pr2 = hb } h

(** val isConnected : hProp **)

let isConnected =
  hconj ishinh (forall_hProp (fun _ -> forall_hProp (fun _ -> ishinh)))

(** val predicateOnConnectedType :
    hProptoType -> ('a1 -> hProp) -> 'a1 -> hProptoType -> 'a1 -> hProptoType **)

let predicateOnConnectedType i p x0 p0 x =
  squash_to_hProp (p x) ((Obj.magic i).pr2 x x0) (fun _ -> p0)

(** val isBaseConnected : coq_PointedType -> hProp **)

let isBaseConnected _ =
  forall_hProp (fun _ -> ishinh)

(** val isConnected_isBaseConnected :
    coq_PointedType -> (hProptoType, hProptoType) logeq **)

let isConnected_isBaseConnected x =
  { pr1 = (fun x0 ->
    let ic = (Obj.magic x0).pr2 in Obj.magic (fun x1 -> ic (basepoint x) x1));
    pr2 = (fun ibc ->
    Obj.magic { pr1 = (hinhpr (basepoint x)); pr2 = (fun x0 y ->
      squash_to_hProp ishinh (Obj.magic ibc x0) (fun p ->
        squash_to_hProp ishinh (Obj.magic ibc y) (fun q ->
          hinhpr
            (pathscomp0 x0 (basepoint x) y (pathsinv0 (basepoint x) x0 p) q)))) }) }

(** val coq_BasePointComponent : coq_PointedType -> coq_PointedType **)

let coq_BasePointComponent x =
  pointedType { pr1 = (basepoint x); pr2 = (hinhpr Coq_paths_refl) }

(** val basePointComponent_inclusion :
    coq_PointedType -> underlyingType -> underlyingType **)

let basePointComponent_inclusion _ x =
  (Obj.magic x).pr1

(** val coq_BasePointComponent_isBaseConnected :
    coq_PointedType -> hProptoType **)

let coq_BasePointComponent_isBaseConnected x =
  Obj.magic (fun x0 ->
    let c' = x0.pr2 in
    hinhfun (fun _ ->
      maponpaths (fun x1 -> { pr1 = (basepoint x); pr2 = x1 })
        (hinhpr Coq_paths_refl) c'
        (let x1 = hinhpr Coq_paths_refl in
         (Obj.magic propproperty ishinh x1 c').pr1)) c')

(** val coq_BasePointComponent_isincl :
    coq_PointedType -> (underlyingType, underlyingType) isincl **)

let coq_BasePointComponent_isincl _ =
  isinclpr1 (fun _ -> propproperty ishinh)

(** val coq_BasePointComponent_isweq :
    coq_PointedType -> hProptoType -> (underlyingType, underlyingType) isweq **)

let coq_BasePointComponent_isweq _ bc =
  Obj.magic isweqpr1 (fun x ->
    iscontraprop1 (propproperty ishinh) (Obj.magic bc x))

(** val coq_BasePointComponent_weq :
    coq_PointedType -> hProptoType -> (underlyingType, underlyingType) weq **)

let coq_BasePointComponent_weq x bc =
  make_weq (basePointComponent_inclusion x)
    (coq_BasePointComponent_isweq x bc)

(** val baseConnectedness : coq_PointedType -> hProptoType -> hProptoType **)

let baseConnectedness x p =
  Obj.magic { pr1 = (hinhpr (basepoint x)); pr2 = (fun x0 y ->
    let a = Obj.magic p x0 in
    let b = Obj.magic p y in
    squash_to_prop a (propproperty ishinh) (fun a0 ->
      squash_to_prop b (propproperty ishinh) (fun b0 ->
        hinhpr
          (pathscomp0 x0 (basepoint x) y (pathsinv0 (basepoint x) x0 a0) b0)))) }

(** val predicateOnBaseConnectedType :
    coq_PointedType -> hProptoType -> (underlyingType -> hProp) ->
    hProptoType -> underlyingType -> hProptoType **)

let predicateOnBaseConnectedType _ b p p0 x =
  squash_to_hProp (p x) (Obj.magic b x) (fun _ -> p0)

(** val predicateOnBasePointComponent :
    coq_PointedType -> (underlyingType -> hProp) -> hProptoType ->
    underlyingType -> hProptoType **)

let predicateOnBasePointComponent x p p0 x0 =
  squash_to_hProp (p x0)
    (Obj.magic coq_BasePointComponent_isBaseConnected x x0) (fun _ -> p0)
let weqlogeq p q =
  weqimplimpl (fun _ -> Obj.magic isrefl_logeq) (fun c ->
    hPropUnivalence p q (Obj.magic c).pr1 (Obj.magic c).pr2)
    (isasethProp p q) (propproperty (hequiv p q))

let setquotl0 r c x =
  invmaponpathsincl (Obj.magic pr1setquot (pr1eqrel r))
    (Obj.magic isinclpr1setquot (pr1eqrel (Obj.magic r))) (setquotpr r x.pr1)
    c
    (funextsec
      (Obj.magic pr1setquot (pr1eqrel (Obj.magic r))
        (setquotpr (Obj.magic r) (Obj.magic x).pr1))
      (Obj.magic pr1setquot (pr1eqrel (Obj.magic r)) c) (fun x0 ->
      Obj.magic hPropUnivalence
        (pr1setquot (pr1eqrel (Obj.magic r))
          (setquotpr (Obj.magic r) (Obj.magic x).pr1) x0)
        (pr1setquot (pr1eqrel (Obj.magic r)) (Obj.magic c) x0) (fun r0 ->
        eqax1 (pr1eqrel (Obj.magic r)) (Obj.magic c).pr1 (Obj.magic c).pr2
          (Obj.magic x).pr1 x0 r0 x.pr2) (fun r0 ->
        eqax2 (pr1eqrel (Obj.magic r)) (Obj.magic c).pr1 (Obj.magic c).pr2
          (Obj.magic x).pr1 x0 x.pr2 r0)))
let image_hsubtype_emptyhsubtype f =
  Obj.magic funextsec (image_hsubtype emptysubtype (Obj.magic f))
    emptysubtype (fun y ->
    Obj.magic hPropUnivalence (image_hsubtype emptysubtype (Obj.magic f) y)
      (emptysubtype y) (fun yinfEmpty ->
      factor_through_squash (emptysubtype y).pr2 (fun x -> x.pr2.pr2)
        yinfEmpty) (fun yinEmpty -> fromempty (Obj.magic yinEmpty)))
let posetStructureIdentity x r s =
  { pr1 = (fun e ->
    subtypePath (fun t -> isaprop_isPartialOrder x t) r s
      (let r0 = r.pr1 in
       let s0 = s.pr1 in
       Obj.magic funextfun r0 s0 (fun x0 ->
         Obj.magic funextfun (Obj.magic r0 x0) (Obj.magic s0 x0) (fun y ->
           let e0 = e.pr1 in
           let e' = e.pr2 in
           Obj.magic hPropUnivalence (r0 x0 y) (s0 x0 y) (e0 x0 y) (e' x0 y)))));
    pr2 = (fun _ -> isPosetEquivalence_idweq { pr1 = x; pr2 = r }) }
let iscompsetquotpr r x x' a =
  invmaponpathsincl (Obj.magic pr1setquot (pr1eqrel r))
    (Obj.magic isinclpr1setquot (pr1eqrel (Obj.magic r))) (setquotpr r x)
    (setquotpr r x')
    (funextsec (fun x0 -> Obj.magic pr1eqrel r x x0) (fun x0 ->
      Obj.magic pr1eqrel r x' x0) (fun x0 ->
      Obj.magic hPropUnivalence (pr1eqrel (Obj.magic r) (Obj.magic x) x0)
        (pr1eqrel (Obj.magic r) (Obj.magic x') x0) (fun r0 ->
        eqreltrans (Obj.magic r) (Obj.magic x') (Obj.magic x) x0
          (eqrelsymm r x x' a) r0) (fun x0' ->
        eqreltrans (Obj.magic r) (Obj.magic x) (Obj.magic x') x0 a x0')))

let iscomprelrelif _ l isr i1 i2 x x' y y' rx ry =
  let rx' = isr x x' rx in
  let ry' = isr y y' ry in
  hPropUnivalence (l x y) (l x' y') (fun lxy ->
    let int1 = i1 x x' y rx lxy in i2 x' y y' ry int1) (fun lxy' ->
    let int1 = i1 x' x y' rx' lxy' in i2 x y' y ry' int1)
let weqpathssetquot2l1 r x x' x'' r0 =
  hPropUnivalence (pr1eqrel r x x') (pr1eqrel r x x'') (fun r' ->
    eqreltrans r x x' x'' r' r0) (fun r'' ->
    eqreltrans r x x'' x' r'' (eqrelsymm r x' x'' r0))
let image_hsubtype_id u =
  Obj.magic funextsec (image_hsubtype (Obj.magic u) idfun) u (fun x ->
    Obj.magic hPropUnivalence (image_hsubtype (Obj.magic u) idfun x)
      (Obj.magic u x) (fun xinIdU ->
      factor_through_squash (let x0 = fun x0 -> (u x0).pr2 in Obj.magic x0 x)
        (fun u0 -> u0.pr2.pr2) xinIdU) (fun xinU ->
      hinhpr { pr1 = x; pr2 = { pr1 = Coq_paths_refl; pr2 = xinU } }))
let image_hsubtype_comp u f g =
  Obj.magic funextsec (image_hsubtype u (funcomp f (Obj.magic g)))
    (image_hsubtype (image_hsubtype u f) (Obj.magic g)) (fun z ->
    Obj.magic hPropUnivalence (image_hsubtype u (funcomp f (Obj.magic g)) z)
      (image_hsubtype (image_hsubtype u f) (Obj.magic g) z) (fun zinCompU ->
      factor_through_squash ishinh.pr2 (fun x ->
        hinhpr { pr1 = (f x.pr1); pr2 = { pr1 = x.pr2.pr1; pr2 =
          (hinhpr { pr1 = x.pr1; pr2 = { pr1 =
            (maponpaths f x.pr1 x.pr1 Coq_paths_refl); pr2 = x.pr2.pr2 } }) } })
        zinCompU) (fun zinCompU ->
      factor_through_squash ishinh.pr2 (fun y ->
        factor_through_squash ishinh.pr2 (fun x ->
          hinhpr { pr1 = x.pr1; pr2 = { pr1 =
            (pathscomp0 (funcomp f g x.pr1) (g y.pr1) (Obj.magic z)
              (maponpaths g (f x.pr1) y.pr1 x.pr2.pr1) y.pr2.pr1); pr2 =
            x.pr2.pr2 } }) y.pr2.pr2) zinCompU))
let wosub_univalence x s t =
  remakeweq
    (weqcomp (Obj.magic total2_paths_equiv s t)
      (weqcomp
        (weqbandf
          (Obj.magic hsubtype_univalence
            (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s))
            (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)))
          (fun _ ->
          let s0 = (Obj.magic s).pr1 in
          let v = (Obj.magic s).pr2 in
          let w = (Obj.magic t).pr2 in
          let v0 = v.pr1 in
          let i = v.pr2 in
          let w0 = w.pr1 in
          let j = w.pr2 in
          weqcomp
            (subtypeInjectivity (fun r ->
              propproperty (isWellOrder (carrier_subset x s0) (Obj.magic r)))
              { pr1 = (Obj.magic v0); pr2 = i } { pr1 = (Obj.magic w0); pr2 =
              j })
            (weqimplimpl (fun _ ->
              Obj.magic { pr1 = { pr1 = (fun _ -> idfun); pr2 = { pr1 =
                (fun _ _ le -> le); pr2 = (fun _ _ _ st _ -> st) } }; pr2 =
                { pr1 = (fun _ -> idfun); pr2 = { pr1 = (fun _ _ le -> le);
                pr2 = (fun _ _ _ st _ -> st) } } }) (fun x0 ->
              let pr3 = (Obj.magic x0).pr1 in
              let a = pr3.pr1 in
              let pr4 = pr3.pr2 in
              let b = pr4.pr1 in
              let pr5 = (Obj.magic x0).pr2 in
              let d = pr5.pr1 in
              let pr6 = pr5.pr2 in
              let e = pr6.pr1 in
              let triv = fun f s1 ->
                subtypePath_prop s0 (subtype_inc s0 s0 f s1) s1 Coq_paths_refl
              in
              funextfun (Obj.magic v0) (Obj.magic w0) (fun s1 ->
                Obj.magic funextfun (Obj.magic v0 s1) (Obj.magic w0 s1)
                  (fun t0 ->
                  Obj.magic hPropUnivalence (Obj.magic v0 s1 t0)
                    (Obj.magic w0 s1 t0) (fun le ->
                    let q = b s1 t0 le in
                    let q0 =
                      internal_paths_rew (Obj.magic subtype_inc s0 s0 a s1) q
                        s1 (Obj.magic triv a s1)
                    in
                    internal_paths_rew (Obj.magic subtype_inc s0 s0 a t0) q0
                      t0 (Obj.magic triv a t0)) (fun le ->
                    let q = e s1 t0 le in
                    let q0 =
                      internal_paths_rew (Obj.magic subtype_inc s0 s0 d s1) q
                        s1 (Obj.magic triv d s1)
                    in
                    internal_paths_rew (Obj.magic subtype_inc s0 s0 d t0) q0
                      t0 (Obj.magic triv d t0)))))
              (setproperty (hrel_set (carrier_subset x s0)) v0 w0)
              (propproperty
                (hconj
                  (wosub_le x
                    (Obj.magic { pr1 = s0; pr2 = { pr1 = v0; pr2 = i } })
                    (Obj.magic { pr1 = s0; pr2 = { pr1 = w0; pr2 = j } }))
                  (wosub_le x
                    (Obj.magic { pr1 = s0; pr2 = { pr1 = w0; pr2 = j } })
                    (Obj.magic { pr1 = s0; pr2 = { pr1 = v0; pr2 = i } })))))))
        (weqimplimpl (fun k ->
          Obj.magic { pr1 = (let x0 = k.pr2 in (Obj.magic x0).pr1); pr2 =
            (let x0 = k.pr2 in (Obj.magic x0).pr2) }) (fun c -> { pr1 =
          (fun x0 -> { pr1 =
          (Obj.magic wosub_le_inc x s t (Obj.magic c).pr1 x0); pr2 =
          (Obj.magic wosub_le_inc x t s (Obj.magic c).pr2 x0) }); pr2 = c })
          (propproperty
            (total2_hProp
              (subtype_equal
                (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s))
                (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)))
              (fun _ -> hconj (wosub_le x s t) (wosub_le x t s))))
          (propproperty (hconj (wosub_le x s t) (wosub_le x t s))))))
    (wosub_univalence_map x s t) (fun _ -> Coq_paths_refl)

let coq_TRRGhomo_topath x _ g h _ =
  internal_paths_rew_r (transportf x x Coq_paths_refl g) g (fun p ->
    let _UU03c0_ = p.pr1 in
    let _UU03c3_ = p.pr2 in
    let q =
      funextfun (Obj.magic g).pr1 (Obj.magic h).pr1 (fun x0 ->
        Obj.magic funextfun ((Obj.magic g).pr1 x0) ((Obj.magic h).pr1 x0)
          (fun y ->
          Obj.magic hPropUnivalence (g.pr1 x0 y) (h.pr1 x0 y)
            (_UU03c0_ x0 y).pr1 (_UU03c0_ x0 y).pr2))
    in
    let x0 = fun x0 y -> (total2_paths_equiv x0 y).pr2 in
    let x1 = fun x1 y y0 -> (x0 x1 y y0).pr1 in
    let x2 = fun x2 y y0 -> (x1 x2 y y0).pr1 in
    Obj.magic x2 g h { pr1 = q; pr2 =
      (helper x g.pr1 h.pr1 g.pr2.pr1 h.pr2.pr1 g.pr2.pr2 h.pr2.pr2
        (Obj.magic q) _UU03c3_) }) (idpath_transportf x g)
let coq_Branch_to_subtype t x s =
  let h =
    hsubtype_to_preZFS_Branch_hsubtype t x
      (preZFS_Branch_hsubtype_tohsubtype t x s)
  in
  Obj.magic funextfunPreliminaryUAH (fun _ _ -> univalenceAxiom) h s
    (fun y ->
    let eS = fun x0 ->
      x0.pr1 (s y) (fun x1 ->
        let pr4 = (Obj.magic y).pr1 in
        let pr5 = (Obj.magic y).pr2 in
        let y0 = x1.pr1 in
        let z = x1.pr2 in
        let p =
          let p = coq_Ed t x pr4 in (Obj.magic propproperty p y0 pr5).pr1
        in
        internal_paths_rew y0 z pr5 p)
    in
    let sE = fun x0 -> { pr1 = (fun _ q ->
      q { pr1 = (Obj.magic y).pr2; pr2 = x0 }); pr2 = (Obj.magic y).pr2 }
    in
    Obj.magic hPropUnivalence (hconj ishinh (coq_Ed t x (Obj.magic y).pr1))
      (s y) eS sE)

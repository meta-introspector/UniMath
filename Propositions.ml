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

let hinhcoprod is =
  Obj.magic (fun p cP ->
    let cPX = fun x -> cP (Coq_ii1 x) in
    let cPY = fun y -> cP (Coq_ii2 y) in
    let is1P = Obj.magic is p in
    let f = sumofmaps (hinhuniv p cPX) (hinhuniv p cPY) in is1P f)

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

open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open UnivalenceAxiom

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type hSet = (coq_UU, __ isaset) total2

(** val make_hSet : 'a1 isaset -> hSet **)

let make_hSet i =
  { pr1 = __; pr2 = (Obj.magic i) }

type pr1hSet = __

(** val eqset : hSet -> pr1hSet -> pr1hSet -> hProp **)

let eqset x x0 x' =
  make_hProp (x.pr2 x0 x')

(** val neqset : hSet -> pr1hSet -> pr1hSet -> hProp **)

let neqset _ _ _ =
  make_hProp isapropneg

(** val setproperty : hSet -> __ isaset **)

let setproperty x =
  x.pr2

(** val setdirprod : hSet -> hSet -> hSet **)

let setdirprod x y =
  { pr1 = __; pr2 =
    (Obj.magic isofhleveldirprod (S (S O)) (setproperty x) (setproperty y)) }

(** val setcoprod : hSet -> hSet -> hSet **)

let setcoprod x y =
  { pr1 = __; pr2 = (Obj.magic isasetcoprod (setproperty x) (setproperty y)) }

(** val isaset_total2_hSet :
    hSet -> (pr1hSet -> hSet) -> (pr1hSet, pr1hSet) total2 isaset **)

let isaset_total2_hSet x y =
  isaset_total2 (setproperty x) (fun x0 -> setproperty (y x0))

(** val total2_hSet : hSet -> (pr1hSet -> hSet) -> hSet **)

let total2_hSet x y =
  make_hSet (isaset_total2_hSet x y)

(** val hfiber_hSet :
    hSet -> hSet -> (pr1hSet -> pr1hSet) -> pr1hSet -> hSet **)

let hfiber_hSet x y f y0 =
  make_hSet (isaset_hfiber f y0 x.pr2 y.pr2)

(** val isaset_forall_hSet : ('a1 -> hSet) -> ('a1 -> pr1hSet) isaset **)

let isaset_forall_hSet y =
  impred_isaset (fun x -> setproperty (y x))

(** val forall_hSet : ('a1 -> hSet) -> hSet **)

let forall_hSet y =
  make_hSet (isaset_forall_hSet y)

(** val unitset : hSet **)

let unitset =
  make_hSet isasetunit

(** val dirprod_hSet_subproof :
    hSet -> hSet -> (pr1hSet, pr1hSet) dirprod isaset **)

let dirprod_hSet_subproof x y =
  Obj.magic isofhleveldirprod (S (S O)) (setproperty x) (setproperty y)

(** val dirprod_hSet : hSet -> hSet -> hSet **)

let dirprod_hSet x y =
  { pr1 = __; pr2 = (Obj.magic dirprod_hSet_subproof x y) }

(** val hPropset : hSet **)

let hPropset =
  { pr1 = __; pr2 = (Obj.magic isasethProp) }

(** val hProp_to_hSet : hProp -> hSet **)

let hProp_to_hSet p =
  make_hSet (isasetaprop (propproperty p))

(** val boolset : hSet **)

let boolset =
  make_hSet isasetbool

(** val isaprop_isInjectiveFunction :
    hSet -> hSet -> (pr1hSet -> pr1hSet) -> (pr1hSet -> pr1hSet -> pr1hSet
    paths -> pr1hSet paths) isaprop **)

let isaprop_isInjectiveFunction x _ _ =
  impred (S O) (fun x0 ->
    impred (S O) (fun y -> impred (S O) (fun _ -> setproperty x x0 y)))

(** val isInjectiveFunction :
    hSet -> hSet -> (pr1hSet -> pr1hSet) -> hProp **)

let isInjectiveFunction x y f =
  { pr1 = __; pr2 = (isaprop_isInjectiveFunction x y f) }

type 'x ischoicebase_uu1 = __ -> ('x -> hProptoType) -> hProptoType

(** val isapropischoicebase : 'a1 ischoicebase_uu1 isaprop **)

let isapropischoicebase =
  impred (S O) (fun _ -> impred (S O) (fun _ -> ishinh.pr2))

(** val ischoicebase : hProp **)

let ischoicebase =
  make_hProp isapropischoicebase

(** val ischoicebaseweqf : ('a1, 'a2) weq -> hProptoType -> hProptoType **)

let ischoicebaseweqf w is =
  Obj.magic (fun _ fs ->
    hinhfun (pr1weq (invweq (weqonsecbase w)))
      (Obj.magic is __ (fun x -> fs (pr1weq w x))))

(** val ischoicebaseweqb : ('a1, 'a2) weq -> hProptoType -> hProptoType **)

let ischoicebaseweqb w is =
  ischoicebaseweqf (invweq w) is

(** val ischoicebaseunit : hProptoType **)

let ischoicebaseunit =
  Obj.magic (fun _ fs -> hinhfun tosecoverunit (fs Coq_tt))

(** val ischoicebasecontr : 'a1 iscontr -> hProptoType **)

let ischoicebasecontr is =
  ischoicebaseweqb (weqcontrtounit is) ischoicebaseunit

(** val ischoicebaseempty : hProptoType **)

let ischoicebaseempty =
  Obj.magic (fun _ _ -> hinhpr fromempty)

(** val ischoicebaseempty2 : 'a1 neg -> hProptoType **)

let ischoicebaseempty2 is =
  ischoicebaseweqb (weqtoempty is) ischoicebaseempty

(** val ischoicebasecoprod : hProptoType -> hProptoType -> hProptoType **)

let ischoicebasecoprod isx isy =
  Obj.magic (fun _ fs ->
    hinhfun (pr1weq (invweq weqsecovercoprodtoprod))
      (hinhand (Obj.magic isx __ (fun x -> fs (Coq_ii1 x)))
        (Obj.magic isy __ (fun y -> fs (Coq_ii2 y)))))

type 'x hsubtype = 'x -> hProp

(** val id_hsubtype : 'a1 hsubtype -> 'a1 -> hProp **)

let id_hsubtype x =
  x

type 'x carrier = ('x, hProptoType) total2

(** val make_carrier :
    'a1 hsubtype -> 'a1 -> hProptoType -> ('a1, hProptoType) total2 **)

let make_carrier _ x x0 =
  { pr1 = x; pr2 = x0 }

(** val pr1carrier : 'a1 hsubtype -> 'a1 carrier -> 'a1 **)

let pr1carrier _ t =
  t.pr1

(** val isaset_carrier_subset :
    hSet -> pr1hSet hsubtype -> (pr1hSet, hProptoType) total2 isaset **)

let isaset_carrier_subset x y =
  isaset_total2 (setproperty x) (fun x0 -> isasetaprop (propproperty (y x0)))

(** val carrier_subset : hSet -> pr1hSet hsubtype -> hSet **)

let carrier_subset x y =
  make_hSet (isaset_carrier_subset x y)

(** val isinclpr1carrier : 'a1 hsubtype -> ('a1 carrier, 'a1) isincl **)

let isinclpr1carrier a =
  isinclpr1 (fun x -> (a x).pr2)

(** val isasethsubtype : 'a1 hsubtype isaset **)

let isasethsubtype x =
  Obj.magic impred (S (S O)) (fun _ -> Obj.magic isasethProp) x

(** val totalsubtype : 'a1 hsubtype **)

let totalsubtype _ =
  htrue

(** val weqtotalsubtype : ('a1 carrier, 'a1) weq **)

let weqtotalsubtype =
  weqpr1 (fun _ -> Obj.magic iscontrunit)

(** val weq_subtypes :
    ('a1, 'a2) weq -> 'a1 hsubtype -> 'a2 hsubtype -> ('a1 -> (hProptoType,
    hProptoType) logeq) -> ('a1 carrier, 'a2 carrier) weq **)

let weq_subtypes w s t eq =
  weqbandf w (fun x ->
    weqiff (eq x) (propproperty (s x)) (propproperty (t (pr1weq w x))))

(** val subtypesdirprod :
    'a1 hsubtype -> 'a2 hsubtype -> ('a1, 'a2) dirprod hsubtype **)

let subtypesdirprod a b xy =
  hconj (a xy.pr1) (b xy.pr2)

(** val fromdsubtypesdirprodcarrier :
    'a1 hsubtype -> 'a2 hsubtype -> ('a1, 'a2) dirprod carrier -> ('a1
    carrier, 'a2 carrier) dirprod **)

let fromdsubtypesdirprodcarrier _ _ xyis =
  let xy = xyis.pr1 in
  let is = xyis.pr2 in
  let x = xy.pr1 in
  let y = xy.pr2 in
  make_dirprod { pr1 = x; pr2 = (Obj.magic is).pr1 } { pr1 = y; pr2 =
    (Obj.magic is).pr2 }

(** val tosubtypesdirprodcarrier :
    'a1 hsubtype -> 'a2 hsubtype -> ('a1 carrier, 'a2 carrier) dirprod ->
    ('a1, 'a2) dirprod carrier **)

let tosubtypesdirprodcarrier _ _ xisyis =
  let xis = xisyis.pr1 in
  let yis = xisyis.pr2 in
  let x = xis.pr1 in
  let isx = xis.pr2 in
  let y = yis.pr1 in
  let isy = yis.pr2 in
  { pr1 = (make_dirprod x y); pr2 = (Obj.magic make_dirprod isx isy) }

(** val weqsubtypesdirprod :
    'a1 hsubtype -> 'a2 hsubtype -> (('a1, 'a2) dirprod carrier, ('a1
    carrier, 'a2 carrier) dirprod) weq **)

let weqsubtypesdirprod a b =
  let f = fromdsubtypesdirprodcarrier a b in
  let g = tosubtypesdirprodcarrier a b in
  { pr1 = f; pr2 =
  (let egf = fun _ -> Coq_paths_refl in
   let efg = fun _ -> Coq_paths_refl in isweq_iso f g (Obj.magic egf) efg) }

(** val ishinhsubtypedirprod :
    'a1 hsubtype -> 'a2 hsubtype -> hProptoType -> hProptoType -> hProptoType **)

let ishinhsubtypedirprod a b isa isb =
  hinhfun (pr1weq (invweq (weqsubtypesdirprod a b))) (hinhand isa isb)

(** val isapropsubtype :
    'a1 hsubtype -> ('a1 -> 'a1 -> hProptoType -> hProptoType -> 'a1 paths)
    -> 'a1 carrier isaprop **)

let isapropsubtype a is =
  invproofirrelevance (fun x x' ->
    let x0 = isinclpr1 (fun x0 -> (a x0).pr2) in
    invmaponpathsincl (fun t -> t.pr1) x0 x x'
      (let x1 = x.pr1 in
       let is0 = x.pr2 in
       let x0' = x'.pr1 in let is0' = x'.pr2 in is x1 x0' is0 is0'))

(** val squash_pairs_to_set :
    'a1 isaset -> ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths) -> hProptoType ->
    'a1 **)

let squash_pairs_to_set is e =
  let iP =
    isapropsubtype (fun _ -> ishinh) (fun y y' f f' ->
      squash_to_prop f (is y y') (fun f0 ->
        squash_to_prop f' (is y y') (fun f'0 -> e y y' f0 f'0)))
  in
  (fun w ->
  let p =
    squash_to_prop w iP (fun w0 -> { pr1 = w0.pr1; pr2 = (hinhpr w0.pr2) })
  in
  p.pr1)

(** val squash_to_set :
    'a2 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a1 -> 'a2 paths) -> hProptoType ->
    'a2 **)

let squash_to_set is f e w =
  let j =
    isapropsubtype (fun _ -> ishinh) (fun y y' j j' ->
      squash_to_prop j (is y y') (fun x0 ->
        let j0 = x0.pr1 in
        let k = x0.pr2 in
        squash_to_prop j' (is y y') (fun x1 ->
          let j'0 = x1.pr1 in
          let k' = x1.pr2 in
          pathscomp0 y (f j0) y' (pathsinv0 (f j0) y k)
            (pathscomp0 (f j0) (f j'0) y' (e j0 j'0) k'))))
  in
  let p =
    squash_to_prop w j (fun x0 -> { pr1 = (f x0); pr2 =
      (hinhpr { pr1 = x0; pr2 = Coq_paths_refl }) })
  in
  p.pr1

type 'x hrel = 'x -> 'x -> hProp

(** val idhrel : 'a1 hrel -> 'a1 -> 'a1 -> hProp **)

let idhrel x =
  x

type 'x brel = 'x -> 'x -> bool

(** val idbrel : 'a1 brel -> 'a1 -> 'a1 -> bool **)

let idbrel x =
  x

type 'x istrans = 'x -> 'x -> 'x -> hProptoType -> hProptoType -> hProptoType

type 'x isrefl = 'x -> hProptoType

type 'x issymm = 'x -> 'x -> hProptoType -> hProptoType

type 'x ispreorder = ('x istrans, 'x isrefl) dirprod

type 'x iseqrel = ('x ispreorder, 'x issymm) dirprod

(** val iseqrelconstr :
    'a1 hrel -> 'a1 istrans -> 'a1 isrefl -> 'a1 issymm -> 'a1 iseqrel **)

let iseqrelconstr _ trans0 refl0 symm0 =
  make_dirprod (make_dirprod trans0 refl0) symm0

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

(** val isaprop_istrans : hSet -> pr1hSet hrel -> pr1hSet istrans isaprop **)

let isaprop_istrans _ r =
  impred (S O) (fun t ->
    impred (S O) (fun _ ->
      impred (S O) (fun t1 ->
        impred (S O) (fun _ -> impred (S O) (fun _ -> propproperty (r t t1))))))

(** val isaprop_isrefl : hSet -> pr1hSet hrel -> pr1hSet isrefl isaprop **)

let isaprop_isrefl _ r =
  impred (S O) (fun t -> propproperty (r t t))

(** val isaprop_istotal : hSet -> pr1hSet hrel -> pr1hSet istotal isaprop **)

let isaprop_istotal _ _ =
  impred (S O) (fun _ -> impred (S O) (fun _ -> propproperty hdisj))

(** val isaprop_isantisymm :
    hSet -> pr1hSet hrel -> pr1hSet isantisymm isaprop **)

let isaprop_isantisymm x _ =
  impred (S O) (fun x0 ->
    impred (S O) (fun y ->
      impred (S O) (fun _ -> impred (S O) (fun _ -> setproperty x x0 y))))

(** val isaprop_ispreorder :
    hSet -> pr1hSet hrel -> pr1hSet ispreorder isaprop **)

let isaprop_ispreorder x r =
  isapropdirprod (isaprop_istrans x r) (isaprop_isrefl x r)

(** val isaprop_isPartialOrder :
    hSet -> pr1hSet hrel -> pr1hSet isPartialOrder isaprop **)

let isaprop_isPartialOrder x r =
  isapropdirprod (isaprop_ispreorder x r) (isaprop_isantisymm x r)

(** val isaset_hrel : hSet -> pr1hSet hrel isaset **)

let isaset_hrel _ =
  impred_isaset (fun _ -> impred_isaset (fun _ -> isasethProp))

(** val istransandirrefltoasymm :
    'a1 hrel -> 'a1 istrans -> 'a1 isirrefl -> 'a1 isasymm **)

let istransandirrefltoasymm _ is1 is2 a b rab rba =
  is2 a (is1 a b a rab rba)

(** val istotaltoiscoasymm : 'a1 hrel -> 'a1 istotal -> 'a1 iscoasymm **)

let istotaltoiscoasymm r is x1 x2 =
  Obj.magic hdisjtoimpl (r x2 x1) (is x1 x2)

(** val isdecreltoisnegrel : 'a1 hrel -> 'a1 isdecrel -> 'a1 isnegrel **)

let isdecreltoisnegrel _ is x1 x2 =
  let c = is x1 x2 in
  (fun _ ->
  match c with
  | Coq_ii1 a -> a
  | Coq_ii2 _ -> assert false (* absurd case *))

(** val isantisymmnegtoiscoantisymm :
    'a1 hrel -> 'a1 isdecrel -> 'a1 isantisymmneg -> 'a1 iscoantisymm **)

let isantisymmnegtoiscoantisymm _ isdr isr x1 x2 nrx12 =
  let c = isdr x2 x1 in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 (isr x1 x2 nrx12 b))

(** val rtoneq :
    'a1 hrel -> 'a1 isirrefl -> 'a1 -> 'a1 -> hProptoType -> 'a1 paths neg **)

let rtoneq _ is a b r e =
  let r0 = internal_paths_rew a r b e in is b r0

type 'x hrellogeq = 'x -> 'x -> (hProptoType, hProptoType) logeq

(** val istranslogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 istrans -> 'a1 istrans **)

let istranslogeqf _ _ lg isl x1 x2 x3 r12 r23 =
  (lg x1 x3).pr1 (isl x1 x2 x3 ((lg x1 x2).pr2 r12) ((lg x2 x3).pr2 r23))

(** val isrefllogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 isrefl -> 'a1 isrefl **)

let isrefllogeqf _ _ lg isl x =
  (lg x x).pr1 (isl x)

(** val issymmlogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 issymm -> 'a1 issymm **)

let issymmlogeqf _ _ lg isl x1 x2 r12 =
  (lg x2 x1).pr1 (isl x1 x2 ((lg x1 x2).pr2 r12))

(** val ispologeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 ispreorder -> 'a1 ispreorder **)

let ispologeqf l r lg isl =
  make_dirprod (istranslogeqf l r lg isl.pr1) (isrefllogeqf l r lg isl.pr2)

(** val iseqrellogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 iseqrel -> 'a1 iseqrel **)

let iseqrellogeqf l r lg isl =
  make_dirprod (ispologeqf l r lg isl.pr1) (issymmlogeqf l r lg isl.pr2)

(** val isirrefllogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 isirrefl -> 'a1 isirrefl **)

let isirrefllogeqf _ _ lg isl x r =
  isl x ((lg x x).pr2 r)

(** val isasymmlogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 isasymm -> 'a1 isasymm **)

let isasymmlogeqf _ _ lg isl x1 x2 r12 r21 =
  isl x1 x2 ((lg x1 x2).pr2 r12) ((lg x2 x1).pr2 r21)

(** val iscoasymmlogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 iscoasymm -> 'a1 iscoasymm **)

let iscoasymmlogeqf _ _ lg isl x1 x2 r12 =
  (lg x2 x1).pr1 (isl x1 x2 (negf (lg x1 x2).pr1 r12))

(** val istotallogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 istotal -> 'a1 istotal **)

let istotallogeqf _ _ lg isl x1 x2 =
  let int = isl x1 x2 in hinhfun (coprodf (lg x1 x2).pr1 (lg x2 x1).pr1) int

(** val iscotranslogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 iscotrans -> 'a1 iscotrans **)

let iscotranslogeqf _ _ lg isl x1 x2 x3 r13 =
  let int = isl x1 x2 x3 ((lg x1 x3).pr2 r13) in
  hinhfun (coprodf (lg x1 x2).pr1 (lg x2 x3).pr1) int

(** val isdecrellogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 isdecrel -> 'a1 isdecrel **)

let isdecrellogeqf _ _ lg isl x1 x2 =
  let c = isl x1 x2 in
  (match c with
   | Coq_ii1 a -> Coq_ii1 ((lg x1 x2).pr1 a)
   | Coq_ii2 b -> Coq_ii2 (negf (lg x1 x2).pr2 b))

(** val isnegrellogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 isnegrel -> 'a1 isnegrel **)

let isnegrellogeqf _ _ lg isl x1 x2 nnr =
  (lg x1 x2).pr1 (isl x1 x2 (negf (negf (lg x1 x2).pr2) nnr))

(** val isantisymmlogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 isantisymm -> 'a1 isantisymm **)

let isantisymmlogeqf _ _ lg isl x1 x2 r12 r21 =
  isl x1 x2 ((lg x1 x2).pr2 r12) ((lg x2 x1).pr2 r21)

(** val isantisymmneglogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 isantisymmneg -> 'a1 isantisymmneg **)

let isantisymmneglogeqf _ _ lg isl x1 x2 nr12 nr21 =
  isl x1 x2 (negf (lg x1 x2).pr1 nr12) (negf (lg x2 x1).pr1 nr21)

(** val iscoantisymmlogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 iscoantisymm -> 'a1 iscoantisymm **)

let iscoantisymmlogeqf _ _ lg isl x1 x2 r12 =
  let int = isl x1 x2 (negf (lg x1 x2).pr1 r12) in
  coprodf (lg x2 x1).pr1 idfun int

(** val neqchoicelogeqf :
    'a1 hrel -> 'a1 hrel -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq)
    -> 'a1 neqchoice -> 'a1 neqchoice **)

let neqchoicelogeqf _ _ lg isl x1 x2 ne =
  coprodf (lg x1 x2).pr1 (lg x2 x1).pr1 (isl x1 x2 ne)

type 'x po = ('x hrel, 'x ispreorder) total2

(** val make_po : 'a1 hrel -> 'a1 ispreorder -> 'a1 po **)

let make_po r is =
  { pr1 = r; pr2 = is }

(** val carrierofpo : 'a1 po -> 'a1 -> 'a1 -> hProp **)

let carrierofpo x =
  x.pr1

type coq_PreorderedSet = (hSet, pr1hSet po) total2

(** val coq_PreorderedSetPair : hSet -> pr1hSet po -> coq_PreorderedSet **)

let coq_PreorderedSetPair x r =
  { pr1 = x; pr2 = r }

(** val carrierofPreorderedSet : coq_PreorderedSet -> hSet **)

let carrierofPreorderedSet t =
  t.pr1

(** val coq_PreorderedSetRelation : coq_PreorderedSet -> pr1hSet hrel **)

let coq_PreorderedSetRelation x =
  x.pr2.pr1

type coq_PartialOrder = (pr1hSet hrel, pr1hSet isPartialOrder) total2

(** val make_PartialOrder :
    hSet -> pr1hSet hrel -> pr1hSet isPartialOrder -> coq_PartialOrder **)

let make_PartialOrder _ r is =
  { pr1 = r; pr2 = is }

(** val carrierofPartialOrder : hSet -> coq_PartialOrder -> pr1hSet hrel **)

let carrierofPartialOrder _ t =
  t.pr1

type coq_Poset = (hSet, coq_PartialOrder) total2

(** val make_Poset : hSet -> coq_PartialOrder -> coq_Poset **)

let make_Poset x r =
  { pr1 = x; pr2 = r }

(** val carrierofposet : coq_Poset -> hSet **)

let carrierofposet t =
  t.pr1

(** val posetRelation : coq_Poset -> pr1hSet hrel **)

let posetRelation x =
  x.pr2.pr1

(** val isrefl_posetRelation : coq_Poset -> pr1hSet isrefl **)

let isrefl_posetRelation x x0 =
  x.pr2.pr2.pr1.pr2 x0

(** val istrans_posetRelation : coq_Poset -> pr1hSet istrans **)

let istrans_posetRelation x x0 y z l m =
  x.pr2.pr2.pr1.pr1 x0 y z l m

(** val isantisymm_posetRelation : coq_Poset -> pr1hSet isantisymm **)

let isantisymm_posetRelation x x0 y l m =
  x.pr2.pr2.pr2 x0 y l m

type isaposetmorphism = pr1hSet -> pr1hSet -> hProptoType -> hProptoType

type posetmorphism = (pr1hSet -> pr1hSet, isaposetmorphism) total2

(** val make_posetmorphism :
    coq_Poset -> coq_Poset -> (pr1hSet -> pr1hSet) -> isaposetmorphism ->
    (pr1hSet -> pr1hSet, isaposetmorphism) total2 **)

let make_posetmorphism _ _ x x0 =
  { pr1 = x; pr2 = x0 }

(** val carrierofposetmorphism :
    coq_Poset -> coq_Poset -> posetmorphism -> pr1hSet -> pr1hSet **)

let carrierofposetmorphism _ _ t =
  t.pr1

type isdec_ordering = pr1hSet -> pr1hSet -> hProptoType decidable

(** val isaprop_isaposetmorphism :
    coq_Poset -> coq_Poset -> (pr1hSet -> pr1hSet) -> isaposetmorphism isaprop **)

let isaprop_isaposetmorphism _ y f =
  impredtwice (S O) (fun t t' ->
    impred_prop (fun _ -> posetRelation y (f t) (f t')))

(** val isaset_po : hSet -> pr1hSet po isaset **)

let isaset_po x =
  Obj.magic isofhleveltotal2 (S (S O)) (isaset_hrel x) (fun x0 ->
    hlevelntosn (S O) (isaprop_ispreorder x x0))

(** val isaset_PartialOrder : hSet -> coq_PartialOrder isaset **)

let isaset_PartialOrder x =
  Obj.magic isofhleveltotal2 (S (S O)) (isaset_hrel x) (fun x0 ->
    hlevelntosn (S O) (isaprop_isPartialOrder x x0))

type isPosetEquivalence = (isaposetmorphism, isaposetmorphism) dirprod

(** val isaprop_isPosetEquivalence :
    coq_Poset -> coq_Poset -> (pr1hSet, pr1hSet) weq -> isPosetEquivalence
    isaprop **)

let isaprop_isPosetEquivalence x y f =
  isapropdirprod (isaprop_isaposetmorphism x y (pr1weq f))
    (isaprop_isaposetmorphism y x (invmap f))

(** val isPosetEquivalence_idweq : coq_Poset -> isPosetEquivalence **)

let isPosetEquivalence_idweq _ =
  { pr1 = (fun _ _ le -> le); pr2 = (fun _ _ le -> le) }

type coq_PosetEquivalence =
  ((pr1hSet, pr1hSet) weq, isPosetEquivalence) total2

(** val posetUnderlyingEquivalence :
    coq_Poset -> coq_Poset -> coq_PosetEquivalence -> (pr1hSet, pr1hSet) weq **)

let posetUnderlyingEquivalence _ _ t =
  t.pr1

(** val identityPosetEquivalence : coq_Poset -> coq_PosetEquivalence **)

let identityPosetEquivalence x =
  { pr1 = idweq; pr2 = (isPosetEquivalence_idweq x) }

(** val isincl_pr1_PosetEquivalence :
    coq_Poset -> coq_Poset -> (coq_PosetEquivalence, (pr1hSet, pr1hSet) weq)
    isincl **)

let isincl_pr1_PosetEquivalence x y =
  isinclpr1 (isaprop_isPosetEquivalence x y)

(** val isinj_pr1_PosetEquivalence :
    coq_Poset -> coq_Poset -> (coq_PosetEquivalence, (pr1hSet, pr1hSet) weq)
    isInjective **)

let isinj_pr1_PosetEquivalence x y f g =
  isweqonpathsincl (fun t -> t.pr1) (isincl_pr1_PosetEquivalence x y) f g

type isMinimal = pr1hSet -> hProptoType

type isMaximal = pr1hSet -> hProptoType

type consecutive =
  ((hProptoType, pr1hSet paths neg) dirprod, pr1hSet -> ((hProptoType,
  pr1hSet paths neg) dirprod, (hProptoType, pr1hSet paths neg) dirprod)
  dirprod neg) dirprod

(** val isaprop_isMinimal : coq_Poset -> pr1hSet -> isMaximal isaprop **)

let isaprop_isMinimal x x0 =
  impred_prop (fun t -> posetRelation x t x0)

(** val isaprop_isMaximal : coq_Poset -> pr1hSet -> isMaximal isaprop **)

let isaprop_isMaximal x x0 =
  impred_prop (fun t -> posetRelation x t x0)

(** val isaprop_consecutive :
    coq_Poset -> pr1hSet -> pr1hSet -> consecutive isaprop **)

let isaprop_consecutive x x0 y =
  isapropdirprod (isapropdirprod (posetRelation x x0 y).pr2 isapropneg)
    (impred (S O) (fun _ -> isapropneg))

type 'x eqrel = ('x hrel, 'x iseqrel) total2

(** val make_eqrel : 'a1 hrel -> 'a1 iseqrel -> 'a1 eqrel **)

let make_eqrel r is =
  { pr1 = r; pr2 = is }

(** val eqrelconstr :
    'a1 hrel -> 'a1 istrans -> 'a1 isrefl -> 'a1 issymm -> 'a1 eqrel **)

let eqrelconstr r is1 is2 is3 =
  make_eqrel r (make_dirprod (make_dirprod is1 is2) is3)

(** val pr1eqrel : 'a1 eqrel -> 'a1 -> 'a1 -> hProp **)

let pr1eqrel x =
  x.pr1

(** val eqreltrans : 'a1 eqrel -> 'a1 istrans **)

let eqreltrans r =
  r.pr2.pr1.pr1

(** val eqrelrefl : 'a1 eqrel -> 'a1 isrefl **)

let eqrelrefl r =
  r.pr2.pr1.pr2

(** val eqrelsymm : 'a1 eqrel -> 'a1 issymm **)

let eqrelsymm r =
  r.pr2.pr2

(** val hreldirprod : 'a1 hrel -> 'a2 hrel -> ('a1, 'a2) dirprod hrel **)

let hreldirprod rX rY xy xy' =
  hconj (rX xy.pr1 xy'.pr1) (rY xy.pr2 xy'.pr2)

(** val istransdirprod :
    'a1 hrel -> 'a2 hrel -> 'a1 istrans -> 'a2 istrans -> ('a1, 'a2) dirprod
    istrans **)

let istransdirprod _ _ isx isy xy1 xy2 xy3 is12 is23 =
  Obj.magic make_dirprod
    (isx xy1.pr1 xy2.pr1 xy3.pr1 (Obj.magic is12).pr1 (Obj.magic is23).pr1)
    (isy xy1.pr2 xy2.pr2 xy3.pr2 (Obj.magic is12).pr2 (Obj.magic is23).pr2)

(** val isrefldirprod :
    'a1 hrel -> 'a2 hrel -> 'a1 isrefl -> 'a2 isrefl -> ('a1, 'a2) dirprod
    isrefl **)

let isrefldirprod _ _ isx isy xy =
  Obj.magic make_dirprod (isx xy.pr1) (isy xy.pr2)

(** val issymmdirprod :
    'a1 hrel -> 'a2 hrel -> 'a1 issymm -> 'a2 issymm -> ('a1, 'a2) dirprod
    issymm **)

let issymmdirprod _ _ isx isy xy1 xy2 is12 =
  Obj.magic make_dirprod (isx xy1.pr1 xy2.pr1 (Obj.magic is12).pr1)
    (isy xy1.pr2 xy2.pr2 (Obj.magic is12).pr2)

(** val eqreldirprod : 'a1 eqrel -> 'a2 eqrel -> ('a1, 'a2) dirprod eqrel **)

let eqreldirprod rX rY =
  eqrelconstr (hreldirprod (pr1eqrel rX) (pr1eqrel rY))
    (istransdirprod (pr1eqrel rX) (pr1eqrel rY) (eqreltrans rX)
      (eqreltrans rY))
    (isrefldirprod (pr1eqrel rX) (pr1eqrel rY) (eqrelrefl rX) (eqrelrefl rY))
    (issymmdirprod (pr1eqrel rX) (pr1eqrel rY) (eqrelsymm rX) (eqrelsymm rY))

(** val negrel : 'a1 hrel -> 'a1 hrel **)

let negrel _ _ _ =
  make_hProp isapropneg

(** val istransnegrel : 'a1 hrel -> 'a1 iscotrans -> 'a1 istrans **)

let istransnegrel _ isr x1 x2 x3 r12 r23 =
  Obj.magic negf (isr x1 x2 x3) (toneghdisj (make_dirprod r12 r23))

(** val isasymmnegrel : 'a1 hrel -> 'a1 iscoasymm -> 'a1 isasymm **)

let isasymmnegrel _ isr x1 x2 r12 r21 =
  Obj.magic r21 (Obj.magic isr x1 x2 r12)

(** val iscoasymmgenrel : 'a1 hrel -> 'a1 isasymm -> 'a1 iscoasymm **)

let iscoasymmgenrel _ isr x1 x2 nr12 =
  Obj.magic negf (Obj.magic isr x2 x1) nr12

(** val isdecnegrel : 'a1 hrel -> 'a1 isdecrel -> 'a1 isdecrel **)

let isdecnegrel _ isr x1 x2 =
  let c = isr x1 x2 in
  (match c with
   | Coq_ii1 a -> Coq_ii2 (Obj.magic todneg a)
   | Coq_ii2 b -> Coq_ii1 (Obj.magic b))

(** val isnegnegrel : 'a1 hrel -> 'a1 isnegrel **)

let isnegnegrel _ _ _ =
  Obj.magic negf todneg

(** val isantisymmnegrel : 'a1 hrel -> 'a1 isantisymmneg -> 'a1 isantisymm **)

let isantisymmnegrel _ isr =
  Obj.magic isr

(** val eqh : 'a1 isdeceq -> 'a1 hrel **)

let eqh is x x' =
  make_hProp (isasetbool (booleq is x x') Coq_true)

(** val neqh : 'a1 isdeceq -> 'a1 hrel **)

let neqh is x x' =
  make_hProp (isasetbool (booleq is x x') Coq_false)

(** val isrefleqh : 'a1 isdeceq -> 'a1 isrefl **)

let isrefleqh is x =
  let d = is x x in
  (match d with
   | Coq_ii1 _ -> Obj.magic Coq_paths_refl
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val weqeqh : 'a1 isdeceq -> 'a1 -> 'a1 -> ('a1 paths, hProptoType) weq **)

let weqeqh is x x' =
  weqimplimpl (fun _ -> isrefleqh is x) (fun _ ->
    let d = is x x' in
    (match d with
     | Coq_ii1 a -> a
     | Coq_ii2 _ -> assert false (* absurd case *))) (isasetifdeceq is x x')
    (isasetbool (booleq is x x') Coq_true)

(** val weqneqh :
    'a1 isdeceq -> 'a1 -> 'a1 -> ('a1 paths neg, hProptoType) weq **)

let weqneqh is x x' =
  weqimplimpl
    (let d = is x x' in
     fun _ ->
     match d with
     | Coq_ii1 _ -> assert false (* absurd case *)
     | Coq_ii2 _ -> Obj.magic Coq_paths_refl)
    (let d = is x x' in
     fun _ ->
     match d with
     | Coq_ii1 _ -> assert false (* absurd case *)
     | Coq_ii2 b -> b) isapropneg
    (isasetbool
      (match is x x' with
       | Coq_ii1 _ -> Coq_true
       | Coq_ii2 _ -> Coq_false) Coq_false)

type 'x decrel = ('x hrel, 'x isdecrel) total2

(** val pr1decrel : 'a1 decrel -> 'a1 hrel **)

let pr1decrel x =
  x.pr1

(** val make_decrel : 'a1 hrel -> 'a1 isdecrel -> 'a1 decrel **)

let make_decrel r is =
  { pr1 = r; pr2 = is }

(** val decreltobrel : 'a1 decrel -> 'a1 brel **)

let decreltobrel r x x' =
  let c = r.pr2 x x' in
  (match c with
   | Coq_ii1 _ -> Coq_true
   | Coq_ii2 _ -> Coq_false)

(** val breltodecrel : 'a1 brel -> 'a1 decrel **)

let breltodecrel b =
  make_decrel (fun x x' -> make_hProp (isasetbool (b x x') Coq_true))
    (fun x x' -> Obj.magic isdeceqbool (b x x') Coq_true)

(** val pathstor : 'a1 decrel -> 'a1 -> 'a1 -> bool paths -> hProptoType **)

let pathstor r x x' _ =
  let c = r.pr2 x x' in
  (match c with
   | Coq_ii1 a -> a
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val rtopaths : 'a1 decrel -> 'a1 -> 'a1 -> hProptoType -> bool paths **)

let rtopaths r x x' _ =
  let c = r.pr2 x x' in
  (match c with
   | Coq_ii1 _ -> Coq_paths_refl
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val pathstonegr :
    'a1 decrel -> 'a1 -> 'a1 -> bool paths -> hProptoType neg **)

let pathstonegr r x x' _ =
  let c = r.pr2 x x' in
  (match c with
   | Coq_ii1 _ -> assert false (* absurd case *)
   | Coq_ii2 b -> b)

(** val negrtopaths :
    'a1 decrel -> 'a1 -> 'a1 -> hProptoType neg -> bool paths **)

let negrtopaths r x x' _ =
  let c = r.pr2 x x' in
  (match c with
   | Coq_ii1 _ -> assert false (* absurd case *)
   | Coq_ii2 _ -> Coq_paths_refl)

(** val ctlong :
    'a1 hrel -> 'a1 isdecrel -> 'a1 -> 'a1 -> bool paths -> hProptoType **)

let ctlong _ is x x' _ =
  let c = is x x' in
  (match c with
   | Coq_ii1 a -> a
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val deceq_to_decrel : 'a1 isdeceq -> 'a1 decrel **)

let deceq_to_decrel i =
  make_decrel (fun x y -> { pr1 = __; pr2 = (isasetifdeceq i x y) })
    (Obj.magic i)

(** val confirm_equal :
    'a1 isdeceq -> 'a1 -> 'a1 -> bool paths -> 'a1 paths **)

let confirm_equal i x x' e =
  Obj.magic pathstor (deceq_to_decrel i) x x' e

(** val confirm_not_equal :
    'a1 isdeceq -> 'a1 -> 'a1 -> bool paths -> 'a1 paths neg **)

let confirm_not_equal i x x' e =
  Obj.magic pathstonegr (deceq_to_decrel i) x x' e

(** val resrel : 'a1 hrel -> 'a1 hsubtype -> 'a1 carrier hrel **)

let resrel l _ p1 p2 =
  l p1.pr1 p2.pr1

(** val istransresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 istrans -> 'a1 carrier istrans **)

let istransresrel _ _ isl x1 x2 x3 r12 r23 =
  isl x1.pr1 x2.pr1 x3.pr1 r12 r23

(** val isreflresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 isrefl -> 'a1 carrier isrefl **)

let isreflresrel _ _ isl x =
  isl x.pr1

(** val issymmresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 issymm -> 'a1 carrier issymm **)

let issymmresrel _ _ isl x1 x2 r12 =
  isl x1.pr1 x2.pr1 r12

(** val isporesrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 ispreorder -> 'a1 carrier ispreorder **)

let isporesrel l p isl =
  make_dirprod (istransresrel l p isl.pr1) (isreflresrel l p isl.pr2)

(** val iseqrelresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 iseqrel -> 'a1 carrier iseqrel **)

let iseqrelresrel l p isl =
  make_dirprod (isporesrel l p isl.pr1) (issymmresrel l p isl.pr2)

(** val isirreflresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 isirrefl -> 'a1 carrier isirrefl **)

let isirreflresrel _ _ isl x r =
  isl x.pr1 r

(** val isasymmresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 isasymm -> 'a1 carrier isasymm **)

let isasymmresrel _ _ isl x1 x2 r12 r21 =
  isl x1.pr1 x2.pr1 r12 r21

(** val iscoasymmresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 iscoasymm -> 'a1 carrier iscoasymm **)

let iscoasymmresrel _ _ isl x1 x2 r12 =
  isl x1.pr1 x2.pr1 r12

(** val istotalresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 istotal -> 'a1 carrier istotal **)

let istotalresrel _ _ isl x1 x2 =
  isl x1.pr1 x2.pr1

(** val iscotransresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 iscotrans -> 'a1 carrier iscotrans **)

let iscotransresrel _ _ isl x1 x2 x3 r13 =
  isl x1.pr1 x2.pr1 x3.pr1 r13

(** val isdecrelresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 isdecrel -> 'a1 carrier isdecrel **)

let isdecrelresrel _ _ isl x1 x2 =
  isl x1.pr1 x2.pr1

(** val isnegrelresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 isnegrel -> 'a1 carrier isnegrel **)

let isnegrelresrel _ _ isl x1 x2 nnr =
  isl x1.pr1 x2.pr1 nnr

(** val isantisymmresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 isantisymm -> 'a1 carrier isantisymm **)

let isantisymmresrel _ p isl x1 x2 r12 r21 =
  invmaponpathsincl (pr1carrier p) (isinclpr1carrier p) x1 x2
    (isl x1.pr1 x2.pr1 r12 r21)

(** val isantisymmnegresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 isantisymmneg -> 'a1 carrier isantisymmneg **)

let isantisymmnegresrel _ p isl x1 x2 nr12 nr21 =
  invmaponpathsincl (pr1carrier p) (isinclpr1carrier p) x1 x2
    (isl x1.pr1 x2.pr1 nr12 nr21)

(** val iscoantisymmresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 iscoantisymm -> 'a1 carrier iscoantisymm **)

let iscoantisymmresrel _ p isl x1 x2 r12 =
  let c = isl x1.pr1 x2.pr1 r12 in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b ->
     Coq_ii2 (invmaponpathsincl (pr1carrier p) (isinclpr1carrier p) x1 x2 b))

(** val neqchoiceresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 neqchoice -> 'a1 carrier neqchoice **)

let neqchoiceresrel _ p isl x1 x2 ne =
  let int =
    negf (invmaponpathsincl (pr1carrier p) (isinclpr1carrier p) x1 x2) ne
  in
  isl (pr1carrier p x1) (pr1carrier p x2) int

type 'x iseqclass =
  (hProptoType, ('x -> 'x -> hProptoType -> hProptoType -> hProptoType, 'x ->
  'x -> hProptoType -> hProptoType -> hProptoType) dirprod) dirprod

(** val iseqclassconstr :
    'a1 hrel -> 'a1 hsubtype -> hProptoType -> ('a1 -> 'a1 -> hProptoType ->
    hProptoType -> hProptoType) -> ('a1 -> 'a1 -> hProptoType -> hProptoType
    -> hProptoType) -> 'a1 iseqclass **)

let iseqclassconstr _ _ ax0 ax1 ax2 =
  make_dirprod ax0 (make_dirprod ax1 ax2)

(** val eqax0 : 'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> hProptoType **)

let eqax0 _ _ is =
  is.pr1

(** val eqax1 :
    'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> 'a1 -> 'a1 -> hProptoType ->
    hProptoType -> hProptoType **)

let eqax1 _ _ is =
  is.pr2.pr1

(** val eqax2 :
    'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> 'a1 -> 'a1 -> hProptoType ->
    hProptoType -> hProptoType **)

let eqax2 _ _ is =
  is.pr2.pr2

(** val isapropiseqclass :
    'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass isaprop **)

let isapropiseqclass r a =
  isofhleveldirprod (S O) isapropishinh
    (isofhleveldirprod (S O)
      (impred (S O) (fun _ ->
        impred (S O) (fun t0 ->
          impred (S O) (fun _ -> impred (S O) (fun _ -> (a t0).pr2)))))
      (impred (S O) (fun t ->
        impred (S O) (fun t0 ->
          impred (S O) (fun _ -> impred (S O) (fun _ -> (r t t0).pr2))))))

(** val iseqclassdirprod :
    'a1 hrel -> 'a2 hrel -> 'a1 hsubtype -> 'a2 hsubtype -> 'a1 iseqclass ->
    'a2 iseqclass -> ('a1, 'a2) dirprod iseqclass **)

let iseqclassdirprod r q a b isa isb =
  let rQ = hreldirprod r q in
  let ax0 = ishinhsubtypedirprod a b (eqax0 r a isa) (eqax0 q b isb) in
  let ax1 = fun xy1 xy2 rq ab1 ->
    make_dirprod (eqax1 r a isa xy1.pr1 xy2.pr1 rq.pr1 ab1.pr1)
      (eqax1 q b isb xy1.pr2 xy2.pr2 rq.pr2 ab1.pr2)
  in
  let ax2 = fun xy1 xy2 ab1 ab2 ->
    make_dirprod (eqax2 r a isa xy1.pr1 xy2.pr1 ab1.pr1 ab2.pr1)
      (eqax2 q b isb xy1.pr2 xy2.pr2 ab1.pr2 ab2.pr2)
  in
  iseqclassconstr rQ (subtypesdirprod a b) ax0 (Obj.magic ax1) (Obj.magic ax2)

(** val surjectionisepitosets :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) issurjective
    -> 'a3 isaset -> ('a1 -> 'a3 paths) -> 'a2 -> 'a3 paths **)

let surjectionisepitosets _ g1 g2 is1 is2 isf y =
  let s1 = fun x1 -> let t = x1.pr1 in isf t in
  let s2 = hinhfun s1 (is1 y) in
  let is3 = is2 (g1 y) (g2 y) in
  Obj.magic hinhuniv (make_hProp is3) (fun x1 -> x1) s2

(** val isaset_set_fun_space : hSet -> ('a1 -> pr1hSet) isaset **)

let isaset_set_fun_space b =
  Obj.magic impred (S (S O)) (fun _ -> (Obj.magic b).pr2)

(** val epiissurjectiontosets :
    ('a1 -> 'a2) -> 'a2 isaset -> (hSet -> ('a2 -> pr1hSet) -> ('a2 ->
    pr1hSet) -> ('a1 -> pr1hSet paths) -> 'a2 -> pr1hSet paths) -> ('a1, 'a2)
    issurjective **)

let epiissurjectiontosets p isB epip =
  let pred_set = isaset_set_fun_space (make_hSet isasethProp) in
  let epip0 =
    Obj.magic epip (make_hSet pred_set) (fun _ _ -> ishinh) (fun b x ->
      make_hProp (isB x b))
  in
  let h =
    epip0 (fun b ->
      funextfun (fun _ -> Obj.magic ishinh) (fun x ->
        Obj.magic make_hProp (Obj.magic isB x (p b))) (fun x ->
        Obj.magic weqtopathshProp ishinh (make_hProp (Obj.magic isB x (p b)))
          (logeqweq ishinh (make_hProp (Obj.magic isB x (p b)))
            (hinhuniv (make_hProp (Obj.magic isB x (p b))) (fun x0 ->
              let y = x0.pr1 in
              let eqx = x0.pr2 in
              internal_paths_rew_r (Obj.magic x) (p y.pr1)
                (Obj.magic hfiberpr2 p (p b) y) eqx)) (fun eqx ->
            hinhpr { pr1 = { pr1 = b; pr2 = Coq_paths_refl }; pr2 = eqx }))))
  in
  (fun y ->
  let h0 = h y in
  let h1 = toforallpaths (fun _ -> ishinh) (fun x -> make_hProp (isB x y)) h0
  in
  let h2 = h1 y in
  let typ = make_hProp (isB y y) in
  let witness = Coq_paths_refl in
  internal_paths_rew ishinh (Obj.magic hinhfun (fun h' -> h'.pr1)) typ h2
    witness)

(** val surjective_iscontr_im :
    'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
    'a3 paths) -> ('a1, 'a2) issurjective -> 'a2 -> (('a1, 'a2) hfiber, 'a3)
    image iscontr **)

let surjective_iscontr_im hsc p f comp_f_epi surjectivep b =
  squash_to_prop (surjectivep b) isapropiscontr (fun h ->
    iscontraprop1
      (isapropsubtype (fun _ -> ishinh) (fun x1 x2 ->
        Obj.magic hinhuniv2 (make_hProp (hsc x1 x2)) (fun y1 y2 ->
          let pr3 = y1.pr1 in
          let z1 = pr3.pr1 in
          let h1 = pr3.pr2 in
          let h1' = y1.pr2 in
          let pr4 = y2.pr1 in
          let z2 = pr4.pr1 in
          let h2 = pr4.pr2 in
          let h2' = y2.pr2 in
          internal_paths_rew (f z1)
            (internal_paths_rew (f z2)
              (Obj.magic comp_f_epi z1 z2
                (internal_paths_rew_r (p z1) b
                  (internal_paths_rew_r (p z2) b Coq_paths_refl h2) h1)) x2
              h2') x1 h1'))) (prtoimage (fun x -> f x.pr1) h))

(** val univ_surj :
    'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
    'a3 paths) -> ('a1, 'a2) issurjective -> 'a2 -> 'a3 **)

let univ_surj hsc p f comp_f_epi surjectivep b =
  (surjective_iscontr_im hsc p f comp_f_epi surjectivep b).pr1.pr1

(** val univ_surj_ax :
    'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
    'a3 paths) -> ('a1, 'a2) issurjective -> 'a1 -> 'a3 paths **)

let univ_surj_ax hsc p f comp_f_epi surjectivep x =
  pathsinv0 (f x) (univ_surj hsc p f comp_f_epi surjectivep (p x))
    (path_to_ctr (surjective_iscontr_im hsc p f comp_f_epi surjectivep (p x))
      (f x)
      (squash_to_prop (surjectivep (p x)) isapropishinh (fun r ->
        hinhpr { pr1 = r; pr2 = (comp_f_epi r.pr1 x r.pr2) })))

(** val univ_surj_unique :
    'a3 isaset -> ('a1 -> 'a2) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a2 paths ->
    'a3 paths) -> ('a1, 'a2) issurjective -> ('a2 -> 'a3) -> ('a1 -> 'a3
    paths) -> 'a2 -> 'a3 paths **)

let univ_surj_unique hsc p f comp_f_epi surjectivep g h b =
  surjectionisepitosets p g (univ_surj hsc p f comp_f_epi surjectivep)
    surjectivep hsc (fun x ->
    internal_paths_rew_r (g (p x)) (f x)
      (internal_paths_rew_r (univ_surj hsc p f comp_f_epi surjectivep (p x))
        (f x) Coq_paths_refl (univ_surj_ax hsc p f comp_f_epi surjectivep x))
      (h x)) b

type 'x setquot = ('x hsubtype, 'x iseqclass) total2

(** val make_setquot :
    'a1 hrel -> 'a1 hsubtype -> 'a1 iseqclass -> 'a1 setquot **)

let make_setquot _ a is =
  { pr1 = a; pr2 = is }

(** val pr1setquot : 'a1 hrel -> 'a1 setquot -> 'a1 hsubtype **)

let pr1setquot _ t =
  t.pr1

(** val isinclpr1setquot : 'a1 hrel -> ('a1 setquot, 'a1 hsubtype) isincl **)

let isinclpr1setquot r =
  isinclpr1 (fun x0 -> isapropiseqclass r x0)

(** val isasetsetquot : 'a1 hrel -> 'a1 setquot isaset **)

let isasetsetquot r =
  isasetsubset (fun t -> t.pr1) isasethsubtype
    (isinclpr1 (fun x -> isapropiseqclass r x))

(** val setquotinset : 'a1 hrel -> hSet **)

let setquotinset r =
  make_hSet (isasetsetquot r)

(** val setquotpr : 'a1 eqrel -> 'a1 -> 'a1 setquot **)

let setquotpr r x0 =
  let rax = eqrelrefl r in
  let sax = eqrelsymm r in
  let tax = eqreltrans r in
  { pr1 = (fun x -> pr1eqrel r x0 x); pr2 = { pr1 =
  (hinhpr { pr1 = x0; pr2 = (rax x0) }); pr2 = { pr1 = (fun x1 x2 x3 x4 ->
  tax x0 x1 x2 x4 x3); pr2 = (fun x1 x2 x3 x4 ->
  tax x1 x0 x2 (sax x0 x1 x3) x4) } } }

(** val setquotl0 :
    'a1 eqrel -> 'a1 setquot -> 'a1 carrier -> 'a1 setquot paths **)

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

(** val issurjsetquotpr : 'a1 eqrel -> ('a1, 'a1 setquot) issurjective **)

let issurjsetquotpr r c =
  hinhuniv ishinh (fun x -> hinhpr { pr1 = x.pr1; pr2 = (setquotl0 r c x) })
    (eqax0 (pr1eqrel r) c.pr1 c.pr2)

(** val iscompsetquotpr :
    'a1 eqrel -> 'a1 -> 'a1 -> hProptoType -> 'a1 setquot paths **)

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

type ('x, 'y) iscomprelfun = 'x -> 'x -> hProptoType -> 'y paths

(** val iscomprelfunlogeqf :
    'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> ('a1 -> 'a2) -> ('a1, 'a2)
    iscomprelfun -> ('a1, 'a2) iscomprelfun **)

let iscomprelfunlogeqf _ _ lg _ is x x' r =
  is x x' ((lg x x').pr2 r)

(** val isapropimeqclass :
    'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun ->
    'a1 setquot -> ('a1 carrier, pr1hSet) image isaprop **)

let isapropimeqclass r y f is c =
  isapropsubtype (fun _ -> ishinh) (fun y1 y2 ->
    Obj.magic hinhuniv2 (make_hProp (y.pr2 y1 y2)) (fun x1 x2 ->
      let a = c.pr1 in
      let iseq = c.pr2 in
      let x3 = x1.pr1 in
      let is1 = x1.pr2 in
      let x4 = x2.pr1 in
      let is2 = x2.pr2 in
      let x5 = x3.pr1 in
      let is1' = x3.pr2 in
      let x6 = x4.pr1 in
      let is2' = x4.pr2 in
      let r0 = eqax2 r a iseq x5 x6 is1' is2' in
      Obj.magic pathscomp0 y1 (f x5) y2 (pathsinv0 (f x5) y1 is1)
        (pathscomp0 (f x5) (f x6) y2 (is x5 x6 r0) is2)))

(** val setquotuniv :
    'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun ->
    'a1 setquot -> pr1hSet **)

let setquotuniv r y f is c =
  pr1image (fun x -> f x.pr1)
    (Obj.magic hinhuniv (make_hProp (isapropimeqclass r y f is c))
      (prtoimage (fun x -> f x.pr1)) (eqax0 r c.pr1 c.pr2))

(** val setquotunivcomm :
    'a1 eqrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun ->
    'a1 -> pr1hSet paths **)

let setquotunivcomm _ _ _ _ _ =
  Coq_paths_refl

(** val weqpathsinsetquot :
    'a1 eqrel -> 'a1 -> 'a1 -> (hProptoType, 'a1 setquot paths) weq **)

let weqpathsinsetquot r x x' =
  { pr1 = (iscompsetquotpr r x x'); pr2 =
    (isweqimplimpl (iscompsetquotpr r x x') (fun e ->
      let e' =
        maponpaths (pr1setquot (pr1eqrel r)) (setquotpr r x) (setquotpr r x')
          e
      in
      let e'' =
        maponpaths (fun f -> f x') (fun x0 -> pr1eqrel r x x0) (fun x0 ->
          pr1eqrel r x' x0) e'
      in
      pr1weq
        (eqweqmaphProp (pr1eqrel r x' x') (pr1eqrel r x x')
          (pathsinv0 (pr1eqrel r x x') (pr1eqrel r x' x') e''))
        (eqrelrefl r x')) (pr1eqrel r x x').pr2
      (isasetsetquot (pr1eqrel r) (setquotpr r x) (setquotpr r x'))) }

type ('x, 'y) iscomprelrelfun = 'x -> 'x -> hProptoType -> hProptoType

(** val iscomprelfunlogeqf1 :
    'a1 hrel -> 'a1 hrel -> 'a2 hrel -> 'a1 hrellogeq -> ('a1 -> 'a2) ->
    ('a1, 'a2) iscomprelrelfun -> ('a1, 'a2) iscomprelrelfun **)

let iscomprelfunlogeqf1 _ _ _ lg _ is x x' r =
  is x x' ((lg x x').pr2 r)

(** val iscomprelfunlogeqf2 :
    'a1 hrel -> 'a2 hrel -> 'a2 hrel -> 'a2 hrellogeq -> ('a1 -> 'a2) ->
    ('a1, 'a2) iscomprelrelfun -> ('a1, 'a2) iscomprelrelfun **)

let iscomprelfunlogeqf2 _ _ _ lg f is x x' r =
  (lg (f x) (f x')).pr1 (is x x' r)

(** val setquotfun :
    'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun ->
    'a1 setquot -> 'a2 setquot **)

let setquotfun rX rY f is cx =
  let ff = funcomp f (setquotpr rY) in
  let isff = fun x x' r -> (weqpathsinsetquot rY (f x) (f x')).pr1 (is x x' r)
  in
  Obj.magic setquotuniv rX (setquotinset (pr1eqrel rY)) ff isff cx

(** val setquotfuncomm :
    'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun ->
    'a1 -> 'a2 setquot paths **)

let setquotfuncomm _ _ _ _ _ =
  Coq_paths_refl

(** val setquotunivprop :
    'a1 eqrel -> ('a1 setquot -> hProp) -> ('a1 -> __) -> 'a1 setquot -> __ **)

let setquotunivprop r p ps c =
  hinhuniv (p c) (fun x ->
    let e = setquotl0 r c x in
    (eqweqmaphProp (p (setquotpr r x.pr1)) (p c)
      (maponpaths p (setquotpr r x.pr1) c e)).pr1 (ps x.pr1))
    (eqax0 r.pr1 c.pr1 c.pr2)

(** val setquotuniv2prop :
    'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> hProp) -> ('a1 -> 'a1 ->
    hProptoType) -> 'a1 setquot -> 'a1 setquot -> hProptoType **)

let setquotuniv2prop r p is c c' =
  setquotunivprop r (fun c0' -> p c c0') (fun x ->
    setquotunivprop r (fun c0 -> p c0 (setquotpr r x)) (fun x0 -> is x0 x) c)
    c'

(** val setquotuniv3prop :
    'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> hProp) -> ('a1
    -> 'a1 -> 'a1 -> hProptoType) -> 'a1 setquot -> 'a1 setquot -> 'a1
    setquot -> hProptoType **)

let setquotuniv3prop r p is c c' c'' =
  setquotuniv2prop r (fun c0' c0'' -> p c c0' c0'') (fun x x' ->
    setquotunivprop r (fun c0 -> p c0 (setquotpr r x) (setquotpr r x'))
      (fun x0 -> is x0 x x') c) c' c''

(** val setquotuniv4prop :
    'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> 'a1 setquot ->
    hProp) -> ('a1 -> 'a1 -> 'a1 -> 'a1 -> hProptoType) -> 'a1 setquot -> 'a1
    setquot -> 'a1 setquot -> 'a1 setquot -> hProptoType **)

let setquotuniv4prop r p is c c' c'' c''' =
  setquotuniv3prop r (fun c0 c0' c0'' -> p c c0 c0' c0'') (fun x x' x'' ->
    setquotunivprop r (fun c0 ->
      p c0 (setquotpr r x) (setquotpr r x') (setquotpr r x'')) (fun x0 ->
      is x0 x x' x'') c) c' c'' c'''

(** val issurjsetquotfun :
    'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) issurjective ->
    ('a1, 'a2) iscomprelrelfun -> ('a1 setquot, 'a2 setquot) issurjective **)

let issurjsetquotfun rX rY f is is1 =
  issurjtwooutof3b (setquotpr rX) (setquotfun (pr1eqrel rX) rY f is1)
    (issurjcomp f (setquotpr rY) is (issurjsetquotpr rY))

(** val isinclsetquotfun :
    'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun ->
    ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1 setquot, 'a2 setquot)
    isincl **)

let isinclsetquotfun rX rY f is1 is2 =
  isinclbetweensets (setquotfun (pr1eqrel rX) rY f is1)
    (isasetsetquot (pr1eqrel rX)) (isasetsetquot (pr1eqrel rY))
    (let is = fun x x' ->
       impred (S O) (fun _ -> isasetsetquot (pr1eqrel rX) x x')
     in
     Obj.magic setquotuniv2prop rX (fun x x' -> make_hProp (is x x'))
       (fun x x' ->
       Obj.magic (fun e ->
         let e' = pr1weq (invweq (weqpathsinsetquot rY (f x) (f x'))) e in
         pr1weq (weqpathsinsetquot rX x x') (is2 x x' e'))))

(** val setquotincl :
    'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelrelfun ->
    ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1 setquot, 'a2 setquot)
    incl **)

let setquotincl rX rY f is1 is2 =
  make_incl (setquotfun (pr1eqrel rX) rY f is1)
    (isinclsetquotfun rX rY f is1 is2)

(** val weqsetquotweq :
    'a1 eqrel -> 'a2 eqrel -> ('a1, 'a2) weq -> ('a1, 'a2) iscomprelrelfun ->
    ('a1 -> 'a1 -> hProptoType -> hProptoType) -> ('a1 setquot, 'a2 setquot)
    weq **)

let weqsetquotweq rX rY f is1 is2 =
  let ff = setquotfun (pr1eqrel rX) rY (pr1weq f) is1 in
  { pr1 = ff; pr2 =
  (let is2' = fun y y' ->
     internal_paths_rew_r y (pr1weq f (invmap f y))
       (internal_paths_rew_r y' (pr1weq f (invmap f y'))
         (internal_paths_rew_r (invmap f (pr1weq f (invmap f y)))
           (invmap f y)
           (internal_paths_rew_r (invmap f (pr1weq f (invmap f y')))
             (invmap f y') (is2 (invmap f y) (invmap f y'))
             (homotinvweqweq f (invmap f y')))
           (homotinvweqweq f (invmap f y)))
         (pathsinv0 (pr1weq f (invmap f y')) y' (homotweqinvweq f y')))
       (pathsinv0 (pr1weq f (invmap f y)) y (homotweqinvweq f y))
   in
   let gg = setquotfun (pr1eqrel rY) rX (invmap f) is2' in
   let egf =
     setquotunivprop rX (fun a0 ->
       make_hProp (isasetsetquot (pr1eqrel rX) (gg (ff a0)) a0)) (fun x ->
       Obj.magic maponpaths (setquotpr rX) (invmap f (pr1weq f x)) x
         (homotinvweqweq f x))
   in
   let efg =
     setquotunivprop rY (fun a0 ->
       make_hProp (isasetsetquot (pr1eqrel rY) (ff (gg a0)) a0)) (fun x ->
       Obj.magic maponpaths (setquotpr rY) (pr1weq f (invmap f x)) x
         (homotweqinvweq f x))
   in
   isweq_iso ff gg (Obj.magic egf) (Obj.magic efg)) }

(** val weqsetquotsurj :
    'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a2) -> ('a1, 'a2) issurjective ->
    ('a1, 'a2) iscomprelrelfun -> ('a1 -> 'a1 -> hProptoType -> hProptoType)
    -> ('a1 setquot, 'a2 setquot) weq **)

let weqsetquotsurj rX rY f is is1 is2 =
  let ff = setquotfun (pr1eqrel rX) rY f is1 in
  { pr1 = ff; pr2 =
  (isweqinclandsurj ff (isinclsetquotfun rX rY f is1 is2)
    (issurjsetquotfun rX rY f is is1)) }

(** val setquottodirprod :
    'a1 eqrel -> 'a2 eqrel -> ('a1, 'a2) dirprod setquot -> ('a1 setquot, 'a2
    setquot) dirprod **)

let setquottodirprod rX rY cc =
  let rXY = eqreldirprod rX rY in
  make_dirprod
    (Obj.magic setquotuniv (pr1eqrel rXY) (setquotinset (pr1eqrel rX))
      (funcomp (fun t -> t.pr1) (Obj.magic setquotpr rX)) (fun xy xy' rr ->
      Obj.magic iscompsetquotpr rX xy.pr1 xy'.pr1 (Obj.magic rr).pr1) cc)
    (Obj.magic setquotuniv (pr1eqrel rXY) (setquotinset (pr1eqrel rY))
      (funcomp (fun t -> t.pr2) (Obj.magic setquotpr rY)) (fun xy xy' rr ->
      Obj.magic iscompsetquotpr rY xy.pr2 xy'.pr2 (Obj.magic rr).pr2) cc)

(** val dirprodtosetquot :
    'a1 hrel -> 'a2 hrel -> ('a1 setquot, 'a2 setquot) dirprod -> ('a1, 'a2)
    dirprod setquot **)

let dirprodtosetquot rX rY cd =
  make_setquot (hreldirprod rX rY) (subtypesdirprod cd.pr1.pr1 cd.pr2.pr1)
    (iseqclassdirprod rX rY cd.pr1.pr1 cd.pr2.pr1 cd.pr1.pr2 cd.pr2.pr2)

(** val weqsetquottodirprod :
    'a1 eqrel -> 'a2 eqrel -> (('a1, 'a2) dirprod setquot, ('a1 setquot, 'a2
    setquot) dirprod) weq **)

let weqsetquottodirprod rX rY =
  let f = setquottodirprod rX rY in
  let g = dirprodtosetquot (pr1eqrel rX) (pr1eqrel rY) in
  { pr1 = f; pr2 =
  (let egf =
     setquotunivprop (eqreldirprod rX rY) (fun a ->
       make_hProp
         (isasetsetquot (hreldirprod (pr1eqrel rX) (pr1eqrel rY)) (g (f a)) a))
       (fun xy ->
       let x = xy.pr1 in
       let y = xy.pr2 in
       Obj.magic invmaponpathsincl
         (pr1setquot (hreldirprod (pr1eqrel rX) (pr1eqrel rY)))
         (isinclpr1setquot
           (Obj.magic hreldirprod (pr1eqrel rX) (pr1eqrel rY)))
         (g (f (setquotpr (eqreldirprod rX rY) { pr1 = x; pr2 = y })))
         (setquotpr (eqreldirprod rX rY) { pr1 = x; pr2 = y })
         (funextsec
           (Obj.magic subtypesdirprod (fun x0 -> pr1eqrel rX x x0) (fun x0 ->
             pr1eqrel rY y x0)) (fun x0 ->
           Obj.magic hreldirprod (pr1eqrel rX) (pr1eqrel rY) { pr1 = x; pr2 =
             y } x0) (fun _ -> Coq_paths_refl)))
   in
   let efg = fun a ->
     let ax = a.pr1 in
     let ay = a.pr2 in
     pathsdirprod
       (Obj.magic setquotuniv (pr1eqrel (eqreldirprod rX rY))
         (setquotinset (pr1eqrel rX))
         (funcomp (fun t -> t.pr1) (Obj.magic setquotpr rX))
         (fun xy xy' rr ->
         Obj.magic iscompsetquotpr rX xy.pr1 xy'.pr1 (Obj.magic rr).pr1)
         (Obj.magic g { pr1 = ax; pr2 = ay })) ax
       (Obj.magic setquotuniv (pr1eqrel (eqreldirprod rX rY))
         (setquotinset (pr1eqrel rY))
         (funcomp (fun t -> t.pr2) (Obj.magic setquotpr rY))
         (fun xy xy' rr ->
         Obj.magic iscompsetquotpr rY xy.pr2 xy'.pr2 (Obj.magic rr).pr2)
         (Obj.magic g { pr1 = ax; pr2 = ay })) ay
       (Obj.magic setquotunivprop rX (fun ax0 ->
         make_hProp
           (isasetsetquot (pr1eqrel rX)
             (Obj.magic setquotuniv (pr1eqrel (eqreldirprod rX rY))
               (setquotinset (pr1eqrel rX))
               (funcomp (fun t -> t.pr1) (Obj.magic setquotpr rX))
               (fun xy xy' rr ->
               Obj.magic iscompsetquotpr rX xy.pr1 xy'.pr1 (Obj.magic rr).pr1)
               (Obj.magic g { pr1 = ax0; pr2 = ay })) ax0)) (fun x ->
         setquotunivprop (Obj.magic rY) (fun ay0 ->
           make_hProp
             (isasetsetquot (pr1eqrel rX)
               (Obj.magic setquotuniv
                 (hreldirprod (pr1eqrel rX) (pr1eqrel rY))
                 (setquotinset (pr1eqrel rX))
                 (funcomp (fun t -> t.pr1) (Obj.magic setquotpr rX))
                 (fun xy xy' rr ->
                 Obj.magic iscompsetquotpr rX xy.pr1 xy'.pr1
                   (Obj.magic rr).pr1)
                 (Obj.magic g { pr1 = (setquotpr rX x); pr2 = ay0 }))
               (setquotpr rX x))) (fun y ->
           Obj.magic invmaponpathsincl (pr1setquot (pr1eqrel rX))
             (isinclpr1setquot (pr1eqrel (Obj.magic rX)))
             (setquotuniv (hreldirprod (pr1eqrel rX) (pr1eqrel rY))
               (setquotinset (pr1eqrel rX))
               (funcomp (fun t -> t.pr1) (Obj.magic setquotpr rX))
               (fun xy xy' rr ->
               Obj.magic iscompsetquotpr rX xy.pr1 xy'.pr1 (Obj.magic rr).pr1)
               (Obj.magic g { pr1 = (setquotpr rX x); pr2 =
                 (setquotpr (Obj.magic rY) y) })) (setquotpr rX x)
             (funextsec
               (Obj.magic pr1setquot (pr1eqrel (Obj.magic rX))
                 (setquotuniv (hreldirprod (pr1eqrel rX) (pr1eqrel rY))
                   (setquotinset (pr1eqrel rX))
                   (funcomp (fun t -> t.pr1) (Obj.magic setquotpr rX))
                   (fun xy xy' rr ->
                   Obj.magic iscompsetquotpr rX xy.pr1 xy'.pr1
                     (Obj.magic rr).pr1)
                   (Obj.magic g { pr1 = (setquotpr rX x); pr2 =
                     (setquotpr (Obj.magic rY) y) })))
               (Obj.magic pr1setquot (pr1eqrel (Obj.magic rX))
                 (setquotpr (Obj.magic rX) (Obj.magic x))) (fun _ ->
               Coq_paths_refl))) ay) ax)
       (Obj.magic setquotunivprop rX (fun ax0 ->
         make_hProp
           (isasetsetquot (pr1eqrel (Obj.magic rY))
             (Obj.magic setquotuniv (pr1eqrel (eqreldirprod rX rY))
               (setquotinset (pr1eqrel rY))
               (funcomp (fun t -> t.pr2) (Obj.magic setquotpr rY))
               (fun xy xy' rr ->
               Obj.magic iscompsetquotpr rY xy.pr2 xy'.pr2 (Obj.magic rr).pr2)
               (Obj.magic g { pr1 = ax0; pr2 = ay })) ay)) (fun x ->
         setquotunivprop (Obj.magic rY) (fun ay0 ->
           make_hProp
             (isasetsetquot (pr1eqrel (Obj.magic rY))
               (Obj.magic setquotuniv
                 (hreldirprod (pr1eqrel rX) (pr1eqrel rY))
                 (setquotinset (pr1eqrel rY))
                 (funcomp (fun t -> t.pr2) (Obj.magic setquotpr rY))
                 (fun xy xy' rr ->
                 Obj.magic iscompsetquotpr rY xy.pr2 xy'.pr2
                   (Obj.magic rr).pr2)
                 (Obj.magic g { pr1 = (setquotpr rX x); pr2 = ay0 })) ay0))
           (fun y ->
           Obj.magic invmaponpathsincl (pr1setquot (pr1eqrel (Obj.magic rY)))
             (isinclpr1setquot (pr1eqrel (Obj.magic rY)))
             (setquotuniv (hreldirprod (pr1eqrel rX) (pr1eqrel rY))
               (setquotinset (pr1eqrel rY))
               (funcomp (fun t -> t.pr2) (Obj.magic setquotpr rY))
               (fun xy xy' rr ->
               Obj.magic iscompsetquotpr rY xy.pr2 xy'.pr2 (Obj.magic rr).pr2)
               (Obj.magic g { pr1 = (setquotpr rX x); pr2 =
                 (setquotpr (Obj.magic rY) y) }))
             (setquotpr (Obj.magic rY) y)
             (funextsec
               (Obj.magic pr1setquot (pr1eqrel (Obj.magic rY))
                 (setquotuniv (hreldirprod (pr1eqrel rX) (pr1eqrel rY))
                   (setquotinset (pr1eqrel rY))
                   (funcomp (fun t -> t.pr2) (Obj.magic setquotpr rY))
                   (fun xy xy' rr ->
                   Obj.magic iscompsetquotpr rY xy.pr2 xy'.pr2
                     (Obj.magic rr).pr2)
                   (Obj.magic g { pr1 = (setquotpr rX x); pr2 =
                     (setquotpr (Obj.magic rY) y) })))
               (Obj.magic pr1setquot (pr1eqrel (Obj.magic rY))
                 (setquotpr (Obj.magic rY) y)) (fun _ -> Coq_paths_refl))) ay)
         ax)
   in
   isweq_iso f g (Obj.magic egf) (Obj.magic efg)) }

type ('x, 'y) iscomprelfun2 =
  'x -> 'x -> 'x -> 'x -> hProptoType -> hProptoType -> 'y paths

(** val iscomprelfun2if :
    'a1 hrel -> ('a1 -> 'a1 -> 'a2) -> ('a1 -> 'a1 -> 'a1 -> hProptoType ->
    'a2 paths) -> ('a1 -> 'a1 -> 'a1 -> hProptoType -> 'a2 paths) -> ('a1,
    'a2) iscomprelfun2 **)

let iscomprelfun2if _ f is1 is2 x x' x0 x0' r r' =
  let e = is1 x x' x0 r in
  let e' = is2 x' x0 x0' r' in pathscomp0 (f x x0) (f x' x0) (f x' x0') e e'

(** val iscomprelfun2logeqf :
    'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> ('a1 -> 'a1 -> 'a2) -> ('a1,
    'a2) iscomprelfun2 -> ('a1, 'a2) iscomprelfun2 **)

let iscomprelfun2logeqf _ _ lg _ is x x' x0 x0' r r0 =
  is x x' x0 x0' ((lg x x').pr2 r) ((lg x0 x0').pr2 r0)

(** val setquotuniv2_iscomprelfun :
    'a1 hrel -> hSet -> ('a1 -> 'a1 -> pr1hSet) -> ('a1, pr1hSet)
    iscomprelfun2 -> 'a1 setquot -> 'a1 setquot -> (('a1, 'a1) dirprod,
    pr1hSet) iscomprelfun **)

let setquotuniv2_iscomprelfun _ _ _ is _ _ xy x'y' dp =
  let r = (Obj.magic dp).pr1 in
  let r' = (Obj.magic dp).pr2 in is xy.pr1 x'y'.pr1 xy.pr2 x'y'.pr2 r r'

(** val setquotuniv2 :
    'a1 hrel -> hSet -> ('a1 -> 'a1 -> pr1hSet) -> ('a1, pr1hSet)
    iscomprelfun2 -> 'a1 setquot -> 'a1 setquot -> pr1hSet **)

let setquotuniv2 r y f is c c0 =
  let ff = fun xy -> f xy.pr1 xy.pr2 in
  let rR = hreldirprod r r in
  setquotuniv rR y ff (setquotuniv2_iscomprelfun r y f is c c0)
    (dirprodtosetquot r r (make_dirprod c c0))

(** val setquotuniv2comm :
    'a1 eqrel -> hSet -> ('a1 -> 'a1 -> pr1hSet) -> ('a1, pr1hSet)
    iscomprelfun2 -> 'a1 -> 'a1 -> pr1hSet paths **)

let setquotuniv2comm _ _ _ _ _ _ =
  Coq_paths_refl

type ('x, 'y) iscomprelrelfun2 =
  'x -> 'x -> 'x -> 'x -> hProptoType -> hProptoType -> hProptoType

(** val iscomprelrelfun2if :
    'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1 -> 'a1 -> 'a1 ->
    hProptoType -> hProptoType) -> ('a1 -> 'a1 -> 'a1 -> hProptoType ->
    hProptoType) -> ('a1, 'a2) iscomprelrelfun2 **)

let iscomprelrelfun2if _ rY f is1 is2 x x' x0 x0' r r' =
  let e = is1 x x' x0 r in
  let e' = is2 x' x0 x0' r' in
  eqreltrans rY (f x x0) (f x' x0) (f x' x0') e e'

(** val iscomprelrelfun2logeqf1 :
    'a1 hrel -> 'a1 hrel -> 'a2 hrel -> 'a1 hrellogeq -> ('a1 -> 'a1 -> 'a2)
    -> ('a1, 'a2) iscomprelrelfun2 -> ('a1, 'a2) iscomprelrelfun2 **)

let iscomprelrelfun2logeqf1 _ _ _ lg _ is x x' x0 x0' r r0 =
  is x x' x0 x0' ((lg x x').pr2 r) ((lg x0 x0').pr2 r0)

(** val iscomprelrelfun2logeqf2 :
    'a1 hrel -> 'a2 hrel -> 'a2 hrel -> 'a2 hrellogeq -> ('a1 -> 'a1 -> 'a2)
    -> ('a1, 'a2) iscomprelrelfun2 -> ('a1, 'a2) iscomprelrelfun2 **)

let iscomprelrelfun2logeqf2 _ _ _ lg f is x x' x0 x0' r r0 =
  (lg (f x x0) (f x' x0')).pr1 (is x x' x0 x0' r r0)

(** val setquotfun2_iscomprelfun2 :
    'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2)
    iscomprelrelfun2 -> 'a1 setquot -> 'a1 setquot -> ('a1, 'a2 setquot)
    iscomprelfun2 **)

let setquotfun2_iscomprelfun2 _ rY f is _ _ x x' x0 x0' r r0 =
  (weqpathsinsetquot rY (f x x0) (f x' x0')).pr1 (is x x' x0 x0' r r0)

(** val setquotfun2 :
    'a1 hrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2)
    iscomprelrelfun2 -> 'a1 setquot -> 'a1 setquot -> 'a2 setquot **)

let setquotfun2 rX rY f is cx cx0 =
  let ff = fun x x0 -> setquotpr rY (f x x0) in
  Obj.magic setquotuniv2 rX (setquotinset (pr1eqrel rY)) ff
    (setquotfun2_iscomprelfun2 rX rY f is cx cx0) cx cx0

(** val setquotfun2comm :
    'a1 eqrel -> 'a2 eqrel -> ('a1 -> 'a1 -> 'a2) -> ('a1, 'a2)
    iscomprelrelfun2 -> 'a1 -> 'a1 -> 'a2 setquot paths **)

let setquotfun2comm _ _ _ _ _ _ =
  Coq_paths_refl

(** val isdeceqsetquot_non_constr :
    'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot isdeceq **)

let isdeceqsetquot_non_constr r is =
  isdeceqif (fun x x' ->
    Obj.magic setquotuniv2prop r (fun _ _ -> make_hProp isapropisdecprop)
      (fun x0 x0' ->
      Obj.magic isdecpropweqf (weqpathsinsetquot r x0 x0') (is x0 x0')) x x')

(** val setquotbooleqint :
    'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 -> 'a1 -> bool **)

let setquotbooleqint _ is x x' =
  let c = (is x x').pr1 in
  (match c with
   | Coq_ii1 _ -> Coq_true
   | Coq_ii2 _ -> Coq_false)

(** val setquotbooleqintcomp :
    'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> ('a1, bool)
    iscomprelfun2 **)

let setquotbooleqintcomp _ is x x' x0 x0' _ _ =
  let c = (is x x0).pr1 in
  (match c with
   | Coq_ii1 _ ->
     let c0 = (is x' x0').pr1 in
     (match c0 with
      | Coq_ii1 _ -> Coq_paths_refl
      | Coq_ii2 _ -> assert false (* absurd case *))
   | Coq_ii2 _ ->
     let c0 = (is x' x0').pr1 in
     (match c0 with
      | Coq_ii1 _ -> assert false (* absurd case *)
      | Coq_ii2 _ -> Coq_paths_refl))

(** val setquotbooleq :
    'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot -> 'a1
    setquot -> bool **)

let setquotbooleq r is =
  Obj.magic setquotuniv2 (pr1eqrel r) (make_hSet isasetbool)
    (setquotbooleqint r is) (setquotbooleqintcomp r is)

(** val setquotbooleqtopaths :
    'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot -> 'a1
    setquot -> bool paths -> 'a1 setquot paths **)

let setquotbooleqtopaths r is x x' =
  let isp = fun x0 x'0 ->
    impred (S O) (fun _ -> isasetsetquot (pr1eqrel r) x0 x'0)
  in
  Obj.magic setquotuniv2prop r (fun x0 x'0 -> make_hProp (isp x0 x'0))
    (fun x0 x'0 ->
    let c = (is x0 x'0).pr1 in
    (match c with
     | Coq_ii1 a -> Obj.magic (fun _ -> pr1weq (weqpathsinsetquot r x0 x'0) a)
     | Coq_ii2 _ -> Obj.magic (fun _ -> assert false (* absurd case *)))) x x'

(** val setquotpathstobooleq :
    'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot -> 'a1
    setquot -> 'a1 setquot paths -> bool paths **)

let setquotpathstobooleq r is x _ _ =
  Obj.magic setquotunivprop r (fun x0 ->
    make_hProp (isasetbool (setquotbooleq r is x0 x0) Coq_true)) (fun x0 ->
    let c = (is x0 x0).pr1 in
    (match c with
     | Coq_ii1 _ -> Obj.magic Coq_paths_refl
     | Coq_ii2 _ -> assert false (* absurd case *))) x

(** val isdeceqsetquot :
    'a1 eqrel -> ('a1 -> 'a1 -> hProptoType isdecprop) -> 'a1 setquot isdeceq **)

let isdeceqsetquot r is x x' =
  let c = boolchoice (setquotbooleq r is x x') in
  (match c with
   | Coq_ii1 a -> Coq_ii1 (setquotbooleqtopaths r is x x' a)
   | Coq_ii2 _ -> Coq_ii2 (fun _ -> assert false (* absurd case *)))

type 'x iscomprelrel = ('x, hProp) iscomprelfun2

(** val iscomprelrelif :
    'a1 hrel -> 'a1 hrel -> 'a1 issymm -> ('a1 -> 'a1 -> 'a1 -> hProptoType
    -> hProptoType -> hProptoType) -> ('a1 -> 'a1 -> 'a1 -> hProptoType ->
    hProptoType -> hProptoType) -> 'a1 iscomprelrel **)

let iscomprelrelif _ l isr i1 i2 x x' y y' rx ry =
  let rx' = isr x x' rx in
  let ry' = isr y y' ry in
  hPropUnivalence (l x y) (l x' y') (fun lxy ->
    let int1 = i1 x x' y rx lxy in i2 x' y y' ry int1) (fun lxy' ->
    let int1 = i1 x' x y' rx' lxy' in i2 x y' y ry' int1)

(** val iscomprelrellogeqf1 :
    'a1 hrel -> 'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> 'a1 iscomprelrel ->
    'a1 iscomprelrel **)

let iscomprelrellogeqf1 r r' l lg is =
  iscomprelfun2logeqf r r' lg l is

(** val iscomprelrellogeqf2 :
    'a1 hrel -> 'a1 hrel -> 'a1 hrel -> 'a1 hrellogeq -> 'a1 iscomprelrel ->
    'a1 iscomprelrel **)

let iscomprelrellogeqf2 _ _ _ _ is =
  is

(** val quotrel :
    'a1 hrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 setquot hrel **)

let quotrel r l is =
  Obj.magic setquotuniv2 r hPropset l is

(** val istransquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 istrans -> 'a1 setquot
    istrans **)

let istransquotrel r l is isl =
  let int = fun x1 _ x3 ->
    impred (S O) (fun _ ->
      impred (S O) (fun _ -> (quotrel (pr1eqrel r) l is x1 x3).pr2))
  in
  Obj.magic setquotuniv3prop r (fun x1 x2 x3 -> make_hProp (int x1 x2 x3))
    (fun x x' x'' -> Obj.magic (fun r0 r' -> isl x x' x'' r0 r'))

(** val issymmquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 issymm -> 'a1 setquot
    issymm **)

let issymmquotrel r l is isl =
  let int = fun x1 x2 ->
    impred (S O) (fun _ -> (quotrel (pr1eqrel r) l is x2 x1).pr2)
  in
  Obj.magic setquotuniv2prop r (fun x1 x2 -> make_hProp (int x1 x2))
    (fun x x' -> Obj.magic (fun r0 -> isl x x' r0))

(** val isreflquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isrefl -> 'a1 setquot
    isrefl **)

let isreflquotrel r l is isl =
  setquotunivprop r (fun c -> quotrel (pr1eqrel r) l is c c) isl

(** val ispoquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 ispreorder -> 'a1
    setquot ispreorder **)

let ispoquotrel r l is isl =
  { pr1 = (istransquotrel r l is isl.pr1); pr2 =
    (isreflquotrel r l is isl.pr2) }

(** val iseqrelquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iseqrel -> 'a1 setquot
    iseqrel **)

let iseqrelquotrel r l is isl =
  { pr1 = (ispoquotrel r l is isl.pr1); pr2 = (issymmquotrel r l is isl.pr2) }

(** val isirreflquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isirrefl -> 'a1 setquot
    isirrefl **)

let isirreflquotrel r _ _ isl =
  Obj.magic setquotunivprop r (fun _ -> make_hProp isapropneg) (fun x ->
    Obj.magic isl x)

(** val isasymmquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isasymm -> 'a1 setquot
    isasymm **)

let isasymmquotrel r _ _ isl =
  let int = fun _ _ ->
    impred (S O) (fun _ -> impred (S O) (fun _ -> isapropempty))
  in
  Obj.magic setquotuniv2prop r (fun x1 x2 -> make_hProp (int x1 x2))
    (fun x x' -> Obj.magic (fun r0 r' -> isl x x' r0 r'))

(** val iscoasymmquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscoasymm -> 'a1 setquot
    iscoasymm **)

let iscoasymmquotrel r l is isl =
  let int = fun x1 x2 ->
    impred (S O) (fun _ -> (quotrel (pr1eqrel r) l is x2 x1).pr2)
  in
  Obj.magic setquotuniv2prop r (fun x1 x2 -> make_hProp (int x1 x2))
    (fun x x' -> Obj.magic (fun r0 -> isl x x' r0))

(** val istotalquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 istotal -> 'a1 setquot
    istotal **)

let istotalquotrel r _ _ isl =
  setquotuniv2prop r (fun _ _ -> hdisj) (fun x x' ->
    Obj.magic (fun r0 r' -> Obj.magic isl x x' r0 r'))

(** val iscotransquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscotrans -> 'a1 setquot
    iscotrans **)

let iscotransquotrel r _ _ isl =
  let int = fun _ _ _ -> impred (S O) (fun _ -> hdisj.pr2) in
  Obj.magic setquotuniv3prop r (fun x1 x2 x3 -> make_hProp (int x1 x2 x3))
    (fun x x' x'' -> Obj.magic (fun r0 -> isl x x' x'' r0))

(** val isantisymmquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isantisymm -> 'a1
    setquot isantisymm **)

let isantisymmquotrel r _ _ isl =
  let int = fun x1 x2 ->
    impred (S O) (fun _ ->
      impred (S O) (fun _ -> isasetsetquot (pr1eqrel r) x1 x2))
  in
  Obj.magic setquotuniv2prop r (fun x1 x2 -> make_hProp (int x1 x2))
    (fun x x' ->
    Obj.magic (fun r0 r' -> maponpaths (setquotpr r) x x' (isl x x' r0 r')))

(** val isantisymmnegquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isantisymmneg -> 'a1
    setquot isantisymmneg **)

let isantisymmnegquotrel r _ _ isl =
  let int = fun x1 x2 ->
    impred (S O) (fun _ ->
      impred (S O) (fun _ -> isasetsetquot (pr1eqrel r) x1 x2))
  in
  Obj.magic setquotuniv2prop r (fun x1 x2 -> make_hProp (int x1 x2))
    (fun x x' ->
    Obj.magic (fun r0 r' -> maponpaths (setquotpr r) x x' (isl x x' r0 r')))

(** val quotrelimpl :
    'a1 eqrel -> 'a1 hrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscomprelrel
    -> ('a1 -> 'a1 -> hProptoType -> hProptoType) -> 'a1 setquot -> 'a1
    setquot -> hProptoType -> hProptoType **)

let quotrelimpl r _ l' _ is' impl x x' ql =
  let int = fun x0 x0' ->
    impred (S O) (fun _ -> (quotrel (pr1eqrel r) l' is' x0 x0').pr2)
  in
  Obj.magic setquotuniv2prop r (fun x0 x0' -> make_hProp (int x0 x0'))
    (fun x0 x0' -> Obj.magic impl x0 x0') x x' ql

(** val quotrellogeq :
    'a1 eqrel -> 'a1 hrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 iscomprelrel
    -> ('a1 -> 'a1 -> (hProptoType, hProptoType) logeq) -> 'a1 setquot -> 'a1
    setquot -> (hProptoType, hProptoType) logeq **)

let quotrellogeq r l l' is is' lg x x' =
  { pr1 = (quotrelimpl r l l' is is' (fun x0 x0' -> (lg x0 x0').pr1) x x');
    pr2 = (quotrelimpl r l' l is' is (fun x0 x0' -> (lg x0 x0').pr2) x x') }

(** val quotdecrelint :
    'a1 hrel -> 'a1 decrel -> 'a1 iscomprelrel -> 'a1 setquot brel **)

let quotdecrelint r l _ =
  let f = decreltobrel l in
  Obj.magic setquotuniv2 r boolset f (fun x x' x0 x0' _ _ ->
    let c = l.pr2 x x0' in
    (match c with
     | Coq_ii1 _ ->
       let c0 = l.pr2 x' x0' in
       (match c0 with
        | Coq_ii1 _ ->
          let c1 = l.pr2 x x0 in
          (match c1 with
           | Coq_ii1 _ -> Coq_paths_refl
           | Coq_ii2 _ -> assert false (* absurd case *))
        | Coq_ii2 _ ->
          let c1 = l.pr2 x x0 in
          (match c1 with
           | Coq_ii1 _ -> assert false (* absurd case *)
           | Coq_ii2 _ -> Coq_paths_refl))
     | Coq_ii2 _ ->
       let c0 = l.pr2 x x0 in
       (match c0 with
        | Coq_ii1 _ ->
          let c1 = l.pr2 x' x0' in
          (match c1 with
           | Coq_ii1 _ -> Coq_paths_refl
           | Coq_ii2 _ -> assert false (* absurd case *))
        | Coq_ii2 _ ->
          let c1 = l.pr2 x' x0' in
          (match c1 with
           | Coq_ii1 _ -> assert false (* absurd case *)
           | Coq_ii2 _ -> Coq_paths_refl))))

(** val quotdecrelintlogeq :
    'a1 eqrel -> 'a1 decrel -> 'a1 iscomprelrel -> 'a1 setquot -> 'a1 setquot
    -> (hProptoType, hProptoType) logeq **)

let quotdecrelintlogeq r l is x x' =
  let int = fun x0 x'0 ->
    isapropdirprod
      (impred (S O) (fun _ -> (quotrel (pr1eqrel r) l.pr1 is x0 x'0).pr2))
      (impred (S O) (fun _ ->
        isasetbool (quotdecrelint (pr1eqrel r) l is x0 x'0) Coq_true))
  in
  Obj.magic setquotuniv2prop r (fun x0 x'0 -> make_hProp (int x0 x'0))
    (fun x0 x'0 ->
    Obj.magic { pr1 = (pathstor l x0 x'0); pr2 = (rtopaths l x0 x'0) }) x x'

(** val isdecquotrel :
    'a1 eqrel -> 'a1 hrel -> 'a1 iscomprelrel -> 'a1 isdecrel -> 'a1 setquot
    isdecrel **)

let isdecquotrel r l is isl =
  isdecrellogeqf
    (pr1decrel
      (breltodecrel (quotdecrelint (pr1eqrel r) (make_decrel l isl) is)))
    (quotrel (pr1eqrel r) (make_decrel l isl).pr1 is)
    (quotdecrelintlogeq r (make_decrel l isl) is)
    (breltodecrel (quotdecrelint (pr1eqrel r) (make_decrel l isl) is)).pr2

(** val decquotrel :
    'a1 eqrel -> 'a1 decrel -> 'a1 iscomprelrel -> 'a1 setquot decrel **)

let decquotrel r l is =
  make_decrel (quotrel (pr1eqrel r) (pr1decrel l) is)
    (isdecquotrel r (pr1decrel l) is l.pr2)

(** val reseqrel : 'a1 eqrel -> 'a1 hsubtype -> 'a1 carrier eqrel **)

let reseqrel r p =
  make_eqrel (resrel (pr1eqrel r) p) (iseqrelresrel (pr1eqrel r) p r.pr2)

(** val iseqclassresrel :
    'a1 hrel -> 'a1 hsubtype -> 'a1 hsubtype -> 'a1 iseqclass -> ('a1 ->
    hProptoType -> hProptoType) -> 'a1 carrier iseqclass **)

let iseqclassresrel _ p _ is is' =
  { pr1 =
    (let l1 = is.pr1 in
     hinhfun (fun q -> { pr1 = (make_carrier p q.pr1 (is' q.pr1 q.pr2));
       pr2 = q.pr2 }) l1); pr2 = { pr1 = (fun p1 p2 r12 q1 ->
    is.pr2.pr1 p1.pr1 p2.pr1 r12 q1); pr2 = (fun p1 p2 q1 q2 ->
    is.pr2.pr2 p1.pr1 p2.pr1 q1 q2) } }

(** val fromsubquot :
    'a1 eqrel -> 'a1 setquot hsubtype -> 'a1 setquot carrier -> 'a1 carrier
    setquot **)

let fromsubquot r p p0 =
  { pr1 = (fun rp -> pr1setquot (pr1eqrel r) p0.pr1 rp.pr1); pr2 =
    (iseqclassresrel (pr1eqrel r) (funcomp (setquotpr r) p) p0.pr1.pr1
      p0.pr1.pr2 (fun x px ->
      let e = setquotl0 r p0.pr1 (make_carrier p0.pr1.pr1 x px) in
      internal_paths_rew_r (setquotpr r x) p0.pr1 p0.pr2 e)) }

(** val tosubquot :
    'a1 eqrel -> 'a1 setquot hsubtype -> 'a1 carrier setquot -> 'a1 setquot
    carrier **)

let tosubquot r p =
  let int =
    isasetsubset (fun t -> t.pr1)
      (Obj.magic setproperty (setquotinset (pr1eqrel r))) (isinclpr1carrier p)
  in
  Obj.magic setquotuniv (resrel (pr1eqrel r) (funcomp (setquotpr r) p))
    (make_hSet int) (fun xp ->
    Obj.magic make_carrier p (setquotpr r xp.pr1) xp.pr2)
    (fun xp1 xp2 rp12 ->
    invmaponpathsincl (Obj.magic pr1carrier p) (isinclpr1carrier p)
      (Obj.magic make_carrier p (setquotpr r xp1.pr1) xp1.pr2)
      (Obj.magic make_carrier p (setquotpr r xp2.pr1) xp2.pr2)
      (iscompsetquotpr r xp1.pr1 xp2.pr1 rp12))

(** val weqsubquot :
    'a1 eqrel -> 'a1 setquot hsubtype -> ('a1 setquot carrier, 'a1 carrier
    setquot) weq **)

let weqsubquot r p =
  let f = fromsubquot r p in
  let g = tosubquot r p in
  { pr1 = f; pr2 =
  (let int0 =
     isasetsubset (fun t -> t.pr1)
       (Obj.magic setproperty (setquotinset (pr1eqrel r)))
       (isinclpr1carrier p)
   in
   let egf = fun a ->
     let p0 = a.pr1 in
     let isp = a.pr2 in
     let int = fun p1 ->
       impred (S O) (fun t ->
         int0 (g (f { pr1 = p1; pr2 = t })) { pr1 = p1; pr2 = t })
     in
     Obj.magic setquotunivprop r (fun a0 -> make_hProp (int a0)) (fun x ->
       Obj.magic (fun isp0 ->
         invmaponpathsincl (pr1carrier p) (isinclpr1carrier p)
           (g (f { pr1 = (setquotpr r x); pr2 = isp0 })) { pr1 =
           (setquotpr r x); pr2 = isp0 } Coq_paths_refl)) p0 isp
   in
   let efg =
     let int = fun a ->
       setproperty
         (setquotinset (resrel (pr1eqrel r) (funcomp (setquotpr r) p)))
         (Obj.magic f (Obj.magic g a)) a
     in
     let q = reseqrel r (funcomp (setquotpr r) p) in
     setquotunivprop q (fun a -> make_hProp (Obj.magic int a)) (fun a ->
       Obj.magic invmaponpathsincl (fun t -> t.pr1)
         (isinclpr1 (fun a0 ->
           isapropiseqclass (resrel (pr1eqrel r) (funcomp (setquotpr r) p)) a0))
         { pr1 = (fun rp ->
         pr1setquot (pr1eqrel r)
           (Obj.magic setquotuniv
             (resrel (pr1eqrel r) (funcomp (setquotpr r) p))
             (make_hSet
               (isasetsubset (fun t -> t.pr1)
                 (Obj.magic setproperty (setquotinset (pr1eqrel r)))
                 (isinclpr1carrier p))) (fun xp ->
             Obj.magic make_carrier p (setquotpr r xp.pr1) xp.pr2)
             (fun xp1 xp2 rp12 ->
             invmaponpathsincl (Obj.magic pr1carrier p) (isinclpr1carrier p)
               (Obj.magic make_carrier p (setquotpr r xp1.pr1) xp1.pr2)
               (Obj.magic make_carrier p (setquotpr r xp2.pr1) xp2.pr2)
               (iscompsetquotpr r xp1.pr1 xp2.pr1 rp12)) (setquotpr q a)).pr1
           rp.pr1); pr2 =
         (iseqclassresrel (pr1eqrel r) (funcomp (setquotpr r) p)
           (Obj.magic setquotuniv
             (resrel (pr1eqrel r) (funcomp (setquotpr r) p))
             (make_hSet
               (isasetsubset (fun t -> t.pr1)
                 (Obj.magic setproperty (setquotinset (pr1eqrel r)))
                 (isinclpr1carrier p))) (fun xp ->
             Obj.magic make_carrier p (setquotpr r xp.pr1) xp.pr2)
             (fun xp1 xp2 rp12 ->
             invmaponpathsincl (Obj.magic pr1carrier p) (isinclpr1carrier p)
               (Obj.magic make_carrier p (setquotpr r xp1.pr1) xp1.pr2)
               (Obj.magic make_carrier p (setquotpr r xp2.pr1) xp2.pr2)
               (iscompsetquotpr r xp1.pr1 xp2.pr1 rp12)) (setquotpr q a)).pr1.pr1
           (Obj.magic setquotuniv
             (resrel (pr1eqrel r) (funcomp (setquotpr r) p))
             (make_hSet
               (isasetsubset (fun t -> t.pr1)
                 (Obj.magic setproperty (setquotinset (pr1eqrel r)))
                 (isinclpr1carrier p))) (fun xp ->
             Obj.magic make_carrier p (setquotpr r xp.pr1) xp.pr2)
             (fun xp1 xp2 rp12 ->
             invmaponpathsincl (Obj.magic pr1carrier p) (isinclpr1carrier p)
               (Obj.magic make_carrier p (setquotpr r xp1.pr1) xp1.pr2)
               (Obj.magic make_carrier p (setquotpr r xp2.pr1) xp2.pr2)
               (iscompsetquotpr r xp1.pr1 xp2.pr1 rp12)) (setquotpr q a)).pr1.pr2
           (fun x px ->
           internal_paths_rew_r (setquotpr r x)
             (Obj.magic setquotuniv
               (resrel (pr1eqrel r) (funcomp (setquotpr r) p))
               (make_hSet
                 (isasetsubset (fun t -> t.pr1)
                   (Obj.magic setproperty (setquotinset (pr1eqrel r)))
                   (isinclpr1carrier p))) (fun xp ->
               Obj.magic make_carrier p (setquotpr r xp.pr1) xp.pr2)
               (fun xp1 xp2 rp12 ->
               invmaponpathsincl (Obj.magic pr1carrier p)
                 (isinclpr1carrier p)
                 (Obj.magic make_carrier p (setquotpr r xp1.pr1) xp1.pr2)
                 (Obj.magic make_carrier p (setquotpr r xp2.pr1) xp2.pr2)
                 (iscompsetquotpr r xp1.pr1 xp2.pr1 rp12)) (setquotpr q a)).pr1
             (Obj.magic setquotuniv
               (resrel (pr1eqrel r) (funcomp (setquotpr r) p))
               (make_hSet
                 (isasetsubset (fun t -> t.pr1)
                   (Obj.magic setproperty (setquotinset (pr1eqrel r)))
                   (isinclpr1carrier p))) (fun xp ->
               Obj.magic make_carrier p (setquotpr r xp.pr1) xp.pr2)
               (fun xp1 xp2 rp12 ->
               invmaponpathsincl (Obj.magic pr1carrier p)
                 (isinclpr1carrier p)
                 (Obj.magic make_carrier p (setquotpr r xp1.pr1) xp1.pr2)
                 (Obj.magic make_carrier p (setquotpr r xp2.pr1) xp2.pr2)
                 (iscompsetquotpr r xp1.pr1 xp2.pr1 rp12)) (setquotpr q a)).pr2
             (setquotl0 r
               (Obj.magic setquotuniv
                 (resrel (pr1eqrel r) (funcomp (setquotpr r) p))
                 (make_hSet
                   (isasetsubset (fun t -> t.pr1)
                     (Obj.magic setproperty (setquotinset (pr1eqrel r)))
                     (isinclpr1carrier p))) (fun xp ->
                 Obj.magic make_carrier p (setquotpr r xp.pr1) xp.pr2)
                 (fun xp1 xp2 rp12 ->
                 invmaponpathsincl (Obj.magic pr1carrier p)
                   (isinclpr1carrier p)
                   (Obj.magic make_carrier p (setquotpr r xp1.pr1) xp1.pr2)
                   (Obj.magic make_carrier p (setquotpr r xp2.pr1) xp2.pr2)
                   (iscompsetquotpr r xp1.pr1 xp2.pr1 rp12)) (setquotpr q a)).pr1
               (make_carrier
                 (Obj.magic setquotuniv
                   (resrel (pr1eqrel r) (funcomp (setquotpr r) p))
                   (make_hSet
                     (isasetsubset (fun t -> t.pr1)
                       (Obj.magic setproperty (setquotinset (pr1eqrel r)))
                       (isinclpr1carrier p))) (fun xp ->
                   Obj.magic make_carrier p (setquotpr r xp.pr1) xp.pr2)
                   (fun xp1 xp2 rp12 ->
                   invmaponpathsincl (Obj.magic pr1carrier p)
                     (isinclpr1carrier p)
                     (Obj.magic make_carrier p (setquotpr r xp1.pr1) xp1.pr2)
                     (Obj.magic make_carrier p (setquotpr r xp2.pr1) xp2.pr2)
                     (iscompsetquotpr r xp1.pr1 xp2.pr1 rp12))
                   (setquotpr q a)).pr1.pr1 x px)))) } (setquotpr q a)
         Coq_paths_refl)
   in
   isweq_iso f g egf (Obj.magic efg)) }

(** val pathshrel : 'a1 -> 'a1 -> hProp **)

let pathshrel _ _ =
  ishinh

(** val istranspathshrel : 'a1 istrans **)

let istranspathshrel x x' x'' a b =
  hinhfun2 (fun e1 e2 -> pathscomp0 x x' x'' e1 e2) a b

(** val isreflpathshrel : 'a1 isrefl **)

let isreflpathshrel _ =
  hinhpr Coq_paths_refl

(** val issymmpathshrel : 'a1 issymm **)

let issymmpathshrel x x' a =
  hinhfun (fun e -> pathsinv0 x x' e) a

(** val pathseqrel : 'a1 eqrel **)

let pathseqrel =
  eqrelconstr pathshrel istranspathshrel isreflpathshrel issymmpathshrel

type 'x pi0 = 'x setquot

(** val pi0pr : 'a1 -> 'a1 setquot **)

let pi0pr x =
  setquotpr pathseqrel x

type ('x, 's) compfun = ('x -> 's, ('x, 's) iscomprelfun) total2

(** val make_compfun :
    'a1 hrel -> ('a1 -> 'a2) -> ('a1, 'a2) iscomprelfun -> ('a1, 'a2) compfun **)

let make_compfun _ f is =
  { pr1 = f; pr2 = is }

(** val pr1compfun : 'a1 hrel -> ('a1, 'a2) compfun -> 'a1 -> 'a2 **)

let pr1compfun _ t =
  t.pr1

(** val compevmapset :
    'a1 hrel -> 'a1 -> hSet -> ('a1, pr1hSet) compfun -> pr1hSet **)

let compevmapset _ x _ f =
  f.pr1 x

(** val compfuncomp :
    'a1 hrel -> ('a1, 'a2) compfun -> ('a2 -> 'a3) -> ('a1, 'a3) compfun **)

let compfuncomp r f g =
  { pr1 = (funcomp (pr1compfun r f) g); pr2 = (fun x x' r0 ->
    maponpaths g (f.pr1 x) (f.pr1 x') (f.pr2 x x' r0)) }

type 'x setquot2 = ('x, hSet -> ('x, pr1hSet) compfun -> pr1hSet) image

(** val isasetsetquot2 : 'a1 hrel -> 'a1 setquot2 isaset **)

let isasetsetquot2 r =
  let is1 = impred (S (S O)) (fun t -> impred (S (S O)) (fun _ -> t.pr2)) in
  isasetsubset (pr1image (compevmapset r)) (Obj.magic is1)
    (isinclpr1image (compevmapset r))

(** val setquot2inset : 'a1 hrel -> hSet **)

let setquot2inset r =
  make_hSet (isasetsetquot2 r)

(** val setquot2pr : 'a1 hrel -> 'a1 -> 'a1 setquot2 **)

let setquot2pr r x =
  make_image (compevmapset r) (compevmapset r x)
    (hinhpr
      (make_hfiber (compevmapset r) (compevmapset r x) x Coq_paths_refl))

(** val issurjsetquot2pr : 'a1 hrel -> ('a1, 'a1 setquot2) issurjective **)

let issurjsetquot2pr r =
  issurjprtoimage (compevmapset r)

(** val iscompsetquot2pr : 'a1 hrel -> ('a1, 'a1 setquot2) iscomprelfun **)

let iscompsetquot2pr r x x' r0 =
  let e1 =
    funextsec (Obj.magic compevmapset r x) (Obj.magic compevmapset r x')
      (fun s ->
      Obj.magic funextsec (compevmapset r x (Obj.magic s))
        (compevmapset r x' (Obj.magic s)) (fun f -> (Obj.magic f).pr2 x x' r0))
  in
  invmaponpathsincl (Obj.magic pr1image (compevmapset r))
    (isinclpr1image (Obj.magic compevmapset r)) (setquot2pr r x)
    (setquot2pr r x') e1

(** val setquot2univ :
    'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun ->
    'a1 setquot2 -> pr1hSet **)

let setquot2univ r y f is c =
  c.pr1 y (make_compfun r f is)

(** val setquot2univcomm :
    'a1 hrel -> hSet -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun ->
    'a1 -> pr1hSet paths **)

let setquot2univcomm _ _ _ _ _ =
  Coq_paths_refl

(** val weqpathssetquot2l1 : 'a1 eqrel -> 'a1 -> ('a1, hProp) iscomprelfun **)

let weqpathssetquot2l1 r x x' x'' r0 =
  hPropUnivalence (pr1eqrel r x x') (pr1eqrel r x x'') (fun r' ->
    eqreltrans r x x' x'' r' r0) (fun r'' ->
    eqreltrans r x x'' x' r'' (eqrelsymm r x' x'' r0))

(** val weqpathsinsetquot2 :
    'a1 eqrel -> 'a1 -> 'a1 -> (hProptoType, 'a1 setquot2 paths) weq **)

let weqpathsinsetquot2 r x x' =
  weqimplimpl (iscompsetquot2pr (pr1eqrel r) x x') (fun _ -> eqrelrefl r x)
    (pr1eqrel r x x').pr2
    (isasetsetquot2 (pr1eqrel r) (setquot2pr (pr1eqrel r) x)
      (setquot2pr (pr1eqrel r) x'))

(** val setquottosetquot2 :
    'a1 hrel -> 'a1 iseqrel -> 'a1 setquot -> 'a1 setquot2 **)

let setquottosetquot2 r _ x0 =
  Obj.magic setquotuniv r (make_hSet (isasetsetquot2 r)) (setquot2pr r)
    (iscompsetquot2pr r) x0

(** val hSet_univalence_map : hSet -> hSet -> hSet paths -> (__, __) weq **)

let hSet_univalence_map x y e =
  eqweqmap (maponpaths (Obj.magic __) x y e)

(** val hSet_univalence :
    hSet -> hSet -> (hSet paths, (pr1hSet, pr1hSet) weq) weq **)

let hSet_univalence x y =
  let f = hSet_univalence_map x y in
  { pr1 = f; pr2 =
  (let h = fun e -> maponpaths (Obj.magic __) x y e in
   twooutof3c h eqweqmap
     (isweqonpathsincl (Obj.magic __) (isinclpr1 (fun _ -> isapropisaset)) x
       y) univalenceAxiom) }

(** val hSet_rect :
    hSet -> hSet -> (hSet paths -> 'a1) -> (pr1hSet, pr1hSet) weq -> 'a1 **)

let hSet_rect x y ih f =
  let p = ih (invmap (hSet_univalence x y) f) in
  let h = homotweqinvweq (hSet_univalence x y) f in
  transportf (pr1weq (hSet_univalence x y) (invmap (hSet_univalence x y) f))
    f h p

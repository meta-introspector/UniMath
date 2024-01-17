open PartA
open PartB
open Preamble

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val eqweqmap : coq_UU paths -> ('a1, 'a2) weq **)

let eqweqmap _ =
  Obj.magic idweq

(** val sectohfiber :
    ('a1 -> 'a2) -> ('a1 -> ('a1, 'a2) total2, 'a1 -> 'a1) hfiber **)

let sectohfiber a =
  { pr1 = (fun x -> { pr1 = x; pr2 = (a x) }); pr2 = Coq_paths_refl }

(** val hfibertosec :
    ('a1 -> ('a1, 'a2) total2, 'a1 -> 'a1) hfiber -> 'a1 -> 'a2 **)

let hfibertosec se x =
  let s = se.pr1 in
  let e = se.pr2 in
  transportf (s x).pr1 x
    (toforallpaths (fun x0 -> (s x0).pr1) (fun x0 -> x0) e x) (s x).pr2

(** val sectohfibertosec : ('a1 -> 'a2) -> ('a1 -> 'a2) paths **)

let sectohfibertosec _ =
  Coq_paths_refl

(** val isweqtransportf10 : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq **)

let isweqtransportf10 _ _ _ =
  idisweq

(** val isweqtransportb10 : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq **)

let isweqtransportb10 x x' e =
  isweqtransportf10 x' x (pathsinv0 x x' e)

(** val l1 :
    coq_UU paths -> 'a3 -> (__ -> __ -> (__, __) weq -> 'a3 -> 'a3) -> (__ ->
    'a3 -> 'a3 paths) -> 'a3 paths **)

let l1 _ pp' _ r =
  r __ (transportb __ __ Coq_paths_refl pp')

type univalenceStatement = __ -> __ -> (coq_UU paths, (__, __) weq) isweq

type funextemptyStatement =
  __ -> (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths

type propositionalUnivalenceStatement =
  __ -> __ -> __ isaprop -> __ isaprop -> (__ -> __) -> (__ -> __) -> coq_UU
  paths

type funcontrStatement = __ -> __ -> (__ -> __ iscontr) -> (__ -> __) iscontr

type funextcontrStatement =
  __ -> __ -> (__ -> __) -> (__ -> __, __ -> __ paths) total2 iscontr

type isweqtoforallpathsStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot)
  isweq

type funextsecStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths

type funextfunStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths

type weqtopathsStatement = __ -> __ -> (__, __) weq -> coq_UU paths

type weqpathsweqStatement = __ -> __ -> (__, __) weq -> (__, __) weq paths

type weqtoforallpathsStatement =
  __ -> __ -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot)
  weq

(** val funextsecImplication :
    isweqtoforallpathsStatement -> (__ -> __) -> (__ -> __) -> (__, __) homot
    -> (__ -> __) paths **)

let funextsecImplication fe f g =
  invmap (make_weq (toforallpaths f g) (fe __ __ f g))

(** val funextfunImplication :
    funextsecStatement -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__
    -> __) paths **)

let funextfunImplication fe =
  fe __ __

(** val univfromtwoaxioms :
    ((weqtopathsStatement, weqpathsweqStatement) total2, univalenceStatement)
    logeq **)
let totalfun f z =
  { pr1 = z.pr1; pr2 = (f z.pr1 z.pr2) }

let univfromtwoaxioms =
  { pr1 = (fun x ->
    let weqtopaths0 = x.pr1 in
    let weqpathsweq0 = x.pr2 in
    (fun _ _ ->
    let f = totalfun (fun _ -> eqweqmap) in
    let g = totalfun (fun _ -> weqtopaths0 __ __) in
    let efg = fun z2 ->
      let xY = z2.pr1 in
      let e = z2.pr2 in
      maponpaths (fun w -> { pr1 = xY; pr2 = w })
        (eqweqmap (weqtopaths0 __ __ e)) e (weqpathsweq0 __ __ e)
    in
    let egf0 = fun _ -> Coq_paths_refl in
    let egf1 = fun a1 a1' x0 ->
      let x' = maponpaths (Obj.magic __) a1'.pr1 a1.pr1 x0 in
      invmaponpathsweq (make_weq (Obj.magic __) isweqpr1pr1) a1' a1 x'
    in
    let egf = fun a1 -> egf1 a1 (g (f a1)) (egf0 a1) in
    let is2 = isweq_iso f g egf efg in
    isweqtotaltofib (fun _ -> eqweqmap) is2 (make_dirprod __ __))); pr2 =
    (fun ua -> { pr1 = (fun _ _ -> invmap (make_weq eqweqmap (ua __ __)));
    pr2 = (fun _ _ -> homotweqinvweq (make_weq eqweqmap (ua __ __))) }) }

(** val univalenceUAH :
    univalenceStatement -> (coq_UU paths, ('a1, 'a2) weq) weq **)

let univalenceUAH univalenceAxiom0 =
  make_weq eqweqmap (Obj.magic univalenceAxiom0 __ __)

(** val weqtopathsUAH :
    univalenceStatement -> (__, __) weq -> coq_UU paths **)

let weqtopathsUAH univalenceAxiom0 =
  invmap (univalenceUAH univalenceAxiom0)

(** val weqpathsweqUAH :
    univalenceStatement -> (__, __) weq -> (__, __) weq paths **)

let weqpathsweqUAH univalenceAxiom0 w =
  homotweqinvweq (univalenceUAH univalenceAxiom0) w

(** val propositionalUnivalenceUAH :
    univalenceStatement -> __ isaprop -> __ isaprop -> (__ -> __) -> (__ ->
    __) -> coq_UU paths **)

let propositionalUnivalenceUAH univalenceAxiom0 i j f g =
  weqtopathsUAH univalenceAxiom0
    (make_weq f
      (isweq_iso f g (fun p -> proofirrelevance i (g (f p)) p) (fun q ->
        proofirrelevance j (f (g q)) q)))

(** val weqtransportbUAH :
    univalenceStatement -> (__ -> __ -> (__, __) weq -> 'a1 -> 'a1) -> (__ ->
    'a1 -> 'a1 paths) -> ('a2, 'a3) weq -> 'a1 -> 'a1 paths **)

let weqtransportbUAH univalenceAxiom0 r r0 w p' =
  let uv = weqtopathsUAH univalenceAxiom0 (Obj.magic w) in l1 uv p' r r0

(** val isweqweqtransportbUAH :
    univalenceStatement -> (__ -> __ -> (__, __) weq -> 'a1 -> 'a1) -> (__ ->
    'a1 -> 'a1 paths) -> ('a2, 'a3) weq -> ('a1, 'a1) isweq **)

let isweqweqtransportbUAH univalenceAxiom0 r r0 w =
  let e = weqtransportbUAH univalenceAxiom0 r r0 w in
  let ee = fun p' ->
    pathsinv0 (Obj.magic r __ __ w p')
      (transportb __ __ (weqtopathsUAH univalenceAxiom0 (Obj.magic w)) p')
      (e p')
  in
  let is1 =
    isweqtransportb10 __ __ (weqtopathsUAH univalenceAxiom0 (Obj.magic w))
  in
  isweqhomot
    (transportb __ __ (weqtopathsUAH univalenceAxiom0 (Obj.magic w)))
    (Obj.magic r __ __ w) ee is1

(** val isweqcompwithweqUAH :
    univalenceStatement -> ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) isweq **)

let isweqcompwithweqUAH univalenceAxiom0 w =
  let r = fun w1 f x -> f (w1 x) in
  Obj.magic isweqweqtransportbUAH univalenceAxiom0 (fun _ _ w1 ->
    Obj.magic r (pr1weq w1)) (fun _ _ -> Coq_paths_refl) w

(** val eqcor0UAH :
    univalenceStatement -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2 -> 'a3) ->
    ('a1 -> 'a3) paths -> ('a2 -> 'a3) paths **)

let eqcor0UAH univalenceAxiom0 w f1 f2 =
  invmaponpathsweq
    (make_weq (fun f x -> f (pr1weq w x))
      (isweqcompwithweqUAH univalenceAxiom0 w)) f1 f2

(** val apathpr1toprUAH :
    univalenceStatement -> ('a1 pathsspace -> 'a1) paths **)

let apathpr1toprUAH univalenceAxiom0 =
  eqcor0UAH univalenceAxiom0 (make_weq deltap isweqdeltap) (fun z -> z.pr1)
    (fun z -> z.pr2.pr1) Coq_paths_refl

(** val funextfunPreliminaryUAH :
    univalenceStatement -> (__ -> __) -> (__ -> __) -> (__, __) homot -> (__
    -> __) paths **)

let funextfunPreliminaryUAH univalenceAxiom0 f1 f2 e =
  let f = fun x -> pathsspacetriple (f1 x) (f2 x) (e x) in
  let g1 = fun z -> z.pr1 in
  let g2 = fun z -> z.pr2.pr1 in
  maponpaths (funcomp f) g1 g2 (apathpr1toprUAH univalenceAxiom0)

(** val funextemptyUAH :
    univalenceStatement -> (__ -> empty) -> (__ -> empty) -> (__ -> empty)
    paths **)

let funextemptyUAH univalenceAxiom0 f g =
  Obj.magic funextfunPreliminaryUAH univalenceAxiom0 f g (fun _ ->
    assert false (* absurd case *))

(** val isweqlcompwithweqUAH :
    univalenceStatement -> ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) isweq **)

let isweqlcompwithweqUAH univalenceAxiom0 w =
  isweq_iso (fun a x -> a (pr1weq w x)) (fun b x' ->
    b (pr1weq (invweq w) x')) (fun a ->
    Obj.magic funextfunPreliminaryUAH univalenceAxiom0 (fun x' ->
      Obj.magic a (pr1weq w (invmap (Obj.magic w) x'))) a (fun x' ->
      maponpaths (Obj.magic a)
        (pr1weq (Obj.magic w) (invmap (Obj.magic w) x')) x'
        (homotweqinvweq (Obj.magic w) x'))) (fun a ->
    Obj.magic funextfunPreliminaryUAH univalenceAxiom0 (fun x ->
      Obj.magic a (invmap w (pr1weq (Obj.magic w) x))) a (fun x ->
      maponpaths (Obj.magic a)
        (invmap (Obj.magic w) (pr1weq (Obj.magic w) x)) x
        (homotinvweqweq (Obj.magic w) x)))

(** val isweqrcompwithweqUAH :
    univalenceStatement -> ('a1, 'a2) weq -> ('a3 -> 'a1, 'a3 -> 'a2) isweq **)

let isweqrcompwithweqUAH univalenceAxiom0 w =
  isweq_iso (fun a x -> pr1weq w (a x)) (fun a' x ->
    pr1weq (invweq w) (a' x)) (fun a ->
    Obj.magic funextfunPreliminaryUAH univalenceAxiom0 (fun x ->
      invmap (Obj.magic w) (pr1weq w (Obj.magic a x))) a (fun x ->
      homotinvweqweq (Obj.magic w) (Obj.magic a x))) (fun a' ->
    Obj.magic funextfunPreliminaryUAH univalenceAxiom0 (fun x ->
      pr1weq (Obj.magic w) (invmap w (Obj.magic a' x))) a' (fun x ->
      homotweqinvweq (Obj.magic w) (Obj.magic a' x)))

(** val funcontrUAH :
    univalenceStatement -> (__ -> __ iscontr) -> (__ -> __) iscontr **)

let funcontrUAH univalenceAxiom0 x0 =
  let is1 = isweqpr1 x0 in
  let w1 = make_weq (fun t -> t.pr1) is1 in
  let x1 = isweqrcompwithweqUAH univalenceAxiom0 w1 (fun x -> x) in
  iscontrretract hfibertosec sectohfiber sectohfibertosec x1

(** val funextcontrUAH :
    univalenceStatement -> (__ -> __) -> (__ -> __, __ -> __ paths) total2
    iscontr **)

let funextcontrUAH univalenceAxiom0 g =
  iscontrretract (fun x -> { pr1 = (fun t -> (Obj.magic x t).pr1); pr2 =
    (fun t -> (Obj.magic x t).pr2) }) (fun y t ->
    Obj.magic { pr1 = (y.pr1 t); pr2 = (y.pr2 t) }) (fun _ -> Coq_paths_refl)
    (funcontrUAH univalenceAxiom0 (fun t ->
      Obj.magic iscontrcoconustot (g t)))

(** val isweqtoforallpathsUAH :
    univalenceStatement -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths,
    (__, __) homot) isweq **)

let isweqtoforallpathsUAH univalenceAxiom0 f g =
  isweqtotaltofib (fun h -> toforallpaths h g)
    (isweqcontrcontr (fun ff -> { pr1 = ff.pr1; pr2 =
      (toforallpaths ff.pr1 g ff.pr2) }) (iscontrcoconustot g)
      (funextcontrUAH univalenceAxiom0 g)) f

(** val funcontrFromUnivalence :
    univalenceStatement -> (__ -> __ iscontr) -> (__ -> __) iscontr **)

let funcontrFromUnivalence =
  funcontrUAH

(** val funextsecweqFromUnivalence :
    univalenceStatement -> (__ -> __) -> (__ -> __) -> ((__ -> __) paths,
    (__, __) homot) isweq **)

let funextsecweqFromUnivalence =
  isweqtoforallpathsUAH

(** val funextemptyFromUnivalence :
    univalenceStatement -> (__ -> empty) -> (__ -> empty) -> (__ -> empty)
    paths **)

let funextemptyFromUnivalence =
  funextemptyUAH

(** val propositionalUnivalenceFromUnivalence :
    univalenceStatement -> __ isaprop -> __ isaprop -> (__ -> __) -> (__ ->
    __) -> coq_UU paths **)

let propositionalUnivalenceFromUnivalence =
  propositionalUnivalenceUAH

(** val funextcontrStatementFromUnivalence :
    univalenceStatement -> (__ -> __) -> (__ -> __, __ -> __ paths) total2
    iscontr **)

let funextcontrStatementFromUnivalence =
  funextcontrUAH

(** val univalenceAxiom : (coq_UU paths, (__, __) weq) isweq **)

let univalenceAxiom =
  failwith "AXIOM TO BE REALIZED"

(** val funextemptyAxiom :
    (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths **)

let funextemptyAxiom =
  failwith "AXIOM TO BE REALIZED"

(** val isweqtoforallpathsAxiom :
    (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) isweq **)

let isweqtoforallpathsAxiom =
  failwith "AXIOM TO BE REALIZED"

(** val funcontrAxiom : (__ -> __ iscontr) -> (__ -> __) iscontr **)

let funcontrAxiom =
  failwith "AXIOM TO BE REALIZED"

(** val propositionalUnivalenceAxiom :
    __ isaprop -> __ isaprop -> (__ -> __) -> (__ -> __) -> coq_UU paths **)

let propositionalUnivalenceAxiom =
  failwith "AXIOM TO BE REALIZED"

(** val funextcontrAxiom :
    (__ -> __) -> (__ -> __, __ -> __ paths) total2 iscontr **)

let funextcontrAxiom =
  failwith "AXIOM TO BE REALIZED"

(** val funextempty :
    (__ -> empty) -> (__ -> empty) -> (__ -> empty) paths **)

let funextempty =
  funextemptyAxiom

(** val univalence : (coq_UU paths, ('a1, 'a2) weq) weq **)

let univalence : (coq_UU paths, ('a1, 'a2) weq) weq =
  univalenceUAH (fun _ _ -> univalenceAxiom)

(** val weqtopaths : (__, __) weq -> coq_UU paths **)

let weqtopaths =
  invmap univalence

(** val weqpathsweq : (__, __) weq -> (__, __) weq paths **)

let weqpathsweq w =
  weqpathsweqUAH (fun _ _ -> univalenceAxiom) w

(** val funcontr : (__ -> __ iscontr) -> (__ -> __) iscontr **)

let funcontr =
  funcontrAxiom

(** val funextcontr :
    (__ -> __) -> (__ -> __, __ -> __ paths) total2 iscontr **)

let funextcontr =
  funextcontrAxiom

(** val isweqtoforallpaths :
    (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) isweq **)

let isweqtoforallpaths =
  isweqtoforallpathsAxiom

(** val weqtoforallpaths :
    (__ -> __) -> (__ -> __) -> ((__ -> __) paths, (__, __) homot) weq **)

let weqtoforallpaths f g =
  make_weq (toforallpaths f g) (isweqtoforallpaths f g)

(** val funextsec :
    (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths **)

let funextsec f g x =
  funextsecImplication (fun _ _ -> isweqtoforallpathsAxiom) f g x

(** val funextfun :
    (__ -> __) -> (__ -> __) -> (__, __) homot -> (__ -> __) paths **)

let funextfun f g x =
  funextfunImplication (fun _ _ -> funextsec) f g x

(** val weqfunextsec :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> (('a1, 'a2) homot, ('a1 -> 'a2) paths) weq **)

let weqfunextsec f g =
  invweq (Obj.magic weqtoforallpaths f g)

(** val funcontrtwice :
    ('a1 -> 'a1 -> 'a2 iscontr) -> ('a1 -> 'a1 -> 'a2) iscontr **)

let funcontrtwice is =
  let is1 = fun x -> funcontr (Obj.magic is x) in Obj.magic funcontr is1

(** val toforallpaths_induction :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> (('a1 -> 'a2) paths -> 'a3) -> ('a1 ->
    'a2 paths) -> 'a3 **)

let toforallpaths_induction f g h i =
  internal_paths_rew
    (pr1weq (Obj.magic weqtoforallpaths f g)
      (invmap (Obj.magic weqtoforallpaths f g) i))
    (Obj.magic h (invmap (Obj.magic weqtoforallpaths f g) i)) i
    (homotweqinvweq (Obj.magic weqtoforallpaths f g) i)

(** val transportf_funextfun :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> 'a1 -> 'a3 -> 'a3
    paths **)

let transportf_funextfun f f' h x f0 =
  toforallpaths_induction f f' (fun e ->
    let xR = homotinvweqweq (Obj.magic weqtoforallpaths f f') e in
    let h0 =
      funextsec (Obj.magic f) (Obj.magic f') (fun x0 ->
        toforallpaths (Obj.magic f) (Obj.magic f') (Obj.magic e) x0)
    in
    pathscomp0 (transportf (Obj.magic f) (Obj.magic f') h0 f0)
      (transportf f f' e f0)
      (transportf (f x) (f' x) (toforallpaths f f' e x) f0)
      (transportf_paths f f' (Obj.magic h0) e xR f0) Coq_paths_refl) h

(** val coq_UU_rect : (coq_UU paths -> 'a3) -> ('a1, 'a2) weq -> 'a3 **)

let coq_UU_rect ih f =
  let p = ih (invmap univalence f) in
  let h = homotweqinvweq univalence f in
  transportf (pr1weq univalence (invmap univalence f)) f h p

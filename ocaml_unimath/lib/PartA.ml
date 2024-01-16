open Preamble

type __ = Obj.t

(** val fromempty : empty -> 'a1 **)

let fromempty _ =
  assert false (* absurd case *)

(** val idfun : 'a1 -> 'a1 **)

let idfun t =
  t

(** val funcomp : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3 **)

let funcomp f g x =
  g (f x)

type 'x neg = 'x -> empty

(** val pathscomp0 :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths **)

let pathscomp0 _ _ _ _ e2 =
  e2

(** val pathscomp0rid : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths **)

let pathscomp0rid _ _ _ =
  Coq_paths_refl

(** val pathsinv0 : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths **)

let pathsinv0 _ _ _ =
  Coq_paths_refl

(** val pathsinv0l : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths **)

let pathsinv0l _ _ _ =
  Coq_paths_refl

(** val maponpaths : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths **)

let maponpaths _ _ _ _ =
  Coq_paths_refl

(** val maponpathscomp :
    'a1 -> 'a1 -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 paths -> 'a3 paths paths **)

let maponpathscomp _ _ _ _ _ =
  Coq_paths_refl

type ('x, 'p) homot = 'x -> 'p paths

(** val pathssec1 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a2 -> 'a2
    paths -> 'a1 paths **)

let pathssec1 s p eps x y e =
  pathscomp0 x (p (s x)) (p y) (pathsinv0 (p (s x)) x (eps x))
    (maponpaths p (s x) y e)

(** val pathssec2 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a2
    paths -> 'a1 paths **)

let pathssec2 s p eps x x' e =
  let e' = pathssec1 s p eps x (s x') e in
  pathscomp0 x (p (s x')) x' e' (eps x')

(** val pathssec2id :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 paths
    paths **)

let pathssec2id _ _ _ _ =
  Coq_paths_refl

(** val pathssec3 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1
    paths -> 'a1 paths paths **)

let pathssec3 s p eps x _ _ =
  pathssec2id s p eps x

(** val constr1 :
    'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a2, ('a2 -> ('a1, 'a2) total2 paths,
    'a2 -> 'a1 paths paths) total2) total2 **)

let constr1 _ _ _ =
  { pr1 = idfun; pr2 = { pr1 = (fun _ -> Coq_paths_refl); pr2 = (fun _ ->
    Coq_paths_refl) } }

(** val transportf : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 **)

let transportf x x' e =
  (constr1 x x' e).pr1

(** val transportb : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 **)

let transportb x x' e =
  transportf x' x (pathsinv0 x x' e)

(** val two_arg_paths_f :
    ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
    -> 'a3 paths **)

let two_arg_paths_f _ _ _ _ _ _ _ =
  Coq_paths_refl

type 't iscontr = ('t, 't -> 't paths) total2

(** val iscontrpr1 : 'a1 iscontr -> 'a1 **)

let iscontrpr1 x =
  x.pr1

(** val iscontrretract :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 iscontr -> 'a2
    iscontr **)

let iscontrretract p s eps is =
  let x = iscontrpr1 is in
  let fe = is.pr2 in
  { pr1 = (p x); pr2 = (fun t ->
  pathscomp0 t (p (s t)) (p is.pr1) (pathsinv0 (p (s t)) t (eps t))
    (maponpaths p (s t) is.pr1 (fe (s t)))) }

(** val proofirrelevancecontr : 'a1 iscontr -> 'a1 -> 'a1 -> 'a1 paths **)

let proofirrelevancecontr is x x' =
  pathscomp0 x is.pr1 x' (is.pr2 x) (pathsinv0 x' is.pr1 (is.pr2 x'))

type ('x, 'y) hfiber = ('x, 'y paths) total2

(** val make_hfiber :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> 'a2 paths -> ('a1, 'a2) hfiber **)

let make_hfiber _ _ x e =
  { pr1 = x; pr2 = e }

(** val hfiberpr1 : ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> 'a1 **)

let hfiberpr1 _ _ t =
  t.pr1

(** val hfibershomotftog :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber -> ('a1, 'a2) hfiber **)

let hfibershomotftog f g h y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in
  { pr1 = x; pr2 =
  (pathscomp0 (g x) (f x) y (pathsinv0 (f x) (g x) (h x)) e) }

(** val hfibershomotgtof :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber -> ('a1, 'a2) hfiber **)

let hfibershomotgtof f g h y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in { pr1 = x; pr2 = (pathscomp0 (f x) (g x) y (h x) e) }

(** val hfibertriangle1 :
    ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> ('a1,
    'a2) hfiber paths -> 'a2 paths paths **)

let hfibertriangle1 _ _ _ _ _ =
  Coq_paths_refl

(** val hfibertriangle1inv0 :
    ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> ('a1,
    'a2) hfiber paths -> 'a2 paths paths **)

let hfibertriangle1inv0 _ _ _ _ _ =
  Coq_paths_refl

(** val hfibertriangle2 :
    ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> 'a1
    paths -> 'a2 paths paths -> ('a1, 'a2) hfiber paths **)

let hfibertriangle2 f y xe1 xe2 _ eee =
  let t = xe1.pr1 in
  let e1 = xe1.pr2 in
  let e2 = xe2.pr2 in maponpaths (fun e -> make_hfiber f y t e) e1 e2 eee

type 't coconusfromt = ('t, 't paths) total2

(** val coconusfromtpair : 'a1 -> 'a1 -> 'a1 paths -> 'a1 coconusfromt **)

let coconusfromtpair _ t' e =
  { pr1 = t'; pr2 = e }

type 't coconustot = ('t, 't paths) total2

(** val coconustotpair : 'a1 -> 'a1 -> 'a1 paths -> 'a1 coconustot **)

let coconustotpair _ t' e =
  { pr1 = t'; pr2 = e }

(** val coconustot_isProofIrrelevant :
    'a1 -> 'a1 coconustot -> 'a1 coconustot -> 'a1 coconustot paths **)

let coconustot_isProofIrrelevant _ _ _ =
  Coq_paths_refl

(** val iscontrcoconusfromt : 'a1 -> 'a1 coconusfromt iscontr **)

let iscontrcoconusfromt t =
  { pr1 = { pr1 = t; pr2 = Coq_paths_refl }; pr2 = (fun _ -> Coq_paths_refl) }

type ('x, 'y) isweq = 'y -> ('x, 'y) hfiber iscontr

(** val idisweq : ('a1, 'a1) isweq **)

let idisweq y =
  { pr1 = (make_hfiber idfun y y Coq_paths_refl); pr2 = (fun _ ->
    Coq_paths_refl) }

type ('x, 'y) weq = ('x -> 'y, ('x, 'y) isweq) total2

(** val pr1weq : ('a1, 'a2) weq -> 'a1 -> 'a2 **)

let pr1weq x =
  x.pr1

(** val weqproperty : ('a1, 'a2) weq -> ('a1, 'a2) isweq **)

let weqproperty f =
  f.pr2

(** val weqccontrhfiber : ('a1, 'a2) weq -> 'a2 -> ('a1, 'a2) hfiber **)

let weqccontrhfiber w y =
  iscontrpr1 (weqproperty w y)

(** val weqccontrhfiber2 :
    ('a1, 'a2) weq -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber paths **)

let weqccontrhfiber2 w y x =
  (w.pr2 y).pr2 x

(** val make_weq : ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) weq **)

let make_weq f is =
  { pr1 = f; pr2 = is }

(** val invmap : ('a1, 'a2) weq -> 'a2 -> 'a1 **)

let invmap w y =
  hfiberpr1 (pr1weq w) y (weqccontrhfiber w y)

(** val homotweqinvweq : ('a1, 'a2) weq -> 'a2 -> 'a2 paths **)

let homotweqinvweq w y =
  (weqccontrhfiber w y).pr2

(** val homotinvweqweq0 : ('a1, 'a2) weq -> 'a1 -> 'a1 paths **)

let homotinvweqweq0 w x =
  let xe2 = make_hfiber (pr1weq w) (pr1weq w x) x Coq_paths_refl in
  let p = weqccontrhfiber2 w (pr1weq w x) xe2 in
  maponpaths (fun t -> t.pr1) xe2 (weqccontrhfiber w (pr1weq w x)) p

(** val homotinvweqweq : ('a1, 'a2) weq -> 'a1 -> 'a1 paths **)

let homotinvweqweq w x =
  pathsinv0 x (invmap w (pr1weq w x)) (homotinvweqweq0 w x)

(** val invmaponpathsweq :
    ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 paths -> 'a1 paths **)

let invmaponpathsweq w x x' =
  pathssec2 (pr1weq w) (invmap w) (homotinvweqweq w) x x'

(** val diaglemma2 :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths
    -> 'a2 paths paths **)

let diaglemma2 _ _ _ _ _ ee =
  ee

(** val homotweqinvweqweq : ('a1, 'a2) weq -> 'a1 -> 'a2 paths paths **)

let homotweqinvweqweq w x =
  let hfid = make_hfiber (pr1weq w) (pr1weq w x) x Coq_paths_refl in
  let hfcc = weqccontrhfiber w (pr1weq w x) in
  diaglemma2 (pr1weq w) x (invmap w (pr1weq w x))
    (maponpaths (fun t -> t.pr1) hfid hfcc
      (weqccontrhfiber2 w (pr1weq w x) hfid))
    (weqccontrhfiber w (pr1weq w x)).pr2
    (hfibertriangle1 (pr1weq w) (pr1weq w x) hfid hfcc
      (weqccontrhfiber2 w (pr1weq w x) hfid))

(** val iscontrweqb : ('a1, 'a2) weq -> 'a2 iscontr -> 'a1 iscontr **)

let iscontrweqb w is =
  iscontrretract (invmap w) (pr1weq w) (homotinvweqweq w) is

(** val isProofIrrelevantUnit : coq_unit -> coq_unit -> coq_unit paths **)

let isProofIrrelevantUnit _ _ =
  Coq_paths_refl

(** val unitl0 : coq_unit paths -> coq_unit coconustot **)

let unitl0 e =
  coconustotpair Coq_tt Coq_tt e

(** val unitl1 : coq_unit coconustot -> coq_unit paths **)

let unitl1 cp =
  cp.pr2

(** val unitl2 : coq_unit paths -> coq_unit paths paths **)

let unitl2 _ =
  Coq_paths_refl

(** val unitl3 : coq_unit paths -> coq_unit paths paths **)

let unitl3 e =
  let e0 =
    coconustot_isProofIrrelevant Coq_tt (unitl0 Coq_paths_refl) (unitl0 e)
  in
  let e1 = maponpaths unitl1 (unitl0 Coq_paths_refl) (unitl0 e) e0 in
  pathscomp0 e (unitl1 (unitl0 e)) Coq_paths_refl
    (pathsinv0 (unitl1 (unitl0 e)) e (unitl2 e))
    (pathscomp0 (unitl1 (unitl0 e)) (unitl1 (unitl0 Coq_paths_refl))
      Coq_paths_refl
      (pathsinv0 (unitl1 (unitl0 Coq_paths_refl)) (unitl1 (unitl0 e)) e1)
      (unitl2 Coq_paths_refl))

(** val iscontrunit : coq_unit iscontr **)

let iscontrunit =
  { pr1 = Coq_tt; pr2 = (fun t -> isProofIrrelevantUnit t Coq_tt) }

(** val iscontrpathsinunit :
    coq_unit -> coq_unit -> coq_unit paths iscontr **)

let iscontrpathsinunit x x' =
  { pr1 = (isProofIrrelevantUnit x x'); pr2 = unitl3 }

(** val ifcontrthenunitl0 :
    coq_unit paths -> coq_unit paths -> coq_unit paths paths **)

let ifcontrthenunitl0 e1 e2 =
  proofirrelevancecontr (iscontrpathsinunit Coq_tt Coq_tt) e1 e2

(** val isweqcontrtounit : 'a1 iscontr -> ('a1, coq_unit) isweq **)

let isweqcontrtounit is _ =
  let c = is.pr1 in
  let h = is.pr2 in
  let hc = make_hfiber (fun _ -> Coq_tt) Coq_tt c Coq_paths_refl in
  { pr1 = hc; pr2 = (fun ha ->
  let x = ha.pr1 in
  let e = ha.pr2 in
  two_arg_paths_f (fun x0 x1 -> { pr1 = x0; pr2 = x1 }) x e c Coq_paths_refl
    (h x) (ifcontrthenunitl0 (transportf x c (h x) e) Coq_paths_refl)) }

(** val hfibersgftog :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a3) hfiber -> ('a2, 'a3)
    hfiber **)

let hfibersgftog f g z xe =
  make_hfiber g z (f xe.pr1) xe.pr2

(** val constr2 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 -> ('a2, 'a1)
    hfiber -> (('a1, 'a1) hfiber, ('a2, 'a1) hfiber paths) total2 **)

let constr2 f g efg x0 xe =
  let y0 = xe.pr1 in
  let e = xe.pr2 in
  let eint = pathssec1 g f efg y0 x0 e in
  let ee =
    pathscomp0 (g (f x0)) (g y0) x0
      (pathsinv0 (g y0) (g (f x0)) (maponpaths g y0 (f x0) eint)) e
  in
  { pr1 = (make_hfiber (funcomp f g) x0 x0 ee); pr2 =
  (two_arg_paths_f (fun x x1 -> { pr1 = x; pr2 = x1 }) y0 e (f x0) ee eint
    Coq_paths_refl) }

(** val iscontrhfiberl1 :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 -> ('a1, 'a1)
    hfiber iscontr -> ('a2, 'a1) hfiber iscontr **)

let iscontrhfiberl1 f g efg x0 is =
  let f1 = hfibersgftog f g x0 in
  let g1 = fun xe -> (constr2 f g efg x0 xe).pr1 in
  let efg1 = fun xe ->
    pathsinv0 xe (hfibersgftog f g x0 (constr2 f g efg x0 xe).pr1)
      (constr2 f g efg x0 xe).pr2
  in
  iscontrretract f1 g1 efg1 is

(** val homothfiber1 :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber -> ('a1, 'a2) hfiber **)

let homothfiber1 f g h y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in
  make_hfiber g y x (pathscomp0 (g x) (f x) y (pathsinv0 (f x) (g x) (h x)) e)

(** val homothfiber2 :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber -> ('a1, 'a2) hfiber **)

let homothfiber2 f g h y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in make_hfiber f y x (pathscomp0 (f x) (g x) y (h x) e)

(** val homothfiberretr :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber -> ('a1, 'a2) hfiber paths **)

let homothfiberretr f g h y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in
  let xe1 =
    make_hfiber g y x
      (pathscomp0 (g x) (f x) y (pathsinv0 (f x) (g x) (h x))
        (pathscomp0 (f x) (g x) y (h x) e))
  in
  let xe2 = make_hfiber g y x e in
  hfibertriangle2 g y xe1 xe2 Coq_paths_refl Coq_paths_refl

(** val iscontrhfiberl2 :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
    hfiber iscontr -> ('a1, 'a2) hfiber iscontr **)

let iscontrhfiberl2 f g h y is =
  let a = homothfiber1 f g h y in
  let b = homothfiber2 f g h y in
  let eab = homothfiberretr f g h y in iscontrretract a b eab is

(** val isweqhomot :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) isweq ->
    ('a1, 'a2) isweq **)

let isweqhomot f1 f2 h x0 y =
  iscontrhfiberl2 f1 f2 h y (x0 y)

(** val isweq_iso :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a2 -> 'a2 paths)
    -> ('a1, 'a2) isweq **)

let isweq_iso f g egf efg y =
  let x0 =
    let efg' = fun y0 -> pathsinv0 (f (g y0)) y0 (efg y0) in
    iscontrhfiberl2 idfun (funcomp g f) efg' y (idisweq y)
  in
  iscontrhfiberl1 g f egf y x0

(** val isweqinvmap : ('a1, 'a2) weq -> ('a2, 'a1) isweq **)

let isweqinvmap w =
  let efg = homotweqinvweq w in
  let egf = homotinvweqweq w in isweq_iso (invmap w) (pr1weq w) efg egf

(** val invweq : ('a1, 'a2) weq -> ('a2, 'a1) weq **)

let invweq w =
  make_weq (invmap w) (isweqinvmap w)

(** val iscontrweqf : ('a1, 'a2) weq -> 'a1 iscontr -> 'a2 iscontr **)

let iscontrweqf w is =
  iscontrweqb (invweq w) is

(** val weqhfibershomot :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> (('a1, 'a2)
    hfiber, ('a1, 'a2) hfiber) weq **)

let weqhfibershomot f g h y =
  let ff = hfibershomotftog f g h y in
  let gg = hfibershomotgtof f g h y in
  { pr1 = ff; pr2 =
  (let effgg = fun xe ->
     let x = xe.pr1 in
     let e = xe.pr2 in
     let eee = Coq_paths_refl in
     let xe1 =
       make_hfiber g y x
         (pathscomp0 (g x) (f x) y (pathsinv0 (f x) (g x) (h x))
           (pathscomp0 (f x) (g x) y (h x) e))
     in
     let xe2 = make_hfiber g y x e in
     hfibertriangle2 g y xe1 xe2 Coq_paths_refl eee
   in
   let eggff = fun xe ->
     let x = xe.pr1 in
     let e = xe.pr2 in
     let eee = Coq_paths_refl in
     let xe1 =
       make_hfiber f y x
         (pathscomp0 (f x) (g x) y (h x)
           (pathscomp0 (g x) (f x) y (pathsinv0 (f x) (g x) (h x)) e))
     in
     let xe2 = make_hfiber f y x e in
     hfibertriangle2 f y xe1 xe2 Coq_paths_refl eee
   in
   isweq_iso ff gg eggff effgg) }

(** val twooutof3a :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) isweq -> ('a2, 'a3) isweq ->
    ('a1, 'a2) isweq **)

let twooutof3a f g isgf isg =
  let gw = make_weq g isg in
  let gfw = make_weq (funcomp f g) isgf in
  let invgf = invmap gfw in
  let invf = funcomp g invgf in
  let efinvf = fun y ->
    let int1 = homotweqinvweq gfw (g y) in
    invmaponpathsweq gw (f (invf y)) y int1
  in
  let einvff = fun x -> homotinvweqweq gfw x in isweq_iso f invf einvff efinvf

(** val twooutof3c :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a2, 'a3) isweq ->
    ('a1, 'a3) isweq **)

let twooutof3c f g isf isg =
  let wf = make_weq f isf in
  let wg = make_weq g isg in
  let invf = invmap wf in
  let invg = invmap wg in
  let gf = funcomp f g in
  let invgf = funcomp invg invf in
  let egfinvgf = fun x -> homotinvweqweq wf x in
  let einvgfgf = fun z -> homotweqinvweq wg z in
  isweq_iso gf invgf egfinvgf einvgfgf

(** val isweqcontrcontr :
    ('a1 -> 'a2) -> 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) isweq **)

let isweqcontrcontr f isx isy =
  let py = fun _ -> Coq_tt in
  twooutof3a f py (isweqcontrtounit isx) (isweqcontrtounit isy)

(** val weqcomp : ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq **)

let weqcomp w1 w2 =
  make_weq (fun x -> pr1weq w2 (pr1weq w1 x))
    (twooutof3c (pr1weq w1) (pr1weq w2) w1.pr2 w2.pr2)

(** val coprodf :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) coprod -> ('a3, 'a4) coprod **)

let coprodf f g = function
| Coq_ii1 x -> Coq_ii1 (f x)
| Coq_ii2 y -> Coq_ii2 (g y)

type ('p, 'q) equality_cases = __

(** val equality_by_case :
    ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths ->
    ('a1, 'a2) equality_cases **)

let equality_by_case x x' e =
  match x with
  | Coq_ii1 a ->
    (match x' with
     | Coq_ii1 a0 ->
       Obj.magic maponpaths (fun c ->
         match c with
         | Coq_ii1 a1 -> a1
         | Coq_ii2 _ -> a) (Coq_ii1 a) (Coq_ii1 a0) e
     | Coq_ii2 b -> transportf (Coq_ii1 a) (Coq_ii2 b) e (Obj.magic Coq_tt))
  | Coq_ii2 b ->
    (match x' with
     | Coq_ii1 a -> transportb (Coq_ii2 b) (Coq_ii1 a) e (Obj.magic Coq_tt)
     | Coq_ii2 b0 ->
       Obj.magic maponpaths (fun c ->
         match c with
         | Coq_ii1 _ -> b
         | Coq_ii2 b1 -> b1) (Coq_ii2 b) (Coq_ii2 b0) e)

(** val ii1_injectivity :
    'a1 -> 'a1 -> ('a1, 'a2) coprod paths -> 'a1 paths **)

let ii1_injectivity p p' =
  Obj.magic equality_by_case (Coq_ii1 p) (Coq_ii1 p')

(** val negpathsii1ii2 : 'a1 -> 'a2 -> ('a1, 'a2) coprod paths neg **)

let negpathsii1ii2 x y =
  Obj.magic equality_by_case (Coq_ii1 x) (Coq_ii2 y)

(** val negpathsii2ii1 : 'a1 -> 'a2 -> ('a1, 'a2) coprod paths neg **)

let negpathsii2ii1 x y =
  Obj.magic equality_by_case (Coq_ii2 y) (Coq_ii1 x)

(** val boolascoprod : ((coq_unit, coq_unit) coprod, bool) weq **)

let boolascoprod =
  let f = fun xx ->
    match xx with
    | Coq_ii1 _ -> Coq_true
    | Coq_ii2 _ -> Coq_false
  in
  { pr1 = f; pr2 =
  (let g = fun t ->
     match t with
     | Coq_true -> Coq_ii1 Coq_tt
     | Coq_false -> Coq_ii2 Coq_tt
   in
   let egf = fun xx ->
     match xx with
     | Coq_ii1 _ -> Coq_paths_refl
     | Coq_ii2 _ -> Coq_paths_refl
   in
   let efg = fun t ->
     match t with
     | Coq_true -> Coq_paths_refl
     | Coq_false -> Coq_paths_refl
   in
   isweq_iso f g egf efg) }

type ('x, 'y) boolsumfun = __

(** val coprodtoboolsum :
    ('a1, 'a2) coprod -> (bool, ('a1, 'a2) boolsumfun) total2 **)

let coprodtoboolsum = function
| Coq_ii1 x -> { pr1 = Coq_true; pr2 = (Obj.magic x) }
| Coq_ii2 y -> { pr1 = Coq_false; pr2 = (Obj.magic y) }

(** val boolsumtocoprod :
    (bool, ('a1, 'a2) boolsumfun) total2 -> ('a1, 'a2) coprod **)

let boolsumtocoprod xy =
  let pr3 = xy.pr1 in
  let y = xy.pr2 in
  (match pr3 with
   | Coq_true -> Coq_ii1 (Obj.magic y)
   | Coq_false -> Coq_ii2 (Obj.magic y))

(** val isweqcoprodtoboolsum :
    (('a1, 'a2) coprod, (bool, ('a1, 'a2) boolsumfun) total2) isweq **)

let isweqcoprodtoboolsum y =
  let egf = fun xy ->
    match xy with
    | Coq_ii1 _ -> Coq_paths_refl
    | Coq_ii2 _ -> Coq_paths_refl
  in
  let efg = fun xy ->
    let t = xy.pr1 in
    (match t with
     | Coq_true -> Coq_paths_refl
     | Coq_false -> Coq_paths_refl)
  in
  isweq_iso coprodtoboolsum boolsumtocoprod egf efg y

(** val weqcoprodtoboolsum :
    (('a1, 'a2) coprod, (bool, ('a1, 'a2) boolsumfun) total2) weq **)

let weqcoprodtoboolsum =
  make_weq coprodtoboolsum isweqcoprodtoboolsum

(** val nopathstruetofalse : bool paths -> empty **)

let nopathstruetofalse x =
  transportf Coq_true Coq_false x (Obj.magic Coq_tt)

(** val nopathsfalsetotrue : bool paths -> empty **)

let nopathsfalsetotrue x =
  transportb Coq_false Coq_true x (Obj.magic Coq_tt)

(** val onefiber :
    'a1 -> ('a1 -> ('a1 paths, 'a2 neg) coprod) -> ('a2, ('a1, 'a2) total2)
    isweq **)

let onefiber x c =
  let f = fun p -> { pr1 = x; pr2 = p } in
  let cx = c x in
  let cnew = fun x' ->
    match cx with
    | Coq_ii1 a ->
      (match c x' with
       | Coq_ii1 a0 -> Coq_ii1 (pathscomp0 x x x' (pathsinv0 x x a) a0)
       | Coq_ii2 b -> Coq_ii2 b)
    | Coq_ii2 _ -> c x'
  in
  let efg = fun pp ->
    let t = pp.pr1 in
    let x0 = pp.pr2 in
    let cnewt = cnew t in
    (match cnewt with
     | Coq_ii1 a ->
       pathsinv0 { pr1 = t; pr2 = x0 } { pr1 = x; pr2 =
         ((constr1 t x (pathsinv0 x t a)).pr1 x0) }
         ((constr1 t x (pathsinv0 x t a)).pr2.pr1 x0)
     | Coq_ii2 _ -> assert false (* absurd case *))
  in
  let e1 = Coq_paths_refl in
  (match cx with
   | Coq_ii1 a ->
     let cnew0 = fun x' ->
       match c x' with
       | Coq_ii1 a0 -> Coq_ii1 (pathscomp0 x x x' (pathsinv0 x x a) a0)
       | Coq_ii2 b -> Coq_ii2 b
     in
     let g = fun pp ->
       match cnew0 pp.pr1 with
       | Coq_ii1 e -> transportb x pp.pr1 e pp.pr2
       | Coq_ii2 phi -> fromempty (phi pp.pr2)
     in
     let cnewx = Coq_ii1 (pathscomp0 x x x (pathsinv0 x x a) a) in
     let e =
       maponpaths (fun x0 -> Coq_ii1 x0)
         (pathscomp0 x x x (pathsinv0 x x a) a) Coq_paths_refl
         (pathsinv0l x x a)
     in
     let egf = fun p ->
       let ff = fun cc ->
         match cc with
         | Coq_ii1 e0 -> transportb x x e0 p
         | Coq_ii2 phi -> fromempty (phi p)
       in
       let ee = maponpaths ff cnewx (Coq_ii1 Coq_paths_refl) e in
       let eee = Coq_paths_refl in
       let e2 = maponpaths ff (cnew0 x) cnewx e1 in
       pathscomp0 (ff (cnew0 x)) (ff (Coq_ii1 Coq_paths_refl)) p
         (pathscomp0 (ff (cnew0 x)) (ff cnewx) (ff (Coq_ii1 Coq_paths_refl))
           e2 ee) eee
     in
     isweq_iso f g egf efg
   | Coq_ii2 _ -> (fun _ -> assert false (* absurd case *)))

type ('x, 'y, 'z) complxstr = 'x -> 'z paths

(** val ezmap :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> 'a1
    -> ('a2, 'a3) hfiber **)

let ezmap f g z ez x =
  make_hfiber g z (f x) (ez x)

type ('x, 'y, 'z) isfibseq = ('x, ('y, 'z) hfiber) isweq

type ('x, 'y, 'z) fibseqstr =
  (('x, 'y, 'z) complxstr, ('x, 'y, 'z) isfibseq) total2

(** val make_fibseqstr :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> ('a1,
    'a2, 'a3) isfibseq -> (('a1, 'a2, 'a3) complxstr, ('a1, 'a2, 'a3)
    isfibseq) total2 **)

let make_fibseqstr _ _ _ x x0 =
  { pr1 = x; pr2 = x0 }

(** val fibseqstrtocomplxstr :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> ('a1,
    'a2, 'a3) complxstr **)

let fibseqstrtocomplxstr _ _ _ t =
  t.pr1

(** val ezweq :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> ('a1,
    ('a2, 'a3) hfiber) weq **)

let ezweq f g z fs =
  make_weq (ezmap f g z fs.pr1) fs.pr2

(** val d1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> 'a3 paths -> 'a1 **)

let d1 f g z fs y e =
  invmap (ezweq f g z fs) (make_hfiber g z y e)

(** val ezmap1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> 'a3 paths -> ('a1, 'a2) hfiber **)

let ezmap1 f g z fs y e =
  { pr1 = (d1 f g z fs y e); pr2 =
    (maponpaths (hfiberpr1 g z)
      (pr1weq (ezweq f g z fs)
        (invmap (ezweq f g z fs) (make_hfiber g z y e)))
      (make_hfiber g z y e)
      (homotweqinvweq (ezweq f g z fs) (make_hfiber g z y e))) }

(** val invezmap1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> 'a2
    -> ('a1, 'a2) hfiber -> 'a3 paths **)

let invezmap1 f g z ez y xe =
  let x = xe.pr1 in
  let e = xe.pr2 in
  pathscomp0 (g y) (g (f x)) z (maponpaths g y (f x) (pathsinv0 (f x) y e))
    (ez x)

(** val isweqezmap1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> ('a3 paths, ('a1, 'a2) hfiber) isweq **)

let isweqezmap1 f g z fs y =
  let ff = ezmap1 f g z fs y in
  let gg = invezmap1 f g z fs.pr1 y in
  let egf = fun e ->
    hfibertriangle1inv0 g z
      (pr1weq (ezweq f g z fs)
        (invmap (ezweq f g z fs) (make_hfiber g z y e)))
      (make_hfiber g z y e)
      (homotweqinvweq (ezweq f g z fs) (make_hfiber g z y e))
  in
  let efg = fun xe ->
    let x = xe.pr1 in
    let gg0 = invezmap1 f g z fs.pr1 (f x) in
    hfibertriangle2 f (f x)
      (make_hfiber f (f x)
        (invmap (ezweq f g z fs)
          (ezmap f g z (fibseqstrtocomplxstr f g z fs) x))
        (maponpaths (hfiberpr1 g z)
          (pr1weq (ezweq f g z fs)
            (invmap (ezweq f g z fs)
              (make_hfiber g z (f x) (gg0 { pr1 = x; pr2 = Coq_paths_refl }))))
          (make_hfiber g z (f x) (gg0 { pr1 = x; pr2 = Coq_paths_refl }))
          (homotweqinvweq (ezweq f g z fs)
            (make_hfiber g z (f x) (gg0 { pr1 = x; pr2 = Coq_paths_refl })))))
      (make_hfiber f (f x) x Coq_paths_refl)
      (homotinvweqweq (ezweq f g z fs) x)
      (let e1 =
         pathsinv0
           (pathscomp0
             (f (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))) 
             (f x) (f x)
             (maponpaths f
               (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
               (homotinvweqweq (ezweq f g z fs) x)) Coq_paths_refl)
           (maponpaths f
             (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
             (homotinvweqweq (ezweq f g z fs) x))
           (pathscomp0rid
             (f (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))) 
             (f x)
             (maponpaths f
               (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
               (homotinvweqweq (ezweq f g z fs) x)))
       in
       let e2 =
         let e3 =
           maponpaths (fun e ->
             maponpaths (hfiberpr1 g z)
               (pr1weq (ezweq f g z fs)
                 (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)))
               (pr1weq (ezweq f g z fs) x) e)
             (homotweqinvweq (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))
             (maponpaths (pr1weq (ezweq f g z fs))
               (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
               (homotinvweqweq (ezweq f g z fs) x))
             (pathsinv0
               (maponpaths (pr1weq (ezweq f g z fs))
                 (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
                 (homotinvweqweq (ezweq f g z fs) x))
               (homotweqinvweq (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))
               (homotweqinvweqweq (ezweq f g z fs) x))
         in
         let e4 =
           maponpathscomp
             (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
             (ezmap f g z fs.pr1) (hfiberpr1 g z)
             (homotinvweqweq (ezweq f g z fs) x)
         in
         pathscomp0
           (maponpaths (hfiberpr1 g z)
             (ezmap f g z fs.pr1
               (invmap (ezweq f g z fs) (ezmap f g z fs.pr1 x)))
             (ezmap f g z fs.pr1 x)
             (homotweqinvweq (ezweq f g z fs) (ezmap f g z fs.pr1 x)))
           (maponpaths (hfiberpr1 g z)
             (ezmap f g z fs.pr1
               (invmap (ezweq f g z fs) (ezmap f g z fs.pr1 x)))
             (ezmap f g z fs.pr1 x)
             (maponpaths (ezmap f g z fs.pr1)
               (invmap (ezweq f g z fs) (ezmap f g z fs.pr1 x)) x
               (homotinvweqweq (ezweq f g z fs) x)))
           (maponpaths (funcomp (ezmap f g z fs.pr1) (hfiberpr1 g z))
             (invmap (ezweq f g z fs) (ezmap f g z fs.pr1 x)) x
             (homotinvweqweq (ezweq f g z fs) x)) e3 e4
       in
       pathscomp0
         (maponpaths (hfiberpr1 g z)
           (pr1weq (ezweq f g z fs)
             (invmap (ezweq f g z fs)
               (ezmap f g z (fibseqstrtocomplxstr f g z fs) x)))
           (ezmap f g z (fibseqstrtocomplxstr f g z fs) x)
           (homotweqinvweq (ezweq f g z fs)
             (ezmap f g z (fibseqstrtocomplxstr f g z fs) x)))
         (maponpaths f (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))
           x (homotinvweqweq (ezweq f g z fs) x))
         (pathscomp0
           (f (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x))) 
           (f x) (f x)
           (maponpaths f
             (invmap (ezweq f g z fs) (pr1weq (ezweq f g z fs) x)) x
             (homotinvweqweq (ezweq f g z fs) x)) Coq_paths_refl) e2 e1)
  in
  isweq_iso ff gg egf efg

(** val ezweq1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> ('a3 paths, ('a1, 'a2) hfiber) weq **)

let ezweq1 f g z fs y =
  make_weq (ezmap1 f g z fs y) (isweqezmap1 f g z fs y)

(** val fibseq1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> ('a3 paths, 'a1, 'a2) fibseqstr **)

let fibseq1 f g z fs y =
  make_fibseqstr (d1 f g z fs y) f y (fun e ->
    maponpaths (hfiberpr1 g z)
      (pr1weq (ezweq f g z fs)
        (invmap (ezweq f g z fs) (make_hfiber g z y e)))
      (make_hfiber g z y e)
      (homotweqinvweq (ezweq f g z fs) (make_hfiber g z y e)))
    (isweqezmap1 f g z fs y)

(** val ezweq2 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    -> 'a1 -> ('a2 paths, ('a3 paths, 'a1) hfiber) weq **)

let ezweq2 f g z fs y x =
  ezweq1 (d1 f g z fs y) f y (fibseq1 f g z fs y) x

(** val ezmappr1 : 'a1 -> 'a2 -> (('a1, 'a2) total2, 'a1) hfiber **)

let ezmappr1 z p =
  { pr1 = { pr1 = z; pr2 = p }; pr2 = Coq_paths_refl }

(** val invezmappr1 : 'a1 -> (('a1, 'a2) total2, 'a1) hfiber -> 'a2 **)

let invezmappr1 z te =
  transportf te.pr1.pr1 z te.pr2 te.pr1.pr2

(** val isweqezmappr1 :
    'a1 -> ('a2, (('a1, 'a2) total2, 'a1) hfiber) isweq **)

let isweqezmappr1 z =
  let egf = fun _ -> Coq_paths_refl in
  let efg = fun _ -> Coq_paths_refl in
  isweq_iso (ezmappr1 z) (invezmappr1 z) egf efg

(** val isfibseqpr1 : 'a1 -> ('a2, ('a1, 'a2) total2, 'a1) isfibseq **)

let isfibseqpr1 =
  isweqezmappr1

(** val fibseqpr1 : 'a1 -> ('a2, ('a1, 'a2) total2, 'a1) fibseqstr **)

let fibseqpr1 z =
  make_fibseqstr (fun p -> { pr1 = z; pr2 = p }) (fun t -> t.pr1) z (fun _ ->
    Coq_paths_refl) (isfibseqpr1 z)

(** val ezweq1pr1 :
    'a1 -> ('a1, 'a2) total2 -> ('a1 paths, ('a2, ('a1, 'a2) total2) hfiber)
    weq **)

let ezweq1pr1 z zp =
  ezweq1 (fun p -> { pr1 = z; pr2 = p }) (fun t -> t.pr1) z (fibseqpr1 z) zp

(** val isfibseqg :
    ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, 'a1, 'a2) isfibseq **)

let isfibseqg g z =
  isweqhomot idfun (ezmap (hfiberpr1 g z) g z (fun ye -> ye.pr2)) (fun _ ->
    Coq_paths_refl) idisweq

(** val fibseqg :
    ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, 'a1, 'a2) fibseqstr **)

let fibseqg g z =
  make_fibseqstr (hfiberpr1 g z) g z (fun ye -> ye.pr2) (isfibseqg g z)

(** val d1g : ('a1 -> 'a2) -> 'a2 -> 'a1 -> 'a2 paths -> ('a1, 'a2) hfiber **)

let d1g =
  make_hfiber

(** val ezweq1g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a2 paths, (('a1, 'a2) hfiber, 'a1)
    hfiber) weq **)

let ezweq1g g z y =
  make_weq (ezmap1 (hfiberpr1 g z) g z (fibseqg g z) y)
    (isweqezmap1 (hfiberpr1 g z) g z (fibseqg g z) y)

(** val fibseq1g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a2 paths, ('a1, 'a2) hfiber, 'a1)
    fibseqstr **)

let fibseq1g g z y =
  make_fibseqstr (d1 (hfiberpr1 g z) g z (fibseqg g z) y) (hfiberpr1 g z) y
    (fun e ->
    maponpaths (hfiberpr1 g z)
      (pr1weq (ezweq (hfiberpr1 g z) g z (fibseqg g z))
        (invmap (ezweq (hfiberpr1 g z) g z (fibseqg g z))
          (make_hfiber g z y e))) (make_hfiber g z y e)
      (homotweqinvweq (ezweq (hfiberpr1 g z) g z (fibseqg g z))
        (make_hfiber g z y e)))
    (isweqezmap1 (hfiberpr1 g z) g z (fibseqg g z) y)

(** val d2g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a1 paths -> 'a2 paths **)

let d2g g z y ye' e =
  pathscomp0 (g y) (g ye'.pr1) z
    (maponpaths g y ye'.pr1 (pathsinv0 ye'.pr1 y e)) ye'.pr2

(** val ezweq3g :
    ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> (('a1,
    'a2) hfiber paths, ('a1 paths, 'a2 paths) hfiber) weq **)

let ezweq3g g z y ye' e =
  ezweq2 (d1g g z y) (hfiberpr1 g z) y (fibseq1g g z y) ye' e

(** val hfibersftogf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ('a1, 'a2)
    hfiber -> ('a1, 'a3) hfiber **)

let hfibersftogf f g z ye xe =
  { pr1 = xe.pr1; pr2 =
    (pathscomp0 (g (f xe.pr1)) (g ye.pr1) z
      (maponpaths g (f xe.pr1) ye.pr1 xe.pr2) ye.pr2) }

(** val ezmaphf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ('a1, 'a2)
    hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber **)

let ezmaphf f g z ye xe =
  { pr1 = (hfibersftogf f g z ye xe); pr2 =
    (hfibertriangle2 g z
      (make_hfiber g z (f xe.pr1)
        (pathscomp0 (g (f xe.pr1)) (g ye.pr1) z
          (maponpaths g (f xe.pr1) ye.pr1 xe.pr2) ye.pr2)) ye xe.pr2
      Coq_paths_refl) }

(** val invezmaphf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
    hfiber, ('a2, 'a3) hfiber) hfiber -> ('a1, 'a2) hfiber **)

let invezmaphf f g z ye xee' =
  { pr1 = xee'.pr1.pr1; pr2 =
    (maponpaths (hfiberpr1 g z) (hfibersgftog f g z xee'.pr1) ye xee'.pr2) }

(** val ffgg :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
    hfiber, ('a2, 'a3) hfiber) hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3)
    hfiber) hfiber **)

let ffgg f g _ ye xee' =
  let y = ye.pr1 in
  let xe = xee'.pr1 in
  let e' = xee'.pr2 in
  let x = xe.pr1 in
  let e = xe.pr2 in
  let e'' =
    maponpaths g (hfiberpr1 g (g y) (make_hfiber g (g y) (f x) e))
      (hfiberpr1 g (g y) { pr1 = y; pr2 = Coq_paths_refl })
      (maponpaths (hfiberpr1 g (g y)) (make_hfiber g (g y) (f x) e) { pr1 =
        y; pr2 = Coq_paths_refl } e')
  in
  { pr1 =
  (make_hfiber (funcomp f g) (g y) x
    (pathscomp0 (g (hfiberpr1 g (g y) (make_hfiber g (g y) (f x) e)))
      (g (hfiberpr1 g (g y) { pr1 = y; pr2 = Coq_paths_refl })) (g y) e''
      Coq_paths_refl)); pr2 =
  (hfibertriangle2 g (g y)
    (make_hfiber g (g y) (f x)
      (pathscomp0 (g (hfiberpr1 g (g y) (make_hfiber g (g y) (f x) e)))
        (g (hfiberpr1 g (g y) { pr1 = y; pr2 = Coq_paths_refl })) (g y) e''
        Coq_paths_refl)) (make_hfiber g (g y) y Coq_paths_refl)
    (maponpaths (hfiberpr1 g (g y)) (make_hfiber g (g y) (f x) e) { pr1 = y;
      pr2 = Coq_paths_refl } e') Coq_paths_refl) }

(** val homotffggid :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
    hfiber, ('a2, 'a3) hfiber) hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3)
    hfiber) hfiber paths **)

let homotffggid _ _ _ _ _ =
  Coq_paths_refl

(** val isweqezmaphf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
    hfiber, (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber) isweq **)

let isweqezmaphf f g z ye =
  let ff = ezmaphf f g z ye in
  let gg = invezmaphf f g z ye in
  let egf =
    let y = ye.pr1 in
    let ff0 = ezmaphf f g (g y) { pr1 = y; pr2 = Coq_paths_refl } in
    let gg0 = invezmaphf f g (g y) { pr1 = y; pr2 = Coq_paths_refl } in
    (fun xe ->
    hfibertriangle2 f y (gg0 (ff0 xe)) xe Coq_paths_refl Coq_paths_refl)
  in
  let efg =
    let y = ye.pr1 in
    let ff0 = ezmaphf f g (g y) { pr1 = y; pr2 = Coq_paths_refl } in
    let gg0 = invezmaphf f g (g y) { pr1 = y; pr2 = Coq_paths_refl } in
    (fun xee' ->
    let hint = Coq_paths_refl in
    pathscomp0 (ff0 (gg0 xee'))
      (ffgg f g (g y) (make_hfiber g (g y) y Coq_paths_refl) xee') xee' hint
      (homotffggid f g (g y) { pr1 = y; pr2 = Coq_paths_refl } xee'))
  in
  isweq_iso ff gg egf efg

(** val ezweqhf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
    hfiber, (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber) weq **)

let ezweqhf f g z ye =
  make_weq (ezmaphf f g z ye) (isweqezmaphf f g z ye)

(** val fibseqhf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
    hfiber, ('a1, 'a3) hfiber, ('a2, 'a3) hfiber) fibseqstr **)

let fibseqhf f g z ye =
  make_fibseqstr (hfibersftogf f g z ye) (hfibersgftog f g z) ye (fun xe ->
    hfibertriangle2 g z
      (make_hfiber g z (f xe.pr1)
        (pathscomp0 (g (f xe.pr1)) (g ye.pr1) z
          (maponpaths g (f xe.pr1) ye.pr1 xe.pr2) ye.pr2)) ye xe.pr2
      Coq_paths_refl) (isweqezmaphf f g z ye)

(** val isweqinvezmaphf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ((('a1, 'a3)
    hfiber, ('a2, 'a3) hfiber) hfiber, ('a1, 'a2) hfiber) isweq **)

let isweqinvezmaphf f g z ye =
  (invweq (ezweqhf f g z ye)).pr2

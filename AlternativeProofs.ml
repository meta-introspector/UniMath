open PartA
open Preamble

(** val total2_paths_equiv' :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths, ('a1,
    'a2) coq_PathPair) weq **)
let totalfun f z =
  { pr1 = z.pr1; pr2 = (f z.pr1 z.pr2) }

let make_weq f is =
  { pr1 = f; pr2 = is }

let invweq w =
  make_weq (invmap w) (isweqinvmap w)

let hfibersftogf f g z ye xe =
  { pr1 = xe.pr1; pr2 =
    (pathscomp0 (g (f xe.pr1)) (g ye.pr1) z
      (maponpaths g (f xe.pr1) ye.pr1 xe.pr2) ye.pr2) }

let ezmaphf f g z ye xe =
  { pr1 = (hfibersftogf f g z ye xe); pr2 =
    (hfibertriangle2 g z
      (make_hfiber g z (f xe.pr1)
        (pathscomp0 (g (f xe.pr1)) (g ye.pr1) z
          (maponpaths g (f xe.pr1) ye.pr1 xe.pr2) ye.pr2)) ye xe.pr2
      Coq_paths_refl) }
let invezmaphf f g z ye xee' =
  { pr1 = xee'.pr1.pr1; pr2 =
    (maponpaths (hfiberpr1 g z) (hfibersgftog f g z xee'.pr1) ye xee'.pr2) }

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
let homotffggid _ _ _ _ _ =
  Coq_paths_refl

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

let ezweqhf f g z ye =
  make_weq (ezmaphf f g z ye) (isweqezmaphf f g z ye)

let isweqinvezmaphf f g z ye =
  (invweq (ezweqhf f g z ye)).pr2

let ezmappr1 z p =
  { pr1 = { pr1 = z; pr2 = p }; pr2 = Coq_paths_refl }

let isweqtotaltofib f x0 x =
  let totf = totalfun f in
  let piq = fun z -> z.pr1 in
  let hfx = hfibersgftog totf piq x in
  let h = fun y ->
    let x1 = isweqinvezmaphf totf piq x y in
    let t = y.pr1 in
    let e = y.pr2 in
    let int = invezmaphf totf piq x { pr1 = t; pr2 = e } in
    let is1 = x0 t in iscontrweqb (make_weq int x1) is1
  in
  let ip = ezmappr1 x in
  let iq = ezmappr1 x in
  let h0 = fun p -> hfx (ip p) in
  let is2 = twooutof3c ip hfx (isweqezmappr1 x) h in
  let h' = fun p -> iq (f x p) in
  let ee = fun _ -> Coq_paths_refl in
  let x2 = isweqhomot h0 h' ee is2 in twooutof3a (f x) iq x2 (isweqezmappr1 x)

let total2_paths_equiv' x y =
  weqtotaltofib (fun z p -> { pr1 = (maponpaths (fun t -> t.pr1) x z p);
    pr2 = Coq_paths_refl })
    (isweqcontrcontr
      (totalfun (fun z p -> { pr1 = (maponpaths (fun t -> t.pr1) x z p);
        pr2 = Coq_paths_refl })) (iscontrcoconusfromt x) { pr1 = { pr1 = x;
      pr2 = { pr1 = Coq_paths_refl; pr2 = Coq_paths_refl } }; pr2 = (fun _ ->
      Coq_paths_refl) }) y

(** val total2_paths_equiv'_compute :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths ->
    ('a1, 'a2) coq_PathPair) paths **)

let total2_paths_equiv'_compute _ _ =
  Coq_paths_refl

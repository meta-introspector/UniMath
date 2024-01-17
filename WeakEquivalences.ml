open PartA
open Preamble

(** val transitive_paths_weq :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) weq **)

let transitive_paths_weq x y z xeqy =
  weq_iso (fun xeqz -> pathscomp0 y x z (pathsinv0 x y xeqy) xeqz)
    (fun yeqz -> pathscomp0 x y z xeqy yeqz) (fun xeqz ->
    pathscomp0
      (pathscomp0 x y z xeqy (pathscomp0 y x z (pathsinv0 x y xeqy) xeqz))
      (pathscomp0 x x z (pathscomp0 x y x xeqy (pathsinv0 x y xeqy)) xeqz)
      xeqz (path_assoc x y x z xeqy (pathsinv0 x y xeqy) xeqz)
      (pathscomp0
        (pathscomp0 x x z (pathscomp0 x y x xeqy (pathsinv0 x y xeqy)) xeqz)
        (pathscomp0 x x z Coq_paths_refl xeqz) xeqz
        (maponpaths (fun p -> pathscomp0 x x z p xeqz)
          (pathscomp0 x y x xeqy (pathsinv0 x y xeqy)) Coq_paths_refl
          (pathsinv0r x y xeqy)) Coq_paths_refl)) (fun yeqz ->
    pathscomp0
      (pathscomp0 y x z (pathsinv0 x y xeqy) (pathscomp0 x y z xeqy yeqz))
      (pathscomp0 y y z (pathscomp0 y x y (pathsinv0 x y xeqy) xeqy) yeqz)
      yeqz (path_assoc y x y z (pathsinv0 x y xeqy) xeqy yeqz)
      (pathscomp0
        (pathscomp0 y y z (pathscomp0 y x y (pathsinv0 x y xeqy) xeqy) yeqz)
        (pathscomp0 y y z Coq_paths_refl yeqz) yeqz
        (maponpaths (fun p -> pathscomp0 y y z p yeqz)
          (pathscomp0 y x y (pathsinv0 x y xeqy) xeqy) Coq_paths_refl
          (pathsinv0l x y xeqy)) Coq_paths_refl))

(* val weqtotal2comm :  (('a1, ('a2, 'a3) total2) total2, ('a2, ('a1, 'a3) total2) total2) weq *)
let weqtotal2comm : (('a1, ('a2, 'a3) total2) total2, ('a2, ('a1, 'a3) total2) total2) weq  =
  weq_iso (fun pair -> { pr1 = pair.pr2.pr1; pr2 = { pr1 = pair.pr1; pr2 =
    pair.pr2.pr2 } }) (fun pair -> { pr1 = pair.pr2.pr1; pr2 = { pr1 =
    pair.pr1; pr2 = pair.pr2.pr2 } }) (fun _ -> Coq_paths_refl) (fun _ ->
    Coq_paths_refl)

(** val pathsdirprodweq :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> (('a1, 'a2) dirprod paths, ('a1 paths, 'a2
    paths) dirprod) weq **)

let pathsdirprodweq x1 x2 y1 y2 =
  weqcomp (total2_paths_equiv (make_dirprod x1 y1) (make_dirprod x2 y2))
    (weqfibtototal (fun p ->
      transitive_paths_weq (transportf x1 x2 p y1) y1 y2
        (toforallpaths (transportf x1 x2 p) idfun (transportf_const x1 x2 p)
          y1)))

(** val dirprod_with_contr_r :
    'a1 iscontr -> ('a2, ('a2, 'a1) dirprod) weq **)

let weqtodirprodwithunit =
  let f = fun x -> make_dirprod x Coq_tt in
  { pr1 = f; pr2 =
  (let g = fun xu -> xu.pr1 in
   let egf = fun _ -> Coq_paths_refl in
   let efg = fun _ -> Coq_paths_refl in isweq_iso f g egf efg) }

let dirprod_with_contr_r iscontrX =
  weqcomp weqtodirprodwithunit
    (weqdirprodf idweq (invweq (weqcontrtounit iscontrX)))

(** val dirprod_with_contr_l :
    'a1 iscontr -> ('a2, ('a1, 'a2) dirprod) weq **)

let weqdirprodcomm =
  let f = fun xy -> make_dirprod xy.pr2 xy.pr1 in
  let g = fun yx -> make_dirprod yx.pr2 yx.pr1 in
  let egf = fun _ -> Coq_paths_refl in
  let efg = fun _ -> Coq_paths_refl in
  { pr1 = f; pr2 = (isweq_iso f g egf efg) }

let dirprod_with_contr_l iscontrX =
  weqcomp (dirprod_with_contr_r iscontrX) weqdirprodcomm

(** val total2_assoc_fun_left :
    (('a1 -> ('a2, 'a3) total2, 'a4) total2, ('a1 -> 'a2, ('a1 -> 'a3, 'a4)
    total2) total2) weq **)

let total2_assoc_fun_left =
  weq_iso (fun p -> { pr1 = (fun a -> (p.pr1 a).pr1); pr2 = { pr1 = (fun a ->
    (p.pr1 a).pr2); pr2 = p.pr2 } }) (fun p -> { pr1 = (fun a -> { pr1 =
    (p.pr1 a); pr2 = (p.pr2.pr1 a) }); pr2 = p.pr2.pr2 }) (fun _ ->
    Coq_paths_refl) (fun _ -> Coq_paths_refl)

(** val sec_total2_distributivity :
    ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq **)

let sec_total2_distributivity =
  weq_iso (fun f -> { pr1 = (fun a -> (f a).pr1); pr2 = (fun a ->
    (f a).pr2) }) (fun f a -> { pr1 = (f.pr1 a); pr2 = (f.pr2 a) })
    (Obj.magic (fun _ -> Coq_paths_refl))
    (Obj.magic (fun _ -> Coq_paths_refl))

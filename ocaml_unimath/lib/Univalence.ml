open PartA
open PartA0
open PartD
open Preamble
open UnivalenceAxiom

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val funextsec_toforallpaths :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1 -> 'a2) paths
    paths **)

let funextsec_toforallpaths f g h =
  pathsinv0 h
    (invmap (Obj.magic weqtoforallpaths f g)
      (pr1weq (Obj.magic weqtoforallpaths f g) h))
    (homotinvweqweq0 (Obj.magic weqtoforallpaths f g) h)

(** val toforallpaths_funextsec :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2) homot
    paths **)

let toforallpaths_funextsec f g h =
  homotweqinvweq (Obj.magic weqtoforallpaths f g) h

(** val toforallpaths_funextsec_comp :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> (('a1, 'a2) homot -> ('a1, 'a2) homot)
    paths **)

let toforallpaths_funextsec_comp f g =
  Obj.magic funextsec
    (funcomp (Obj.magic funextsec f g) (Obj.magic toforallpaths f g)) idfun
    (fun x -> Obj.magic toforallpaths_funextsec f g x)

(** val maponpaths_funextsec :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) homot -> 'a2 paths paths **)

let maponpaths_funextsec f g t p =
  pathscomp0
    (maponpaths (fun h -> Obj.magic h t) (Obj.magic f) (Obj.magic g)
      (funextsec (Obj.magic f) (Obj.magic g) (Obj.magic p)))
    (toforallpaths f g (Obj.magic funextsec f g p) t) (p t) Coq_paths_refl
    (eqtohomot (funcomp (Obj.magic funextsec f g) (toforallpaths f g) p)
      (idfun p)
      (eqtohomot (funcomp (Obj.magic funextsec f g) (toforallpaths f g))
        idfun (toforallpaths_funextsec_comp f g) p) t)

(** val weqonsec :
    ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> ('a1 -> 'a3, 'a2 -> 'a4) weq **)

let weqonsec f g =
  weqcomp (weqonsecfibers g) (invweq (weqonsecbase f))

(** val weq_transportf : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) weq **)

let weq_transportf _ _ _ =
  idweq

(** val weq_transportf_comp :
    'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths **)

let weq_transportf_comp _ _ _ _ =
  Coq_paths_refl

(** val weqonpaths2 :
    ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths ->
    ('a1 paths, 'a2 paths) weq **)

let weqonpaths2 w x x' _ _ _ _ =
  weqonpaths w x x'

(** val eqweqmap_ap : 'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths **)

let eqweqmap_ap _ _ _ _ =
  Coq_paths_refl

(** val eqweqmap_ap' :
    'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths **)

let eqweqmap_ap' _ _ _ _ =
  Coq_paths_refl

(** val pr1_eqweqmap : __ paths -> ('a1 -> 'a2) paths **)

let pr1_eqweqmap _ =
  Coq_paths_refl

(** val path_to_fun : __ paths -> 'a1 -> 'a2 **)

let path_to_fun _ =
  Obj.magic idfun

(** val pr1_eqweqmap2 : coq_UU paths -> ('a1 -> 'a2) paths **)

let pr1_eqweqmap2 _ =
  Coq_paths_refl

(** val weqpath_transport : ('a1, 'a2) weq -> ('a1 -> 'a2) paths **)

let weqpath_transport w =
  pathscomp0
    (Obj.magic transportf __ __
      (weqtopathsUAH (fun _ _ -> univalenceAxiom) (Obj.magic w)))
    (eqweqmap (weqtopathsUAH (fun _ _ -> univalenceAxiom) (Obj.magic w))).pr1
    w.pr1
    (pathsinv0
      (eqweqmap (weqtopathsUAH (fun _ _ -> univalenceAxiom) (Obj.magic w))).pr1
      (Obj.magic transportf __ __
        (weqtopathsUAH (fun _ _ -> univalenceAxiom) (Obj.magic w)))
      (pr1_eqweqmap2
        (weqtopathsUAH (fun _ _ -> univalenceAxiom) (Obj.magic w))))
    (maponpaths (Obj.magic (fun t -> t.pr1))
      (eqweqmap (weqtopathsUAH (fun _ _ -> univalenceAxiom) (Obj.magic w)))
      (Obj.magic w) (weqpathsweq (Obj.magic w)))

(** val weqpath_cast : ('a1, 'a2) weq -> ('a1 -> 'a2) paths **)

let weqpath_cast w = w
  (* pathscomp0 *)
  (*   (cast (weqtopathsUAH (fun _ _ -> univalenceAxiom) (Obj.magic w))) *)
  (*   (eqweqmap (weqtopathsUAH (fun _ _ -> univalenceAxiom) (Obj.magic w))).pr1 *)
  (*   w.pr1 *)
  (*   (pr1_eqweqmap (weqtopathsUAH (fun _ _ -> univalenceAxiom) (Obj.magic w))) *)
  (*   (maponpaths (Obj.magic (fun t -> t.pr1)) *)
  (*     (eqweqmap (weqtopathsUAH (fun _ _ -> univalenceAxiom) (Obj.magic w))) *)
  (*     (Obj.magic w) (weqpathsweq (Obj.magic w))) *)

(** val switch_weq :
    ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a2 paths -> 'a1 paths **)

let switch_weq f x y p =
  pathscomp0 (pr1weq (invweq f) y) (pr1weq (invweq f) (pr1weq f x)) x
    (maponpaths (pr1weq (invweq f)) y (pr1weq f x) p) (homotinvweqweq f x)

(** val switch_weq' :
    ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths **)

let switch_weq' f x y p =
  pathscomp0 y (pr1weq f (invmap f y)) (pr1weq f x)
    (pathsinv0 (pr1weq f (invmap f y)) y (homotweqinvweq f y))
    (maponpaths (pr1weq f) (pr1weq (invweq f) y) x p)

(** val weq_over_sections :
    ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> 'a3 -> 'a3 paths ->
    (('a2 -> 'a3) -> ('a4, 'a5) weq) -> ((('a2 -> 'a3, 'a4) total2, 'a3)
    hfiber, (('a1 -> 'a3, 'a5) total2, 'a3) hfiber) weq **)

let weq_over_sections w _ _ _ _ _ _ g =
  weqbandf (weqbandf (weqonsecbase w) g) (fun _ -> idweq)

(** val maponpaths_app_homot :
    ('a2 -> 'a1 -> 'a3) -> ('a2 -> 'a1 -> 'a3) -> (('a2, 'a1) dirprod -> 'a3
    paths) -> 'a1 -> 'a2 -> 'a3 paths paths **)

let maponpaths_app_homot f g p x y =
  maponpaths_funextsec (f y) (fun x0 -> g y x0) x (fun x0 ->
    p { pr1 = y; pr2 = x0 })

(** val path_path_fun :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1 -> 'a2) paths
    -> ('a1 -> 'a2 paths paths) -> ('a1 -> 'a2) paths paths **)

let path_path_fun f g e_UU2081_ e_UU2082_ h =
  pathscomp0 e_UU2081_
    (Obj.magic funextsec f g
      (toforallpaths (Obj.magic f) (Obj.magic g) (Obj.magic e_UU2081_)))
    e_UU2082_
    (pathsinv0
      (Obj.magic funextsec f g
        (toforallpaths (Obj.magic f) (Obj.magic g) (Obj.magic e_UU2081_)))
      e_UU2081_ (funextsec_toforallpaths f g e_UU2081_))
    (pathscomp0
      (Obj.magic funextsec f g
        (toforallpaths (Obj.magic f) (Obj.magic g) (Obj.magic e_UU2081_)))
      (Obj.magic funextsec f g
        (toforallpaths (Obj.magic f) (Obj.magic g) (Obj.magic e_UU2082_)))
      e_UU2082_
      (maponpaths (Obj.magic funextsec f g)
        (Obj.magic toforallpaths f g e_UU2081_)
        (Obj.magic toforallpaths f g e_UU2082_)
        (funextsec (Obj.magic toforallpaths f g e_UU2081_)
          (Obj.magic toforallpaths f g e_UU2082_) (fun x -> Obj.magic h x)))
      (funextsec_toforallpaths f g e_UU2082_))

open HLevels
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val maponpaths_1 :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths **)

let maponpaths_1 =
  maponpaths

(** val maponpaths_2 :
    ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 paths **)

let maponpaths_2 f y y' e_y x =
  maponpaths (fun y0 -> f y0 x) y y' e_y

(** val maponpaths_12 :
    ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths
    -> 'a3 paths **)

let maponpaths_12 f y y' e_y x x' e_x =
  pathscomp0 (f y x) (f y x') (f y' x') (maponpaths_1 (f y) x x' e_x)
    (maponpaths_2 f y y' e_y x')

(** val maponpaths_3 :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 ->
    'a4 paths **)

let maponpaths_3 f z z' e_z y x =
  maponpaths (fun z0 -> f z0 y x) z z' e_z

(** val maponpaths_123 :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 ->
    'a2 paths -> 'a3 -> 'a3 -> 'a3 paths -> 'a4 paths **)

let maponpaths_123 f z z' e_z y y' e_y x x' e_x =
  pathscomp0 (f z y x) (f z y' x') (f z' y' x')
    (maponpaths_12 (f z) y y' e_y x x' e_x) (maponpaths_3 f z z' e_z y' x')

(** val maponpaths_13 :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 ->
    'a3 -> 'a3 paths -> 'a4 paths **)

let maponpaths_13 f z z' e_z y x x' e_x =
  maponpaths_123 f z z' e_z y y Coq_paths_refl x x' e_x

(** val maponpaths_4 :
    ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 ->
    'a3 -> 'a4 -> 'a5 paths **)

let maponpaths_4 f w w' e_w z y x =
  maponpaths (fun w0 -> f w0 z y x) w w' e_w

(** val maponpaths_1234 :
    ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 ->
    'a2 -> 'a2 paths -> 'a3 -> 'a3 -> 'a3 paths -> 'a4 -> 'a4 -> 'a4 paths ->
    'a5 paths **)

let maponpaths_1234 f w w' e_w z z' e_z y y' e_y x x' e_x =
  pathscomp0 (f w z y x) (f w z' y' x') (f w' z' y' x')
    (maponpaths_123 (f w) z z' e_z y y' e_y x x' e_x)
    (maponpaths_4 f w w' e_w z' y' x')

(** val maponpaths_for_constant_function :
    'a2 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths paths **)

let maponpaths_for_constant_function _ _ _ _ =
  Coq_paths_refl

(** val base_paths_pair_path_in2 :
    'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a1 paths paths **)

let base_paths_pair_path_in2 _ _ _ _ =
  Coq_paths_refl

(** val transportf_transpose_right :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths **)

let transportf_transpose_right _ _ _ _ _ =
  idfun

(** val transportb_transpose_right :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths **)

let transportb_transpose_right _ _ _ _ _ =
  idfun

(** val transportf_transpose_left :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths **)

let transportf_transpose_left _ _ _ _ _ =
  idfun

(** val transportb_transpose_left :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths **)

let transportb_transpose_left _ _ _ _ _ =
  idfun

(** val transportf_pathsinv0 :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths **)

let transportf_pathsinv0 _ _ _ _ _ _ =
  Coq_paths_refl

(** val transportf_comp_lemma :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths ->
    'a2 paths **)

let transportf_comp_lemma a a' a'' e e' x x' h =
  pathscomp0 (transportf a a'' e x)
    (transportf a' a'' e'
      (transportf a a' (pathscomp0 a a'' a' e (pathsinv0 a' a'' e')) x))
    (transportf a' a'' e' x')
    (pathscomp0 (transportf a a'' e x)
      (transportf a a''
        (pathscomp0 a a' a'' (pathscomp0 a a'' a' e (pathsinv0 a' a'' e')) e')
        x)
      (transportf a' a'' e'
        (transportf a a' (pathscomp0 a a'' a' e (pathsinv0 a' a'' e')) x))
      (maponpaths (fun p -> transportf a a'' p x) e
        (pathscomp0 a a' a'' (pathscomp0 a a'' a' e (pathsinv0 a' a'' e')) e')
        (pathsinv0
          (pathscomp0 a a' a'' (pathscomp0 a a'' a' e (pathsinv0 a' a'' e'))
            e') e
          (pathscomp0
            (pathscomp0 a a' a''
              (pathscomp0 a a'' a' e (pathsinv0 a' a'' e')) e')
            (pathscomp0 a a'' a'' e
              (pathscomp0 a'' a' a'' (pathsinv0 a' a'' e') e')) e
            (pathsinv0
              (pathscomp0 a a'' a'' e
                (pathscomp0 a'' a' a'' (pathsinv0 a' a'' e') e'))
              (pathscomp0 a a' a''
                (pathscomp0 a a'' a' e (pathsinv0 a' a'' e')) e')
              (path_assoc a a'' a' a'' e (pathsinv0 a' a'' e') e'))
            (pathscomp0
              (pathscomp0 a a'' a'' e
                (pathscomp0 a'' a' a'' (pathsinv0 a' a'' e') e'))
              (pathscomp0 a a'' a'' e Coq_paths_refl) e
              (maponpaths (pathscomp0 a a'' a'' e)
                (pathscomp0 a'' a' a'' (pathsinv0 a' a'' e') e')
                Coq_paths_refl (pathsinv0l a' a'' e'))
              (pathscomp0rid a a'' e))))) Coq_paths_refl)
    (maponpaths (transportf a' a'' e')
      (transportf a a' (pathscomp0 a a'' a' e (pathsinv0 a' a'' e')) x) x' h)

(** val transportf_comp_lemma_hset :
    'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a1 isaset -> 'a2 paths -> 'a2 paths **)

let transportf_comp_lemma_hset a e x x' hs ex =
  pathscomp0 (transportf a a e x) (transportf a a Coq_paths_refl x) x'
    (maponpaths (fun p -> transportf a a p x) e Coq_paths_refl
      (let x'0 = Coq_paths_refl in (Obj.magic hs a a e x'0).pr1)) ex

(** val transportf_bind :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths ->
    'a2 paths **)

let transportf_bind _ _ _ _ _ _ _ h =
  h

(** val pathscomp0_dep :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2
    paths -> 'a2 paths -> 'a2 paths **)

let pathscomp0_dep x x' x'' e e' y y' y'' ee ee' =
  pathscomp0 y (transportf x' x e y')
    (transportf x'' x (pathscomp0 x'' x' x e' e) y'') ee
    (transportf_bind x' x'' x e' e y' y'' ee')

(** val transportf_set :
    'a1 -> 'a1 paths -> 'a2 -> 'a1 isaset -> 'a2 paths **)

let transportf_set a e b x =
  transportf_comp_lemma_hset a e b b x Coq_paths_refl

(** val transportf_pair :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a3 -> 'a3 paths **)

let transportf_pair _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val weqhomot :
    ('a1 -> 'a2) -> ('a1, 'a2) weq -> ('a1, 'a2) homot -> ('a1, 'a2) isweq **)

let weqhomot f w h =
  isweqhomot (pr1weq w) f h (weqproperty w)

(** val invmap_eq : ('a1, 'a2) weq -> 'a2 -> 'a1 -> 'a2 paths -> 'a1 paths **)

let invmap_eq f b a h =
  invmaponpathsweq f (invmap f b) a
    (pathscomp0 (pr1weq f (invmap f b)) b (pr1weq f a) (homotweqinvweq f b) h)

(** val pr1_transportf :
    'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a3) total2 -> 'a2 paths **)

let pr1_transportf a a' e xs =
  pathsinv0 (transportf a a' e xs.pr1) (transportf a a' e xs).pr1
    (transport_map (fun _ t -> t.pr1) a a' e xs)

(** val pr2_transportf :
    'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a3) dirprod -> 'a3 paths **)

let pr2_transportf a a' e xs =
  pathsinv0 (transportf a a' e xs.pr2) (transportf a a' e xs).pr2
    (transport_map (fun _ t -> t.pr2) a a' e xs)

(** val coprodcomm_coprodcomm :
    ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths **)

let coprodcomm_coprodcomm _ =
  Coq_paths_refl

(** val sumofmaps_funcomp :
    ('a1 -> 'a2) -> ('a2 -> 'a5) -> ('a3 -> 'a4) -> ('a4 -> 'a5) -> (('a1,
    'a3) coprod, 'a5) homot **)

let sumofmaps_funcomp _ _ _ _ _ =
  Coq_paths_refl

(** val sumofmaps_homot :
    ('a1 -> 'a3) -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a1,
    'a3) homot -> ('a2, 'a3) homot -> (('a1, 'a2) coprod, 'a3) homot **)

let sumofmaps_homot _ _ _ _ h h2 = function
| Coq_ii1 a -> h a
| Coq_ii2 b -> h2 b

(** val coprod_rect_compute_1 :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a1 -> 'a3 paths **)

let coprod_rect_compute_1 _ _ _ =
  Coq_paths_refl

(** val coprod_rect_compute_2 :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a2 -> 'a3 paths **)

let coprod_rect_compute_2 _ _ _ =
  Coq_paths_refl

(** val flipsec : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flipsec f x y =
  f y x

(** val isweq_flipsec : ('a1 -> 'a2 -> 'a3, 'a2 -> 'a1 -> 'a3) isweq **)

let isweq_flipsec y =
  isweq_iso flipsec flipsec (fun _ -> Coq_paths_refl) (fun _ ->
    Coq_paths_refl) y

(** val flipsec_weq : ('a1 -> 'a2 -> 'a3, 'a2 -> 'a1 -> 'a3) weq **)

let flipsec_weq =
  make_weq flipsec isweq_flipsec

(** val empty_hlevel : nat -> empty isofhlevel **)

let empty_hlevel = function
| O -> isapropempty
| S _ -> Obj.magic fromempty

(** val empty_HLevel : nat -> coq_HLevel **)

let empty_HLevel n =
  { pr1 = __; pr2 = (empty_hlevel n) }

(** val coq_HLevel_fun : nat -> coq_HLevel -> coq_HLevel -> coq_HLevel **)

let coq_HLevel_fun n _ y =
  { pr1 = __; pr2 = (impredfun n y.pr2) }

(** val isofhlevel_hsubtype :
    nat -> 'a1 isofhlevel -> 'a1 hsubtype -> 'a1 carrier isofhlevel **)

let isofhlevel_hsubtype n isof subt =
  isofhleveltotal2 (S n) isof (fun x ->
    isofhlevelsnprop n (propproperty (subt x)))

(** val weqtotal2 :
    ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> (('a1, 'a3) total2, ('a2,
    'a4) total2) weq **)

let weqtotal2 f e =
  { pr1 = (fun xp -> { pr1 = (pr1weq f xp.pr1); pr2 =
    (pr1weq (e xp.pr1) xp.pr2) }); pr2 =
    (twooutof3c (totalfun (fun x -> pr1weq (e x))) (weqfp f).pr1
      (isweqfibtototal e) (weqfp f).pr2) }

(** val weq_subtypes' :
    ('a1, 'a2) weq -> ('a1, 'a3) isPredicate -> ('a2, 'a4) isPredicate ->
    ('a1 -> ('a3, 'a4) logeq) -> (('a1, 'a3) total2, ('a2, 'a4) total2) weq **)

let weq_subtypes' w hS hT hST =
  weqbandf w (fun x -> weqiff (hST x) (hS x) (hT (pr1weq w x)))

(** val weq_subtypes_iff :
    ('a1, 'a2) isPredicate -> ('a1, 'a3) isPredicate -> ('a1 -> ('a2, 'a3)
    logeq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) weq **)

let weq_subtypes_iff hS hT hST =
  weq_subtypes' idweq hS hT hST

(** val hlevel_total2 :
    nat -> ('a1, 'a2) total2 isofhlevel -> 'a1 isofhlevel -> 'a1 -> 'a2
    isofhlevel **)

let hlevel_total2 n ic ia x =
  isofhlevelweqf n (invweq (ezweqpr1 x))
    (isofhlevelffromXY n (fun t -> t.pr1) ic ia x)

(** val path_sigma_hprop :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a2 isaprop -> (('a1, 'a2)
    total2 paths, 'a1 paths) weq **)

let path_sigma_hprop x y hB =
  weqcomp (total2_paths_equiv x y)
    (weqpr1 (fun z -> Obj.magic hB (transportf x.pr1 y.pr1 z x.pr2) y.pr2))

type coq_PointedType = (coq_UU, __) total2

(** val pointedType : 'a1 -> coq_PointedType **)

let pointedType x =
  { pr1 = __; pr2 = (Obj.magic x) }

type underlyingType = __

(** val basepoint : coq_PointedType -> __ **)

let basepoint x =
  x.pr2

(** val loopSpace : coq_PointedType -> coq_PointedType **)

let loopSpace _ =
  pointedType Coq_paths_refl

(** val underlyingLoop : coq_PointedType -> underlyingType -> __ paths **)

let underlyingLoop _ l =
  Obj.magic l

(** val _UU03a9_ : coq_PointedType -> coq_PointedType **)

let _UU03a9_ =
  loopSpace

(** val weq_total2_prod :
    (('a2, ('a1, 'a3) dirprod) total2, ('a1, ('a2, 'a3) total2) dirprod) weq **)

let weq_total2_prod =
  make_weq (fun x0 ->
    let y = x0.pr1 in
    let pr3 = x0.pr2 in
    let x = pr3.pr1 in
    let z = pr3.pr2 in { pr1 = x; pr2 = { pr1 = y; pr2 = z } })
    (isweq_iso (fun x0 ->
      let y = x0.pr1 in
      let pr3 = x0.pr2 in
      let x = pr3.pr1 in
      let z = pr3.pr2 in { pr1 = x; pr2 = { pr1 = y; pr2 = z } }) (fun x0 ->
      let x = x0.pr1 in
      let pr3 = x0.pr2 in
      let y = pr3.pr1 in
      let z = pr3.pr2 in { pr1 = y; pr2 = { pr1 = x; pr2 = z } }) (fun _ ->
      Coq_paths_refl) (fun _ -> Coq_paths_refl))

(** val totalAssociativity :
    (('a1, ('a2, 'a3) total2) total2, (('a1, 'a2) total2, 'a3) total2) weq **)

let totalAssociativity =
  { pr1 = (fun x0 ->
    let x = x0.pr1 in
    let pr3 = x0.pr2 in
    let y = pr3.pr1 in
    let z = pr3.pr2 in { pr1 = { pr1 = x; pr2 = y }; pr2 = z }); pr2 =
    (isweq_iso (fun x0 ->
      let x = x0.pr1 in
      let pr3 = x0.pr2 in
      let y = pr3.pr1 in
      let z = pr3.pr2 in { pr1 = { pr1 = x; pr2 = y }; pr2 = z }) (fun x0 ->
      let pr3 = x0.pr1 in
      let x = pr3.pr1 in
      let y = pr3.pr2 in
      let z = x0.pr2 in { pr1 = x; pr2 = { pr1 = y; pr2 = z } }) (fun _ ->
      Coq_paths_refl) (fun _ -> Coq_paths_refl)) }

(** val paths3 :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a3 -> 'a3 -> 'a1 paths -> 'a2 paths -> 'a3
    paths -> ('a1, ('a2, 'a3) dirprod) dirprod paths **)

let paths3 _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val confun : 'a2 -> 'a1 -> 'a2 **)

let confun y _ =
  y

type 'x path_type = 'x

(** val path_start : 'a1 -> 'a1 -> 'a1 paths -> 'a1 **)

let path_start x _ _ =
  x

(** val path_end : 'a1 -> 'a1 -> 'a1 paths -> 'a1 **)

let path_end _ x' _ =
  x'

(** val uniqueness : 'a1 iscontr -> 'a1 -> 'a1 paths **)

let uniqueness i t =
  i.pr2 t

(** val uniqueness' : 'a1 iscontr -> 'a1 -> 'a1 paths **)

let uniqueness' i t =
  pathsinv0 t i.pr1 (i.pr2 t)

(** val path_inverse_to_right :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths **)

let path_inverse_to_right _ _ _ _ _ =
  Coq_paths_refl

(** val path_inverse_to_right' :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths **)

let path_inverse_to_right' _ _ _ _ _ =
  Coq_paths_refl

(** val pathsinv0_to_right :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths
    paths -> 'a1 paths paths **)

let pathsinv0_to_right _ _ _ _ _ _ e =
  e

(** val pathsinv0_to_right' :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths **)

let pathsinv0_to_right' _ _ _ _ e =
  e

(** val pathsinv0_to_right'' :
    'a1 -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths **)

let pathsinv0_to_right'' x p e =
  pathsinv0_to_right' x x p Coq_paths_refl
    (internal_paths_rew_r (pathscomp0 x x x p Coq_paths_refl) p e
      (pathscomp0rid x x p))

(** val loop_power_nat : 'a1 -> 'a1 paths -> nat -> 'a1 paths **)

let rec loop_power_nat y l = function
| O -> Coq_paths_refl
| S n0 -> pathscomp0 y y y (loop_power_nat y l n0) l

(** val irrel_paths :
    ('a1 -> 'a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1
    paths paths **)

let irrel_paths irr x y p q =
  let k = fun _ _ -> Coq_paths_refl in
  let l =
    pathscomp0 (pathscomp0 x y y p (irr y y)) (irr x y)
      (pathscomp0 x y y q (irr y y)) (k y p)
      (pathsinv0 (pathscomp0 x y y q (irr y y)) (irr x y) (k y q))
  in
  pathscomp_cancel_right x y y p q (irr y y) l

(** val path_inv_rotate_2 :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1
    paths -> 'a1 paths paths -> 'a1 paths paths **)

let path_inv_rotate_2 a b _ _ p p' _ _ =
  internal_paths_rew_r (pathscomp0 a b b p Coq_paths_refl) p
    (internal_paths_rew_r (pathscomp0 a b b p' Coq_paths_refl) p' idfun
      (pathscomp0rid a b p')) (pathscomp0rid a b p)

(** val maponpaths_naturality :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 paths
    -> 'a2 paths -> 'a2 paths paths -> 'a2 paths paths -> 'a2 paths paths **)

let maponpaths_naturality f x x' x'' p q _ _ _ _ =
  maponpathscomp0 x x' x'' f p q

(** val maponpaths_naturality' :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 paths
    -> 'a2 paths -> 'a2 paths paths -> 'a2 paths paths -> 'a2 paths paths **)

let maponpaths_naturality' _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val pr2_of_make_hfiber :
    ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a2 paths paths **)

let pr2_of_make_hfiber _ _ _ _ =
  Coq_paths_refl

(** val pr2_of_pair : 'a1 -> 'a2 -> 'a2 paths **)

let pr2_of_pair _ _ =
  Coq_paths_refl

(** val pr2_of_make_weq :
    ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) isweq paths **)

let pr2_of_make_weq _ _ =
  Coq_paths_refl

(** val pair_path2 :
    'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a2 paths ->
    ('a1, 'a2) total2 paths **)

let pair_path2 _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val pair_path_in2_comp1 :
    'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a1 paths paths **)

let pair_path_in2_comp1 _ _ _ _ =
  Coq_paths_refl

(** val total2_paths2_comp1 :
    'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a1 paths paths **)

let total2_paths2_comp1 _ _ _ _ _ _ =
  Coq_paths_refl

(** val total2_paths2_comp2 :
    'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths **)

let total2_paths2_comp2 _ _ _ _ _ _ =
  Coq_paths_refl

(** val from_total2 : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3 **)

let from_total2 f x0 =
  let x = x0.pr1 in let p = x0.pr2 in f x p

(** val inv_equality_by_case_equality_by_case :
    ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths ->
    ('a1, 'a2) coprod paths paths **)

let inv_equality_by_case_equality_by_case _ _ _ =
  Coq_paths_refl

(** val equality_by_case_inv_equality_by_case :
    ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) equality_cases ->
    ('a1, 'a2) equality_cases paths **)

let equality_by_case_inv_equality_by_case x y _ =
  match x with
  | Coq_ii1 _ ->
    (match y with
     | Coq_ii1 _ -> Coq_paths_refl
     | Coq_ii2 _ -> assert false (* absurd case *))
  | Coq_ii2 _ ->
    (match y with
     | Coq_ii1 _ -> assert false (* absurd case *)
     | Coq_ii2 _ -> Coq_paths_refl)

(** val equality_by_case_equiv :
    ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> (('a1, 'a2) coprod paths, ('a1,
    'a2) equality_cases) weq **)

let equality_by_case_equiv t u =
  weq_iso (equality_by_case t u) (inv_equality_by_case t u)
    (inv_equality_by_case_equality_by_case t u)
    (equality_by_case_inv_equality_by_case t u)

(** val paths_inl_inl_equiv :
    'a1 -> 'a1 -> (('a1, 'a2) coprod paths, 'a1 paths) weq **)

let paths_inl_inl_equiv a a' =
  Obj.magic equality_by_case_equiv (Coq_ii1 a) (Coq_ii1 a')

(** val paths_inl_inr_equiv :
    'a1 -> 'a2 -> (('a1, 'a2) coprod paths, empty) weq **)

let paths_inl_inr_equiv a b =
  Obj.magic equality_by_case_equiv (Coq_ii1 a) (Coq_ii2 b)

(** val paths_inr_inr_equiv :
    'a2 -> 'a2 -> (('a1, 'a2) coprod paths, 'a2 paths) weq **)

let paths_inr_inr_equiv b b' =
  Obj.magic equality_by_case_equiv (Coq_ii2 b) (Coq_ii2 b')

(** val paths_inr_inl_equiv :
    'a1 -> 'a2 -> (('a1, 'a2) coprod paths, empty) weq **)

let paths_inr_inl_equiv a b =
  Obj.magic equality_by_case_equiv (Coq_ii2 b) (Coq_ii1 a)

(** val isInjective_inl : ('a1, ('a1, 'a2) coprod) isInjective **)

let isInjective_inl x x' =
  isweqinvmap (paths_inl_inl_equiv x x')

(** val isInjective_inr : ('a2, ('a1, 'a2) coprod) isInjective **)

let isInjective_inr x x' =
  isweqinvmap (paths_inr_inr_equiv x x')

(** val homotsec_natural :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a1 -> 'a1 -> 'a1
    paths -> 'a2 paths paths **)

let homotsec_natural f g e x _ _ =
  pathsinv0
    (pathscomp0 (f x) (g x) (g x)
      (pathscomp0 (f x) (f x) (g x) (maponpaths f x x Coq_paths_refl) (e x))
      Coq_paths_refl)
    (pathscomp0 (f x) (f x) (g x) (maponpaths f x x Coq_paths_refl) (e x))
    (pathscomp0rid (f x) (g x)
      (pathscomp0 (f x) (f x) (g x) (maponpaths f x x Coq_paths_refl) (e x)))

(** val evalat : 'a1 -> ('a1 -> 'a2) -> 'a2 **)

let evalat t f =
  f t

(** val apfun :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> 'a1 -> 'a1 -> 'a1
    paths -> 'a2 paths **)

let apfun f f' p x _ _ =
  eqtohomot f f' p x

(** val fromemptysec : empty -> 'a1 **)

let fromemptysec _ =
  assert false (* absurd case *)

(** val maponpaths_idpath : ('a1 -> 'a2) -> 'a1 -> 'a2 paths paths **)

let maponpaths_idpath _ _ =
  Coq_paths_refl

(** val cast : __ paths -> 'a1 -> 'a2 **)

let cast x =
  Obj.magic transportf __ __ x

(** val transport_type_path : __ paths -> 'a1 -> 'a2 paths **)

let transport_type_path _ _ =
  Coq_paths_refl

(** val transport_fun_path :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths ->
    'a2 paths -> 'a2 paths paths -> 'a2 paths paths **)

let transport_fun_path f g x _ _ e _ k =
  let k0 =
    internal_paths_rew (maponpaths g x x Coq_paths_refl) k Coq_paths_refl
      (maponpaths_idpath g x)
  in
  let k1 =
    internal_paths_rew (maponpaths f x x Coq_paths_refl) k0 Coq_paths_refl
      (maponpaths_idpath f x)
  in
  internal_paths_rew (pathscomp0 (f x) (g x) (g x) e Coq_paths_refl) k1 e
    (pathscomp0rid (f x) (g x) e)

(** val transportf_pathsinv0' :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths **)

let transportf_pathsinv0' _ _ _ _ _ _ =
  Coq_paths_refl

(** val transport_idfun : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 paths **)

let transport_idfun _ _ _ _ =
  Coq_paths_refl

(** val transport_functions :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1 -> 'a3) -> 'a1
    -> 'a3 paths **)

let transport_functions _ _ _ _ _ =
  Coq_paths_refl

(** val transport_funapp :
    ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a3
    paths **)

let transport_funapp _ _ _ _ _ =
  Coq_paths_refl

(** val helper_A :
    'a2 -> 'a2 -> ('a1 -> 'a3) -> 'a2 paths -> 'a1 -> 'a3 paths **)

let helper_A _ _ _ _ _ =
  Coq_paths_refl

(** val helper_B :
    ('a1 -> 'a2) -> 'a2 -> 'a2 -> ('a1 -> 'a2 paths) -> 'a2 paths -> 'a1 ->
    'a2 paths paths **)

let helper_B _ =
  helper_A

(** val transport_invweq :
    ('a1 -> ('a2, 'a3) weq) -> 'a1 -> 'a1 -> 'a1 paths -> ('a3, 'a2) weq paths **)

let transport_invweq _ _ _ _ =
  Coq_paths_refl

(** val transport_invmap :
    ('a1 -> ('a2, 'a3) weq) -> 'a1 -> 'a1 -> 'a1 paths -> ('a3 -> 'a2) paths **)

let transport_invmap _ _ _ _ =
  Coq_paths_refl

(** val transportf2 : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3 **)

let transportf2 _ _ _ _ z =
  z

(** val transportb2 : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3 **)

let transportb2 _ _ _ _ z' =
  z'

(** val maponpaths_pr1_pr2 :
    ('a1, ('a2, 'a3) total2) total2 -> ('a1, ('a2, 'a3) total2) total2 ->
    ('a1, ('a2, 'a3) total2) total2 paths -> 'a2 paths **)

let maponpaths_pr1_pr2 _ _ _ =
  Coq_paths_refl

(** val transportb_pair :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3 -> ('a2, 'a3) total2 paths **)

let transportb_pair _ _ _ _ _ _ =
  Coq_paths_refl

(** val transportf_total2_const :
    'a2 -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 -> ('a2, 'a3) total2 paths **)

let transportf_total2_const _ _ _ _ _ =
  Coq_paths_refl

(** val isaprop_wma_inhab : ('a1 -> 'a1 isaprop) -> 'a1 isaprop **)

let isaprop_wma_inhab f =
  invproofirrelevance (fun x y -> (Obj.magic f x x y).pr1)

(** val isaprop_wma_inhab' : ('a1 -> 'a1 iscontr) -> 'a1 isaprop **)

let isaprop_wma_inhab' f =
  isaprop_wma_inhab (fun x -> isapropifcontr (f x))

(** val coq_Unnamed_thm :
    hSet -> pr1hSet -> pr1hSet -> pr1hSet paths -> pr1hSet paths -> pr1hSet
    paths paths **)

let coq_Unnamed_thm x x0 y p q =
  (Obj.magic setproperty x x0 y p q).pr1

(** val coq_Unnamed_thm0 :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 isaset -> 'a1 paths paths **)

let coq_Unnamed_thm0 x y p q is =
  (Obj.magic is x y p q).pr1

(** val funset : hSet -> hSet **)

let funset y =
  make_hSet (Obj.magic impredfun (S (S O)) (setproperty y))

(** val eq_equalities_between_pairs :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths ->
    ('a1, 'a2) total2 paths -> 'a1 paths paths -> 'a2 paths paths -> ('a1,
    'a2) total2 paths paths **)

let eq_equalities_between_pairs x y p q h h2 =
  invmaponpathsweq (total2_paths_equiv x y) p q
    (total2_paths_f (pr1weq (total2_paths_equiv x y) p)
      (pr1weq (total2_paths_equiv x y) q) h h2)

(** val total2_reassoc_paths :
    'a1 -> 'a1 -> ('a2, 'a3) total2 -> ('a2, 'a3) total2 -> 'a1 paths -> 'a2
    paths -> 'a3 paths -> ('a2, 'a3) total2 paths **)

let total2_reassoc_paths _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val total2_reassoc_paths' :
    'a1 -> 'a1 -> ('a2, 'a3) total2 -> ('a2, 'a3) total2 -> 'a1 paths -> 'a2
    paths -> 'a3 paths -> ('a2, 'a3) total2 paths **)

let total2_reassoc_paths' _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val invrot :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths **)

let invrot x y p _ _ =
  pathsinv0 (pathsinv0 y x (pathsinv0 x y p)) p (pathsinv0inv0 x y p)

(** val invrot' :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths paths **)

let invrot' x y _ p' _ =
  pathsinv0inv0 y x p'

(** val invrot'rot :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths
    paths paths **)

let invrot'rot _ _ _ _ _ =
  Coq_paths_refl

(** val invrotrot' :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a1 paths
    paths paths **)

let invrotrot' x y p p' e =
  internal_paths_rew
    (pathsinv0 (pathsinv0 y x p') p (pathsinv0 p (pathsinv0 y x p') e))
    Coq_paths_refl e (pathsinv0inv0 p (pathsinv0 y x p') e)

(** val hornRotation_rr :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
    paths, 'a1 paths paths) weq **)

let hornRotation_rr x _ _ p _ _ =
  eqweqmap
    (maponpaths (Obj.magic __) (pathscomp0 x x x p Coq_paths_refl) p
      (pathscomp0rid x x p))

(** val hornRotation_lr :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
    paths, 'a1 paths paths) weq **)

let hornRotation_lr _ _ _ _ _ _ =
  idweq

(** val hornRotation_rl :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
    paths, 'a1 paths paths) weq **)

let hornRotation_rl x _ _ p _ _ =
  eqweqmap
    (maponpaths (Obj.magic __) (pathscomp0 x x x p Coq_paths_refl) p
      (pathscomp0rid x x p))

(** val hornRotation_ll :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> ('a1 paths
    paths, 'a1 paths paths) weq **)

let hornRotation_ll _ _ _ _ _ _ =
  idweq

(** val uniqueFiller :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> ('a1 paths, 'a1 paths
    paths) total2 iscontr **)

let uniqueFiller x y z p q =
  iscontrweqf (weqfibtototal (fun r -> hornRotation_rr x y z p q r))
    (iscontrcoconustot (pathscomp0 x z y p (pathsinv0 y z q)))

(** val fillerEquation :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths
    paths -> ('a1 paths, 'a1 paths paths) total2 paths **)

let fillerEquation x y z p q r k =
  proofirrelevancecontr (uniqueFiller x y z p q) { pr1 = r; pr2 = k } { pr1 =
    (pathscomp0 x z y p (pathsinv0 y z q)); pr2 =
    (pr1weq
      (hornRotation_rr x y z p q (pathscomp0 x z y p (pathsinv0 y z q)))
      Coq_paths_refl) }

(** val isweqpathscomp0r' :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) isweq **)

let isweqpathscomp0r' x x' x'' e' p =
  { pr1 = { pr1 = (pathscomp0 x x'' x' p (pathsinv0 x' x'' e')); pr2 =
    ((hornRotation_rr x x' x'' p e'
       (pathscomp0 x x'' x' p (pathsinv0 x' x'' e'))).pr1 Coq_paths_refl) };
    pr2 = (fun t ->
    let q = t.pr1 in let l = t.pr2 in fillerEquation x x' x'' p e' q l) }

(** val transportPathTotal :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) total2 paths -> 'a3 -> 'a3 **)

let transportPathTotal _ _ _ _ _ x0 =
  x0

(** val inductionOnFiller :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a1 paths -> 'a1
    paths paths -> 'a2 **)

let inductionOnFiller x y z p q t r e =
  transportPathTotal (pathscomp0 x z y p (pathsinv0 y z q)) r
    (pr1weq
      (hornRotation_rr x y z p q (pathscomp0 x z y p (pathsinv0 y z q)))
      Coq_paths_refl) e
    (pathsinv0 { pr1 = r; pr2 = e } { pr1 =
      (pathscomp0 x z y p (pathsinv0 y z q)); pr2 =
      (pr1weq
        (hornRotation_rr x y z p q (pathscomp0 x z y p (pathsinv0 y z q)))
        Coq_paths_refl) } (fillerEquation x y z p q r e)) t

(** val transportf_paths_FlFr :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths ->
    'a2 paths paths **)

let transportf_paths_FlFr f g x1 _ _ q =
  pathsinv0 (pathscomp0 (f x1) (g x1) (g x1) q Coq_paths_refl) q
    (pathscomp0rid (f x1) (g x1) q)

(** val transportf_sec_constant :
    'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a3) -> ('a2 -> 'a3) paths **)

let transportf_sec_constant _ _ _ _ =
  Coq_paths_refl

(** val path_hfp :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3)
    hfp -> 'a1 paths -> 'a2 paths -> 'a3 paths paths -> ('a1, 'a2, 'a3) hfp
    paths **)

let path_hfp f g x y _ _ p_UU2083_ =
  let pr3 = x.pr1 in
  let x_UU2081_ = pr3.pr1 in
  let x_UU2082_ = pr3.pr2 in
  let px = x.pr2 in
  let py = y.pr2 in
  maponpaths (fun x0 -> { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ }; pr2 =
    x0 }) px py
    (pathscomp0 px
      (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px Coq_paths_refl)
      py
      (pathsinv0
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl) px (pathscomp0rid (g x_UU2082_) (f x_UU2081_) px))
      p_UU2083_)

(** val maponpaths_hfpg_path_hfp :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3)
    hfp -> 'a1 paths -> 'a2 paths -> 'a3 paths paths -> 'a1 paths paths **)

let maponpaths_hfpg_path_hfp f g x _ _ _ _ =
  let pr3 = x.pr1 in
  let x_UU2081_ = pr3.pr1 in
  let x_UU2082_ = pr3.pr2 in
  let px = x.pr2 in
  pathscomp0
    (maponpaths (hfpg f g) { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ };
      pr2 = px } { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ }; pr2 =
      (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px Coq_paths_refl) }
      (maponpaths (fun x0 -> { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ };
        pr2 = x0 }) px
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathscomp0 px
          (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
            Coq_paths_refl)
          (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
            Coq_paths_refl)
          (pathsinv0
            (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
              Coq_paths_refl) px
            (pathscomp0rid (g x_UU2082_) (f x_UU2081_) px)) Coq_paths_refl)))
    (maponpaths
      (funcomp (fun x0 -> { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ }; pr2 =
        x0 }) (hfpg f g)) px
      (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px Coq_paths_refl)
      (pathscomp0 px
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathsinv0
          (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
            Coq_paths_refl) px (pathscomp0rid (g x_UU2082_) (f x_UU2081_) px))
        Coq_paths_refl)) Coq_paths_refl
    (maponpathscomp px
      (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px Coq_paths_refl)
      (fun x0 -> { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ }; pr2 = x0 })
      (hfpg f g)
      (pathscomp0 px
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathsinv0
          (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
            Coq_paths_refl) px (pathscomp0rid (g x_UU2082_) (f x_UU2081_) px))
        Coq_paths_refl))
    (maponpaths_for_constant_function x_UU2081_ px
      (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px Coq_paths_refl)
      (pathscomp0 px
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathsinv0
          (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
            Coq_paths_refl) px (pathscomp0rid (g x_UU2082_) (f x_UU2081_) px))
        Coq_paths_refl))

(** val maponpaths_hfpg'_path_hfp :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3)
    hfp -> 'a1 paths -> 'a2 paths -> 'a3 paths paths -> 'a2 paths paths **)

let maponpaths_hfpg'_path_hfp f g x _ _ _ _ =
  let pr3 = x.pr1 in
  let x_UU2081_ = pr3.pr1 in
  let x_UU2082_ = pr3.pr2 in
  let px = x.pr2 in
  pathscomp0
    (maponpaths (hfpg' f g) { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ };
      pr2 = px } { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ }; pr2 =
      (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px Coq_paths_refl) }
      (maponpaths (fun x0 -> { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ };
        pr2 = x0 }) px
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathscomp0 px
          (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
            Coq_paths_refl)
          (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
            Coq_paths_refl)
          (pathsinv0
            (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
              Coq_paths_refl) px
            (pathscomp0rid (g x_UU2082_) (f x_UU2081_) px)) Coq_paths_refl)))
    (maponpaths
      (funcomp (fun x0 -> { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ }; pr2 =
        x0 }) (hfpg' f g)) px
      (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px Coq_paths_refl)
      (pathscomp0 px
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathsinv0
          (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
            Coq_paths_refl) px (pathscomp0rid (g x_UU2082_) (f x_UU2081_) px))
        Coq_paths_refl)) Coq_paths_refl
    (maponpathscomp px
      (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px Coq_paths_refl)
      (fun x0 -> { pr1 = { pr1 = x_UU2081_; pr2 = x_UU2082_ }; pr2 = x0 })
      (hfpg' f g)
      (pathscomp0 px
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathsinv0
          (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
            Coq_paths_refl) px (pathscomp0rid (g x_UU2082_) (f x_UU2081_) px))
        Coq_paths_refl))
    (maponpaths_for_constant_function x_UU2082_ px
      (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px Coq_paths_refl)
      (pathscomp0 px
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
          Coq_paths_refl)
        (pathsinv0
          (pathscomp0 (g x_UU2082_) (f x_UU2081_) (f x_UU2081_) px
            Coq_paths_refl) px (pathscomp0rid (g x_UU2082_) (f x_UU2081_) px))
        Coq_paths_refl))

(** val path_hfp_eta :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3)
    hfp -> ('a1, 'a2, 'a3) hfp paths -> ('a1, 'a2, 'a3) hfp paths paths **)

let path_hfp_eta f g x _ _ =
  pathsinv0
    (maponpaths (fun x0 -> { pr1 = { pr1 = x.pr1.pr1; pr2 = x.pr1.pr2 };
      pr2 = x0 }) x.pr2 x.pr2
      (pathscomp0 x.pr2
        (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
          Coq_paths_refl) x.pr2
        (pathsinv0
          (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
            Coq_paths_refl) x.pr2
          (pathscomp0rid (g x.pr1.pr2) (f x.pr1.pr1) x.pr2))
        (pathscomp0
          (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g x))
            (commhfp f g x) Coq_paths_refl) (commhfp f g x) (commhfp f g x)
          (pathsinv0 (commhfp f g x)
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g x))
              (commhfp f g x) Coq_paths_refl)
            (pathsinv0
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g x))
                (commhfp f g x) Coq_paths_refl) (commhfp f g x)
              (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x))
                (commhfp f g x)))) Coq_paths_refl))) Coq_paths_refl
    (pathscomp0
      (maponpaths (fun x0 -> { pr1 = { pr1 = x.pr1.pr1; pr2 = x.pr1.pr2 };
        pr2 = x0 }) x.pr2 x.pr2
        (pathscomp0 x.pr2
          (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
            Coq_paths_refl) x.pr2
          (pathsinv0
            (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
              Coq_paths_refl) x.pr2
            (pathscomp0rid (g x.pr1.pr2) (f x.pr1.pr1) x.pr2))
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g x))
              (commhfp f g x) Coq_paths_refl) (commhfp f g x) (commhfp f g x)
            (pathsinv0 (commhfp f g x)
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g x))
                (commhfp f g x) Coq_paths_refl)
              (pathsinv0
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                (commhfp f g x)
                (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x))
                  (commhfp f g x)))) Coq_paths_refl)))
      (maponpaths (fun x0 -> { pr1 = { pr1 = x.pr1.pr1; pr2 = x.pr1.pr2 };
        pr2 = x0 }) x.pr2 x.pr2 Coq_paths_refl) Coq_paths_refl
      (maponpaths
        (maponpaths (fun x0 -> { pr1 = { pr1 = x.pr1.pr1; pr2 = x.pr1.pr2 };
          pr2 = x0 }) x.pr2 x.pr2)
        (pathscomp0 x.pr2
          (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
            Coq_paths_refl) x.pr2
          (pathsinv0
            (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
              Coq_paths_refl) x.pr2
            (pathscomp0rid (g x.pr1.pr2) (f x.pr1.pr1) x.pr2))
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g x))
              (commhfp f g x) Coq_paths_refl) (commhfp f g x) (commhfp f g x)
            (pathsinv0 (commhfp f g x)
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g x))
                (commhfp f g x) Coq_paths_refl)
              (pathsinv0
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                (commhfp f g x)
                (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x))
                  (commhfp f g x)))) Coq_paths_refl)) Coq_paths_refl
        (pathscomp0
          (pathscomp0 x.pr2
            (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
              Coq_paths_refl) x.pr2
            (pathsinv0
              (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
                Coq_paths_refl) x.pr2
              (pathscomp0rid (g x.pr1.pr2) (f x.pr1.pr1) x.pr2))
            (pathscomp0
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g x))
                (commhfp f g x) Coq_paths_refl) (commhfp f g x)
              (commhfp f g x)
              (pathsinv0 (commhfp f g x)
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                (pathsinv0
                  (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                    (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                  (commhfp f g x)
                  (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x))
                    (commhfp f g x)))) Coq_paths_refl))
          (pathscomp0 x.pr2
            (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
              Coq_paths_refl) x.pr2
            (pathsinv0
              (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
                Coq_paths_refl) x.pr2
              (pathscomp0rid (g x.pr1.pr2) (f x.pr1.pr1) x.pr2))
            (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x)) (commhfp f g x)))
          Coq_paths_refl
          (maponpaths
            (pathscomp0 x.pr2
              (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
                Coq_paths_refl) x.pr2
              (pathsinv0
                (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
                  Coq_paths_refl) x.pr2
                (pathscomp0rid (g x.pr1.pr2) (f x.pr1.pr1) x.pr2)))
            (pathscomp0
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g x))
                (commhfp f g x) Coq_paths_refl) (commhfp f g x)
              (commhfp f g x)
              (pathsinv0 (commhfp f g x)
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                (pathsinv0
                  (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                    (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                  (commhfp f g x)
                  (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x))
                    (commhfp f g x)))) Coq_paths_refl)
            (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x)) (commhfp f g x))
            (pathscomp0
              (pathscomp0
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                (commhfp f g x) (commhfp f g x)
                (pathsinv0 (commhfp f g x)
                  (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                    (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                  (pathsinv0
                    (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                      (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                    (commhfp f g x)
                    (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x))
                      (commhfp f g x)))) Coq_paths_refl)
              (pathsinv0 (commhfp f g x)
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                (pathsinv0
                  (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                    (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                  (commhfp f g x)
                  (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x))
                    (commhfp f g x))))
              (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x))
                (commhfp f g x))
              (pathscomp0rid
                (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
                  Coq_paths_refl) x.pr2
                (pathsinv0 (commhfp f g x)
                  (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                    (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                  (pathsinv0
                    (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                      (f (hfpg f g x)) (commhfp f g x) Coq_paths_refl)
                    (commhfp f g x)
                    (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x))
                      (commhfp f g x)))))
              (pathsinv0inv0
                (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
                  Coq_paths_refl) x.pr2
                (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x))
                  (commhfp f g x)))))
          (pathsinv0l
            (pathscomp0 (g x.pr1.pr2) (f x.pr1.pr1) (f x.pr1.pr1) x.pr2
              Coq_paths_refl) x.pr2
            (pathscomp0rid (g (hfpg' f g x)) (f (hfpg f g x)) (commhfp f g x)))))
      Coq_paths_refl)

(** val homot_hfp :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3)
    hfp -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 paths -> 'a2
    paths -> 'a2 paths paths -> 'a3 paths paths -> ('a1, 'a2, 'a3) hfp paths
    paths **)

let homot_hfp f g x y h_UU2081_ _ _ h_UU2082_ _ _ h_UU2083_ =
  maponpaths (path_hfp f g x y h_UU2081_ h_UU2082_) h_UU2083_
    (pathscomp0
      (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
        (commhfp f g x) (maponpaths f (hfpg f g x) (hfpg f g y) h_UU2081_))
      (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
        (maponpaths g (hfpg' f g x) (hfpg' f g y) h_UU2082_) (commhfp f g y))
      (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
        (maponpaths g (hfpg' f g x) (hfpg' f g y) h_UU2082_) (commhfp f g y))
      h_UU2083_ Coq_paths_refl)
    (pathsinv0
      (pathscomp0
        (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
          (commhfp f g x) (maponpaths f (hfpg f g x) (hfpg f g y) h_UU2081_))
        (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
          (maponpaths g (hfpg' f g x) (hfpg' f g y) h_UU2082_)
          (commhfp f g y))
        (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
          (maponpaths g (hfpg' f g x) (hfpg' f g y) h_UU2082_)
          (commhfp f g y)) h_UU2083_ Coq_paths_refl) h_UU2083_
      (pathscomp0rid
        (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
          (commhfp f g x) (maponpaths f (hfpg f g x) (hfpg f g y) h_UU2081_))
        (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
          (maponpaths g (hfpg' f g x) (hfpg' f g y) h_UU2082_)
          (commhfp f g y)) h_UU2083_))

(** val homot_hfp_one_type :
    'a3 isofhlevel -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp ->
    ('a1, 'a2, 'a3) hfp -> ('a1, 'a2, 'a3) hfp paths -> ('a1, 'a2, 'a3) hfp
    paths -> 'a1 paths paths -> 'a2 paths paths -> ('a1, 'a2, 'a3) hfp paths
    paths **)

let homot_hfp_one_type hZ f g x y p q r_UU2081_ r_UU2082_ =
  pathscomp0 p
    (path_hfp f g x y (maponpaths (hfpg f g) x y p)
      (maponpaths (hfpg' f g) x y p)
      (pathscomp0
        (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
          (commhfp f g x)
          (maponpaths f (hfpg f g x) (hfpg f g y)
            (maponpaths (hfpg f g) x y p)))
        (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
          (commhfp f g x) (maponpaths (funcomp (hfpg f g) f) x y p))
        (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
          (maponpaths g (hfpg' f g x) (hfpg' f g y)
            (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
        (maponpaths (fun z ->
          pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
            (commhfp f g x) z)
          (maponpaths f (hfpg f g x) (hfpg f g y)
            (maponpaths (hfpg f g) x y p))
          (maponpaths (funcomp (hfpg f g) f) x y p)
          (maponpathscomp x y (hfpg f g) f p))
        (pathscomp0
          (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
            (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y p))
          (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
            (maponpaths (fun z -> g (hfpg' f g z)) x y p) (commhfp f g y))
          (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
            (maponpaths g (hfpg' f g x) (hfpg' f g y)
              (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
          (pathsinv0
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths (fun z -> g (hfpg' f g z)) x y p) (commhfp f g y))
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y p))
            (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
              f (hfpg f g z)) (commhfp f g) x y p))
          (maponpaths (fun z ->
            pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y)) z
              (commhfp f g y)) (maponpaths (funcomp (hfpg' f g) g) x y p)
            (maponpaths g (hfpg' f g x) (hfpg' f g y)
              (maponpaths (hfpg' f g) x y p))
            (pathsinv0
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y p))
              (maponpaths (funcomp (hfpg' f g) g) x y p)
              (maponpathscomp x y (hfpg' f g) g p)))))) q
    (path_hfp_eta f g x y p)
    (pathscomp0
      (path_hfp f g x y (maponpaths (hfpg f g) x y p)
        (maponpaths (hfpg' f g) x y p)
        (pathscomp0
          (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
            (commhfp f g x)
            (maponpaths f (hfpg f g x) (hfpg f g y)
              (maponpaths (hfpg f g) x y p)))
          (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
            (commhfp f g x) (maponpaths (funcomp (hfpg f g) f) x y p))
          (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
            (maponpaths g (hfpg' f g x) (hfpg' f g y)
              (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
          (maponpaths (fun z ->
            pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x) z)
            (maponpaths f (hfpg f g x) (hfpg f g y)
              (maponpaths (hfpg f g) x y p))
            (maponpaths (funcomp (hfpg f g) f) x y p)
            (maponpathscomp x y (hfpg f g) f p))
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y p))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths (fun z -> g (hfpg' f g z)) x y p) (commhfp f g y))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
            (pathsinv0
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths (fun z -> g (hfpg' f g z)) x y p) (commhfp f g y))
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y p))
              (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                f (hfpg f g z)) (commhfp f g) x y p))
            (maponpaths (fun z ->
              pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
                z (commhfp f g y)) (maponpaths (funcomp (hfpg' f g) g) x y p)
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y p))
              (pathsinv0
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y p))
                (maponpaths (funcomp (hfpg' f g) g) x y p)
                (maponpathscomp x y (hfpg' f g) g p))))))
      (path_hfp f g x y (maponpaths (hfpg f g) x y q)
        (maponpaths (hfpg' f g) x y q)
        (pathscomp0
          (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
            (commhfp f g x)
            (maponpaths f (hfpg f g x) (hfpg f g y)
              (maponpaths (hfpg f g) x y q)))
          (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
            (commhfp f g x) (maponpaths (funcomp (hfpg f g) f) x y q))
          (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
            (maponpaths g (hfpg' f g x) (hfpg' f g y)
              (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
          (maponpaths (fun z ->
            pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x) z)
            (maponpaths f (hfpg f g x) (hfpg f g y)
              (maponpaths (hfpg f g) x y q))
            (maponpaths (funcomp (hfpg f g) f) x y q)
            (maponpathscomp x y (hfpg f g) f q))
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y q))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths (fun z -> g (hfpg' f g z)) x y q) (commhfp f g y))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
            (pathsinv0
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths (fun z -> g (hfpg' f g z)) x y q) (commhfp f g y))
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y q))
              (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                f (hfpg f g z)) (commhfp f g) x y q))
            (maponpaths (fun z ->
              pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
                z (commhfp f g y)) (maponpaths (funcomp (hfpg' f g) g) x y q)
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y q))
              (pathsinv0
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y q))
                (maponpaths (funcomp (hfpg' f g) g) x y q)
                (maponpathscomp x y (hfpg' f g) g q)))))) q
      (pathscomp0
        (path_hfp f g x y (maponpaths (hfpg f g) x y p)
          (maponpaths (hfpg' f g) x y p)
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y p)))
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x) (maponpaths (funcomp (hfpg f g) f) x y p))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
            (maponpaths (fun z ->
              pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) z)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y p))
              (maponpaths (funcomp (hfpg f g) f) x y p)
              (maponpathscomp x y (hfpg f g) f p))
            (pathscomp0
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y p))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths (fun z -> g (hfpg' f g z)) x y p) (commhfp f g y))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
              (pathsinv0
                (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y))
                  (maponpaths (fun z -> g (hfpg' f g z)) x y p)
                  (commhfp f g y))
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g y)) (commhfp f g x)
                  (maponpaths (fun z -> f (hfpg f g z)) x y p))
                (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                  f (hfpg f g z)) (commhfp f g) x y p))
              (maponpaths (fun z ->
                pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y)) z (commhfp f g y))
                (maponpaths (funcomp (hfpg' f g) g) x y p)
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y p))
                (pathsinv0
                  (maponpaths g (hfpg' f g x) (hfpg' f g y)
                    (maponpaths (hfpg' f g) x y p))
                  (maponpaths (funcomp (hfpg' f g) g) x y p)
                  (maponpathscomp x y (hfpg' f g) g p))))))
        (path_hfp f g x y (maponpaths (hfpg f g) x y q)
          (maponpaths (hfpg' f g) x y q)
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y q)))
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y p)))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
            (maponpaths (fun z ->
              pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) (maponpaths f (hfpg f g x) (hfpg f g y) z))
              (maponpaths (hfpg f g) x y q) (maponpaths (hfpg f g) x y p)
              (pathsinv0 (maponpaths (hfpg f g) x y p)
                (maponpaths (hfpg f g) x y q) r_UU2081_))
            (pathscomp0
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x)
                (maponpaths f (hfpg f g x) (hfpg f g y)
                  (maponpaths (hfpg f g) x y p)))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
              (pathscomp0
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g y)) (commhfp f g x)
                  (maponpaths f (hfpg f g x) (hfpg f g y)
                    (maponpaths (hfpg f g) x y p)))
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g y)) (commhfp f g x)
                  (maponpaths (funcomp (hfpg f g) f) x y p))
                (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y))
                  (maponpaths g (hfpg' f g x) (hfpg' f g y)
                    (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
                (maponpaths (fun z ->
                  pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                    (f (hfpg f g y)) (commhfp f g x) z)
                  (maponpaths f (hfpg f g x) (hfpg f g y)
                    (maponpaths (hfpg f g) x y p))
                  (maponpaths (funcomp (hfpg f g) f) x y p)
                  (maponpathscomp x y (hfpg f g) f p))
                (pathscomp0
                  (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                    (f (hfpg f g y)) (commhfp f g x)
                    (maponpaths (fun z -> f (hfpg f g z)) x y p))
                  (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                    (f (hfpg f g y))
                    (maponpaths (fun z -> g (hfpg' f g z)) x y p)
                    (commhfp f g y))
                  (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                    (f (hfpg f g y))
                    (maponpaths g (hfpg' f g x) (hfpg' f g y)
                      (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
                  (pathsinv0
                    (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                      (f (hfpg f g y))
                      (maponpaths (fun z -> g (hfpg' f g z)) x y p)
                      (commhfp f g y))
                    (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                      (f (hfpg f g y)) (commhfp f g x)
                      (maponpaths (fun z -> f (hfpg f g z)) x y p))
                    (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                      f (hfpg f g z)) (commhfp f g) x y p))
                  (maponpaths (fun z ->
                    pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                      (f (hfpg f g y)) z (commhfp f g y))
                    (maponpaths (funcomp (hfpg' f g) g) x y p)
                    (maponpaths g (hfpg' f g x) (hfpg' f g y)
                      (maponpaths (hfpg' f g) x y p))
                    (pathsinv0
                      (maponpaths g (hfpg' f g x) (hfpg' f g y)
                        (maponpaths (hfpg' f g) x y p))
                      (maponpaths (funcomp (hfpg' f g) g) x y p)
                      (maponpathscomp x y (hfpg' f g) g p)))))
              (maponpaths (fun z ->
                pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y))
                  (maponpaths g (hfpg' f g x) (hfpg' f g y) z) (commhfp f g y))
                (maponpaths (hfpg' f g) x y p) (maponpaths (hfpg' f g) x y q)
                r_UU2082_))))
        (path_hfp f g x y (maponpaths (hfpg f g) x y q)
          (maponpaths (hfpg' f g) x y q)
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y q)))
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x) (maponpaths (funcomp (hfpg f g) f) x y q))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
            (maponpaths (fun z ->
              pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) z)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y q))
              (maponpaths (funcomp (hfpg f g) f) x y q)
              (maponpathscomp x y (hfpg f g) f q))
            (pathscomp0
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y q))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths (fun z -> g (hfpg' f g z)) x y q) (commhfp f g y))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
              (pathsinv0
                (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y))
                  (maponpaths (fun z -> g (hfpg' f g z)) x y q)
                  (commhfp f g y))
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g y)) (commhfp f g x)
                  (maponpaths (fun z -> f (hfpg f g z)) x y q))
                (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                  f (hfpg f g z)) (commhfp f g) x y q))
              (maponpaths (fun z ->
                pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y)) z (commhfp f g y))
                (maponpaths (funcomp (hfpg' f g) g) x y q)
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y q))
                (pathsinv0
                  (maponpaths g (hfpg' f g x) (hfpg' f g y)
                    (maponpaths (hfpg' f g) x y q))
                  (maponpaths (funcomp (hfpg' f g) g) x y q)
                  (maponpathscomp x y (hfpg' f g) g q))))))
        (homot_hfp f g x y (maponpaths (hfpg f g) x y p)
          (maponpaths (hfpg f g) x y q) r_UU2081_
          (maponpaths (hfpg' f g) x y p) (maponpaths (hfpg' f g) x y q)
          r_UU2082_
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y p)))
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x) (maponpaths (funcomp (hfpg f g) f) x y p))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
            (maponpaths (fun z ->
              pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) z)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y p))
              (maponpaths (funcomp (hfpg f g) f) x y p)
              (maponpathscomp x y (hfpg f g) f p))
            (pathscomp0
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y p))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths (fun z -> g (hfpg' f g z)) x y p) (commhfp f g y))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
              (pathsinv0
                (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y))
                  (maponpaths (fun z -> g (hfpg' f g z)) x y p)
                  (commhfp f g y))
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g y)) (commhfp f g x)
                  (maponpaths (fun z -> f (hfpg f g z)) x y p))
                (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                  f (hfpg f g z)) (commhfp f g) x y p))
              (maponpaths (fun z ->
                pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y)) z (commhfp f g y))
                (maponpaths (funcomp (hfpg' f g) g) x y p)
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y p))
                (pathsinv0
                  (maponpaths g (hfpg' f g x) (hfpg' f g y)
                    (maponpaths (hfpg' f g) x y p))
                  (maponpaths (funcomp (hfpg' f g) g) x y p)
                  (maponpathscomp x y (hfpg' f g) g p))))))
        (maponpaths
          (path_hfp f g x y (maponpaths (hfpg f g) x y q)
            (maponpaths (hfpg' f g) x y q))
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y q)))
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y p)))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
            (maponpaths (fun z ->
              pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) (maponpaths f (hfpg f g x) (hfpg f g y) z))
              (maponpaths (hfpg f g) x y q) (maponpaths (hfpg f g) x y p)
              (pathsinv0 (maponpaths (hfpg f g) x y p)
                (maponpaths (hfpg f g) x y q) r_UU2081_))
            (pathscomp0
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x)
                (maponpaths f (hfpg f g x) (hfpg f g y)
                  (maponpaths (hfpg f g) x y p)))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
              (pathscomp0
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g y)) (commhfp f g x)
                  (maponpaths f (hfpg f g x) (hfpg f g y)
                    (maponpaths (hfpg f g) x y p)))
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g y)) (commhfp f g x)
                  (maponpaths (funcomp (hfpg f g) f) x y p))
                (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y))
                  (maponpaths g (hfpg' f g x) (hfpg' f g y)
                    (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
                (maponpaths (fun z ->
                  pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                    (f (hfpg f g y)) (commhfp f g x) z)
                  (maponpaths f (hfpg f g x) (hfpg f g y)
                    (maponpaths (hfpg f g) x y p))
                  (maponpaths (funcomp (hfpg f g) f) x y p)
                  (maponpathscomp x y (hfpg f g) f p))
                (pathscomp0
                  (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                    (f (hfpg f g y)) (commhfp f g x)
                    (maponpaths (fun z -> f (hfpg f g z)) x y p))
                  (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                    (f (hfpg f g y))
                    (maponpaths (fun z -> g (hfpg' f g z)) x y p)
                    (commhfp f g y))
                  (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                    (f (hfpg f g y))
                    (maponpaths g (hfpg' f g x) (hfpg' f g y)
                      (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
                  (pathsinv0
                    (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                      (f (hfpg f g y))
                      (maponpaths (fun z -> g (hfpg' f g z)) x y p)
                      (commhfp f g y))
                    (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                      (f (hfpg f g y)) (commhfp f g x)
                      (maponpaths (fun z -> f (hfpg f g z)) x y p))
                    (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                      f (hfpg f g z)) (commhfp f g) x y p))
                  (maponpaths (fun z ->
                    pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                      (f (hfpg f g y)) z (commhfp f g y))
                    (maponpaths (funcomp (hfpg' f g) g) x y p)
                    (maponpaths g (hfpg' f g x) (hfpg' f g y)
                      (maponpaths (hfpg' f g) x y p))
                    (pathsinv0
                      (maponpaths g (hfpg' f g x) (hfpg' f g y)
                        (maponpaths (hfpg' f g) x y p))
                      (maponpaths (funcomp (hfpg' f g) g) x y p)
                      (maponpathscomp x y (hfpg' f g) g p)))))
              (maponpaths (fun z ->
                pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y))
                  (maponpaths g (hfpg' f g x) (hfpg' f g y) z) (commhfp f g y))
                (maponpaths (hfpg' f g) x y p) (maponpaths (hfpg' f g) x y q)
                r_UU2082_)))
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y q)))
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x) (maponpaths (funcomp (hfpg f g) f) x y q))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
            (maponpaths (fun z ->
              pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) z)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y q))
              (maponpaths (funcomp (hfpg f g) f) x y q)
              (maponpathscomp x y (hfpg f g) f q))
            (pathscomp0
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y q))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths (fun z -> g (hfpg' f g z)) x y q) (commhfp f g y))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
              (pathsinv0
                (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y))
                  (maponpaths (fun z -> g (hfpg' f g z)) x y q)
                  (commhfp f g y))
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g y)) (commhfp f g x)
                  (maponpaths (fun z -> f (hfpg f g z)) x y q))
                (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                  f (hfpg f g z)) (commhfp f g) x y q))
              (maponpaths (fun z ->
                pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y)) z (commhfp f g y))
                (maponpaths (funcomp (hfpg' f g) g) x y q)
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y q))
                (pathsinv0
                  (maponpaths g (hfpg' f g x) (hfpg' f g y)
                    (maponpaths (hfpg' f g) x y q))
                  (maponpaths (funcomp (hfpg' f g) g) x y q)
                  (maponpathscomp x y (hfpg' f g) g q)))))
          (let x0 = g (hfpg' f g x) in
           let x' = f (hfpg f g y) in
           let x1 =
             pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
               (commhfp f g x)
               (maponpaths f (hfpg f g x) (hfpg f g y)
                 (maponpaths (hfpg f g) x y q))
           in
           let x'0 =
             pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
               (maponpaths g (hfpg' f g x) (hfpg' f g y)
                 (maponpaths (hfpg' f g) x y q)) (commhfp f g y)
           in
           let x2 =
             pathscomp0
               (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                 (f (hfpg f g y)) (commhfp f g x)
                 (maponpaths f (hfpg f g x) (hfpg f g y)
                   (maponpaths (hfpg f g) x y q)))
               (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                 (f (hfpg f g y)) (commhfp f g x)
                 (maponpaths f (hfpg f g x) (hfpg f g y)
                   (maponpaths (hfpg f g) x y p)))
               (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                 (f (hfpg f g y))
                 (maponpaths g (hfpg' f g x) (hfpg' f g y)
                   (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
               (maponpaths (fun z ->
                 pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                   (f (hfpg f g y)) (commhfp f g x)
                   (maponpaths f (hfpg f g x) (hfpg f g y) z))
                 (maponpaths (hfpg f g) x y q) (maponpaths (hfpg f g) x y p)
                 (pathsinv0 (maponpaths (hfpg f g) x y p)
                   (maponpaths (hfpg f g) x y q) r_UU2081_))
               (pathscomp0
                 (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                   (f (hfpg f g y)) (commhfp f g x)
                   (maponpaths f (hfpg f g x) (hfpg f g y)
                     (maponpaths (hfpg f g) x y p)))
                 (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                   (f (hfpg f g y))
                   (maponpaths g (hfpg' f g x) (hfpg' f g y)
                     (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
                 (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                   (f (hfpg f g y))
                   (maponpaths g (hfpg' f g x) (hfpg' f g y)
                     (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
                 (pathscomp0
                   (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                     (f (hfpg f g y)) (commhfp f g x)
                     (maponpaths f (hfpg f g x) (hfpg f g y)
                       (maponpaths (hfpg f g) x y p)))
                   (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                     (f (hfpg f g y)) (commhfp f g x)
                     (maponpaths (funcomp (hfpg f g) f) x y p))
                   (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                     (f (hfpg f g y))
                     (maponpaths g (hfpg' f g x) (hfpg' f g y)
                       (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
                   (maponpaths (fun z ->
                     pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                       (f (hfpg f g y)) (commhfp f g x) z)
                     (maponpaths f (hfpg f g x) (hfpg f g y)
                       (maponpaths (hfpg f g) x y p))
                     (maponpaths (funcomp (hfpg f g) f) x y p)
                     (maponpathscomp x y (hfpg f g) f p))
                   (pathscomp0
                     (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                       (f (hfpg f g y)) (commhfp f g x)
                       (maponpaths (fun z -> f (hfpg f g z)) x y p))
                     (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                       (f (hfpg f g y))
                       (maponpaths (fun z -> g (hfpg' f g z)) x y p)
                       (commhfp f g y))
                     (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                       (f (hfpg f g y))
                       (maponpaths g (hfpg' f g x) (hfpg' f g y)
                         (maponpaths (hfpg' f g) x y p)) (commhfp f g y))
                     (pathsinv0
                       (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                         (f (hfpg f g y))
                         (maponpaths (fun z -> g (hfpg' f g z)) x y p)
                         (commhfp f g y))
                       (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                         (f (hfpg f g y)) (commhfp f g x)
                         (maponpaths (fun z -> f (hfpg f g z)) x y p))
                       (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                         f (hfpg f g z)) (commhfp f g) x y p))
                     (maponpaths (fun z ->
                       pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                         (f (hfpg f g y)) z (commhfp f g y))
                       (maponpaths (funcomp (hfpg' f g) g) x y p)
                       (maponpaths g (hfpg' f g x) (hfpg' f g y)
                         (maponpaths (hfpg' f g) x y p))
                       (pathsinv0
                         (maponpaths g (hfpg' f g x) (hfpg' f g y)
                           (maponpaths (hfpg' f g) x y p))
                         (maponpaths (funcomp (hfpg' f g) g) x y p)
                         (maponpathscomp x y (hfpg' f g) g p)))))
                 (maponpaths (fun z ->
                   pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                     (f (hfpg f g y))
                     (maponpaths g (hfpg' f g x) (hfpg' f g y) z)
                     (commhfp f g y)) (maponpaths (hfpg' f g) x y p)
                   (maponpaths (hfpg' f g) x y q) r_UU2082_))
           in
           let x'1 =
             pathscomp0
               (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                 (f (hfpg f g y)) (commhfp f g x)
                 (maponpaths f (hfpg f g x) (hfpg f g y)
                   (maponpaths (hfpg f g) x y q)))
               (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                 (f (hfpg f g y)) (commhfp f g x)
                 (maponpaths (funcomp (hfpg f g) f) x y q))
               (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                 (f (hfpg f g y))
                 (maponpaths g (hfpg' f g x) (hfpg' f g y)
                   (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
               (maponpaths (fun z ->
                 pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                   (f (hfpg f g y)) (commhfp f g x) z)
                 (maponpaths f (hfpg f g x) (hfpg f g y)
                   (maponpaths (hfpg f g) x y q))
                 (maponpaths (funcomp (hfpg f g) f) x y q)
                 (maponpathscomp x y (hfpg f g) f q))
               (pathscomp0
                 (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                   (f (hfpg f g y)) (commhfp f g x)
                   (maponpaths (fun z -> f (hfpg f g z)) x y q))
                 (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                   (f (hfpg f g y))
                   (maponpaths (fun z -> g (hfpg' f g z)) x y q)
                   (commhfp f g y))
                 (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                   (f (hfpg f g y))
                   (maponpaths g (hfpg' f g x) (hfpg' f g y)
                     (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
                 (pathsinv0
                   (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                     (f (hfpg f g y))
                     (maponpaths (fun z -> g (hfpg' f g z)) x y q)
                     (commhfp f g y))
                   (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                     (f (hfpg f g y)) (commhfp f g x)
                     (maponpaths (fun z -> f (hfpg f g z)) x y q))
                   (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                     f (hfpg f g z)) (commhfp f g) x y q))
                 (maponpaths (fun z ->
                   pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                     (f (hfpg f g y)) z (commhfp f g y))
                   (maponpaths (funcomp (hfpg' f g) g) x y q)
                   (maponpaths g (hfpg' f g x) (hfpg' f g y)
                     (maponpaths (hfpg' f g) x y q))
                   (pathsinv0
                     (maponpaths g (hfpg' f g x) (hfpg' f g y)
                       (maponpaths (hfpg' f g) x y q))
                     (maponpaths (funcomp (hfpg' f g) g) x y q)
                     (maponpathscomp x y (hfpg' f g) g q))))
           in
           (Obj.magic hZ x0 x' x1 x'0 x2 x'1).pr1)))
      (pathsinv0 q
        (path_hfp f g x y (maponpaths (hfpg f g) x y q)
          (maponpaths (hfpg' f g) x y q)
          (pathscomp0
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y q)))
            (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
              (commhfp f g x) (maponpaths (funcomp (hfpg f g) f) x y q))
            (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y)) (f (hfpg f g y))
              (maponpaths g (hfpg' f g x) (hfpg' f g y)
                (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
            (maponpaths (fun z ->
              pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) z)
              (maponpaths f (hfpg f g x) (hfpg f g y)
                (maponpaths (hfpg f g) x y q))
              (maponpaths (funcomp (hfpg f g) f) x y q)
              (maponpathscomp x y (hfpg f g) f q))
            (pathscomp0
              (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x)) (f (hfpg f g y))
                (commhfp f g x) (maponpaths (fun z -> f (hfpg f g z)) x y q))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths (fun z -> g (hfpg' f g z)) x y q) (commhfp f g y))
              (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                (f (hfpg f g y))
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y q)) (commhfp f g y))
              (pathsinv0
                (pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y))
                  (maponpaths (fun z -> g (hfpg' f g z)) x y q)
                  (commhfp f g y))
                (pathscomp0 (g (hfpg' f g x)) (f (hfpg f g x))
                  (f (hfpg f g y)) (commhfp f g x)
                  (maponpaths (fun z -> f (hfpg f g z)) x y q))
                (homotsec_natural (fun z -> g (hfpg' f g z)) (fun z ->
                  f (hfpg f g z)) (commhfp f g) x y q))
              (maponpaths (fun z ->
                pathscomp0 (g (hfpg' f g x)) (g (hfpg' f g y))
                  (f (hfpg f g y)) z (commhfp f g y))
                (maponpaths (funcomp (hfpg' f g) g) x y q)
                (maponpaths g (hfpg' f g x) (hfpg' f g y)
                  (maponpaths (hfpg' f g) x y q))
                (pathsinv0
                  (maponpaths g (hfpg' f g x) (hfpg' f g y)
                    (maponpaths (hfpg' f g) x y q))
                  (maponpaths (funcomp (hfpg' f g) g) x y q)
                  (maponpathscomp x y (hfpg' f g) g q))))))
        (path_hfp_eta f g x y q)))

(** val hfp_is_of_hlevel :
    nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> 'a3 isofhlevel -> ('a1 -> 'a3)
    -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp isofhlevel **)

let hfp_is_of_hlevel n hX hY hZ f g =
  isofhleveltotal2 n (isofhleveldirprod n hX hY) (fun x ->
    Obj.magic hlevelntosn n hZ (g x.pr2) (f x.pr1))

(** val hfp_HLevel :
    nat -> coq_HLevel -> coq_HLevel -> coq_HLevel -> (__ -> __) -> (__ -> __)
    -> coq_HLevel **)

let hfp_HLevel n x y z f g =
  { pr1 = __; pr2 = (hfp_is_of_hlevel n x.pr2 y.pr2 z.pr2 f g) }

(** val transportf_total2_paths_f :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a3 -> 'a3 paths **)

let transportf_total2_paths_f _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val maponpaths_pr1_pathsdirprod :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a1 paths paths **)

let maponpaths_pr1_pathsdirprod _ _ _ _ _ _ =
  Coq_paths_refl

(** val maponpaths_pr2_pathsdirprod :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths **)

let maponpaths_pr2_pathsdirprod _ _ _ _ _ _ =
  Coq_paths_refl

(** val pathsdirprod_eta :
    ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod paths ->
    ('a1, 'a2) dirprod paths paths **)

let pathsdirprod_eta _ _ _ =
  Coq_paths_refl

(** val paths_pathsdirprod :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a2 paths -> 'a2
    paths -> 'a1 paths paths -> 'a2 paths paths -> ('a1, 'a2) dirprod paths
    paths **)

let paths_pathsdirprod _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val app_fun : ('a1 -> 'a2, 'a1) dirprod -> 'a2 **)

let app_fun fx =
  fx.pr1 fx.pr2

(** val app_homot :
    ('a2 -> 'a1 -> 'a3) -> ('a2 -> 'a1 -> 'a3) -> (('a2, 'a1) dirprod -> 'a3
    paths) -> 'a2 -> ('a1 -> 'a3) paths **)

let app_homot f g p y =
  Obj.magic funextsec (fun x -> Obj.magic f y x) (fun x -> Obj.magic g y x)
    (fun x -> Obj.magic p { pr1 = y; pr2 = x })

(** val maponpaths_app_fun :
    ('a1 -> 'a2, 'a1) dirprod -> ('a1 -> 'a2, 'a1) dirprod -> ('a1 -> 'a2,
    'a1) dirprod paths -> 'a2 paths paths **)

let maponpaths_app_fun _ _ _ =
  Coq_paths_refl

(** val dirprod_with_prop : 'a1 isaprop -> (('a1, 'a1) dirprod, 'a1) weq **)

let dirprod_with_prop isa =
  weqpr1 (iscontraprop1 isa)

(** val dirprod_with_prop' :
    'a1 isaprop -> (('a1, ('a2, 'a1) dirprod) dirprod, ('a2, 'a1) dirprod) weq **)

let dirprod_with_prop' isa =
  weqcomp (invweq weqtotal2asstor)
    (weqcomp weqdirprodcomm
      (weqcomp (invweq weqtotal2asstor)
        (weqcomp (weqdirprodf (dirprod_with_prop isa) idweq) weqdirprodcomm)))

(** val issurjective_idfun : ('a1, 'a1) issurjective **)

let issurjective_idfun x =
  hinhpr { pr1 = x; pr2 = Coq_paths_refl }

(** val issurjective_to_contr :
    'a1 -> ('a1 -> 'a2) -> 'a2 iscontr -> ('a1, 'a2) issurjective **)

let issurjective_to_contr x f contr y =
  hinhpr (make_hfiber f y x (proofirrelevancecontr contr (f x) y))

(** val issurjective_tounit : 'a1 -> ('a1, coq_unit) issurjective **)

let issurjective_tounit x =
  issurjective_to_contr x tounit iscontrunit

(** val issurjective_coprodf :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) issurjective -> ('a2, 'a4)
    issurjective -> (('a1, 'a2) coprod, ('a3, 'a4) coprod) issurjective **)

let issurjective_coprodf f g fsurjective gsurjective = function
| Coq_ii1 a -> hinhfun (pr1weq (weqhfibercoprodf1 f g a)) (fsurjective a)
| Coq_ii2 b -> hinhfun (pr1weq (weqhfibercoprodf2 f g b)) (gsurjective b)

(** val issurjective_dirprodf :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) issurjective -> ('a2, 'a4)
    issurjective -> (('a1, 'a2) dirprod, ('a3, 'a4) dirprod) issurjective **)

let issurjective_dirprodf f g fsurjective gsurjective y =
  let u = y.pr1 in
  let w = y.pr2 in
  hinhfun2 (fun ffiber gfiber ->
    make_hfiber (dirprodf f g) { pr1 = u; pr2 = w } { pr1 =
      (hfiberpr1 f u ffiber); pr2 = (hfiberpr1 g w gfiber) }
      (dirprodeq
        (dirprodf f g { pr1 = (hfiberpr1 f u ffiber); pr2 =
          (hfiberpr1 g w gfiber) }) { pr1 = u; pr2 = w }
        (hfiberpr2 f u ffiber) (hfiberpr2 g w gfiber))) (fsurjective u)
    (gsurjective w)

(** val issurjective_totalfun :
    ('a1 -> 'a2 -> 'a3) -> ('a1 -> ('a2, 'a3) issurjective) -> (('a1, 'a2)
    total2, ('a1, 'a3) total2) issurjective **)

let issurjective_totalfun f fsurjective y =
  let x = y.pr1 in
  let qx = y.pr2 in
  hinhfun (fun x0 ->
    let px = x0.pr1 in
    let pathpx = x0.pr2 in
    make_hfiber (totalfun f) { pr1 = x; pr2 = qx } { pr1 = x; pr2 = px }
      (pair_path_in2 x (f x px) qx pathpx)) (fsurjective x qx)

(** val issurjective_sumofmaps_1 :
    ('a2 -> 'a1) -> ('a3 -> 'a1) -> ('a2, 'a1) issurjective -> (('a2, 'a3)
    coprod, 'a1) issurjective **)

let issurjective_sumofmaps_1 f g fsurjective x =
  hinhfun (fun ffiber -> coprodofhfiberstohfiber f g x (Coq_ii1 ffiber))
    (fsurjective x)

(** val issurjective_sumofmaps_2 :
    ('a2 -> 'a1) -> ('a3 -> 'a1) -> ('a3, 'a1) issurjective -> (('a2, 'a3)
    coprod, 'a1) issurjective **)

let issurjective_sumofmaps_2 f g gsurjective x =
  hinhfun (fun gfiber -> coprodofhfiberstohfiber f g x (Coq_ii2 gfiber))
    (gsurjective x)

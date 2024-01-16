open PartA
open PartD
open Preamble
open UnivalenceAxiom

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val eqweqmap_transportb : __ paths -> ('a2 -> 'a1) paths **)

let eqweqmap_transportb _ =
  Coq_paths_refl

(** val eqweqmap_weqtopaths : ('a1, 'a2) weq -> ('a1, 'a2) weq paths **)

let eqweqmap_weqtopaths w =
  homotweqinvweq univalence w

(** val sum_of_fibers :
    ('a1 -> 'a2) -> (('a2, ('a1, 'a2) hfiber) total2, 'a1) weq **)

let sum_of_fibers f =
  make_weq (fun bap -> bap.pr2.pr1) (fun a ->
    make_iscontr
      (make_hfiber (fun bap -> bap.pr2.pr1) a { pr1 = (f a); pr2 =
        (make_hfiber f (f a) a Coq_paths_refl) } Coq_paths_refl) (fun _ ->
      Coq_paths_refl))

type 'a display = (__, 'a) hfiber

(** val totalfst : (__, __ -> 'a1) total2 **)

let totalfst =
  { pr1 = __; pr2 = (Obj.magic (fun t -> t.pr1)) }

(** val totalfst_display :
    (__, __ -> 'a1) total2 -> (__, __ -> 'a1) total2 paths **)

let totalfst_display bf =
  total2_paths_f totalfst bf (weqtopaths (Obj.magic sum_of_fibers bf.pr2))
    (internal_paths_rew_r
      (transportf __ __ (weqtopaths (Obj.magic sum_of_fibers bf.pr2))
        totalfst.pr2)
      (funcomp
        (transportb __ __ (weqtopaths (Obj.magic sum_of_fibers bf.pr2)))
        totalfst.pr2)
      (internal_paths_rew (fun u ->
        pr1weq
          (eqweqmap
            (pathsinv0 __ __ (weqtopaths (Obj.magic sum_of_fibers bf.pr2)))) u)
        (internal_paths_rew_r
          (eqweqmap
            (pathsinv0 __ __ (weqtopaths (Obj.magic sum_of_fibers bf.pr2))))
          (invweq (eqweqmap (weqtopaths (Obj.magic sum_of_fibers bf.pr2))))
          (internal_paths_rew_r
            (eqweqmap (weqtopaths (Obj.magic sum_of_fibers bf.pr2)))
            (sum_of_fibers bf.pr2) Coq_paths_refl
            (eqweqmap_weqtopaths (sum_of_fibers bf.pr2)))
          (eqweqmap_pathsinv0 (weqtopaths (Obj.magic sum_of_fibers bf.pr2))))
        (transportb __ __ (weqtopaths (Obj.magic sum_of_fibers bf.pr2)))
        (eqweqmap_transportb (weqtopaths (Obj.magic sum_of_fibers bf.pr2))))
      (transportf_fun __ __ (weqtopaths (Obj.magic sum_of_fibers bf.pr2))
        totalfst.pr2))

(** val display_totalfst : __ paths **)

let display_totalfst =
  Obj.magic funextsec __ __ (fun a ->
    pathsinv0 (Obj.magic __) (Obj.magic __)
      (Obj.magic weqtopaths (ezweqpr1 a)))

(** val display_weq : ((__, __ -> 'a1) total2, __) weq **)

let display_weq =
  { pr1 = (Obj.magic __); pr2 =
    (isweq_iso (Obj.magic __) (fun _ -> totalfst) totalfst_display (fun _ ->
      display_totalfst)) }

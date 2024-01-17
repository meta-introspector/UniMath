open PartA
open PartA0
open PartB
open Preamble

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type ('x, 'y) coq_PathOver = __

(** val coq_PathOverToPathPair :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathPair **)

let coq_PathOverToPathPair _ _ _ _ _ q =
  { pr1 = Coq_paths_refl; pr2 = (Obj.magic q) }

(** val apd :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> ('a1, 'a2) coq_PathOver **)

let apd s x _ _ =
  Obj.magic pathsinv0 (s x) (s x) Coq_paths_refl

(** val coq_PathOverToTotalPath :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) total2 paths **)

let coq_PathOverToTotalPath x x' p y y' q =
  invmap (total2_paths_equiv { pr1 = x; pr2 = y } { pr1 = x'; pr2 = y' })
    (coq_PathOverToPathPair x x' p y y' q)

(** val coq_PathOverUniqueness :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a2, ('a1, 'a2) coq_PathOver) total2
    iscontr **)

let coq_PathOverUniqueness _ _ _ y =
  Obj.magic iscontrcoconusfromt y

(** val stdPathOver :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) coq_PathOver **)

let stdPathOver x _ _ y =
  Obj.magic pathsinv0 (transportf x x Coq_paths_refl y) y Coq_paths_refl

(** val stdPathOver' :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) coq_PathOver **)

let stdPathOver' x _ _ y' =
  Obj.magic pathsinv0 y' (transportb x x Coq_paths_refl y') Coq_paths_refl

(** val identityPathOver : 'a1 -> 'a2 -> ('a1, 'a2) coq_PathOver **)

let identityPathOver _ _ =
  Obj.magic Coq_paths_refl

(** val pathOverIdpath : 'a1 -> 'a2 -> 'a2 -> __ paths **)

let pathOverIdpath _ _ _ =
  Coq_paths_refl

(** val toPathOverIdpath :
    'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) coq_PathOver **)

let toPathOverIdpath _ _ _ =
  Obj.magic idfun

(** val fromPathOverIdpath :
    'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> 'a2 paths **)

let fromPathOverIdpath _ _ _ =
  Obj.magic idfun

(** val inductionPathOver :
    'a1 -> 'a2 -> 'a3 -> 'a1 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver
    -> 'a3 **)

let inductionPathOver _ _ t _ _ _ _ =
  t

(** val transportPathOver :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> 'a3
    -> 'a3 **)

let transportPathOver _ _ _ _ _ _ x0 =
  x0

(** val transportPathOver' :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> 'a3
    -> 'a3 **)

let transportPathOver' _ _ _ _ _ _ x0 =
  x0

(** val composePathOver :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1,
    'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver **)

let composePathOver _ _ _ _ _ y y' y'' =
  Obj.magic pathscomp0 y y' y''

(** val composePathOverPath :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver
    -> 'a2 paths -> ('a1, 'a2) coq_PathOver **)

let composePathOverPath _ _ _ _ _ _ q _ =
  q

(** val composePathOverIdpath :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver paths **)

let composePathOverIdpath _ _ _ _ _ _ =
  Coq_paths_refl

(** val composePathPathOver :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
    coq_PathOver -> ('a1, 'a2) coq_PathOver **)

let composePathPathOver _ _ _ _ _ _ _ q =
  q

(** val composeIdpathPathOver :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver paths **)

let composeIdpathPathOver _ _ _ _ _ _ =
  Coq_paths_refl

(** val composePathPathOverRotate :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 -> ('a1, 'a2)
    coq_PathOver -> ('a1, 'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver
    paths, ('a1, 'a2) coq_PathOver paths) logeq **)

let composePathPathOverRotate _ _ _ _ _ _ _ _ _ =
  isrefl_logeq

(** val composePathOverPathRotate :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver
    -> 'a2 paths -> ('a1, 'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver
    paths, ('a1, 'a2) coq_PathOver paths) logeq **)

let composePathOverPathRotate _ _ _ _ _ _ _ _ _ =
  isrefl_logeq

(** val composePathPathOverPath :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1,
    'a2) coq_PathOver -> 'a2 paths -> ('a1, 'a2) coq_PathOver paths **)

let composePathPathOverPath _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val composePathOverLeftUnit :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver paths **)

let composePathOverLeftUnit _ _ _ _ _ _ =
  Coq_paths_refl

(** val composePathOverRightUnit :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver paths **)

let composePathOverRightUnit _ _ _ _ _ _ =
  Coq_paths_refl

(** val assocPathOver :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a2 ->
    'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver
    -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths **)

let assocPathOver _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val inversePathOver :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver **)

let inversePathOver _ _ _ _ _ _ =
  Obj.magic Coq_paths_refl

(** val inversePathOver' :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver **)

let inversePathOver' _ _ _ _ _ _ =
  Obj.magic Coq_paths_refl

(** val inverseInversePathOver1 :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver paths **)

let inverseInversePathOver1 _ _ _ _ _ _ =
  Coq_paths_refl

(** val inverseInversePathOver2 :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver paths **)

let inverseInversePathOver2 _ _ _ _ _ _ =
  Coq_paths_refl

(** val inversePathOverIdpath :
    'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) coq_PathOver paths **)

let inversePathOverIdpath _ _ _ _ =
  Coq_paths_refl

(** val inversePathOverIdpath' :
    'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) coq_PathOver paths **)

let inversePathOverIdpath' _ _ _ _ =
  Coq_paths_refl

(** val inverseInversePathOver :
    'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver paths **)

let inverseInversePathOver x y =
  inductionPathOver x y
    (pathsinv0 (identityPathOver x y)
      (transportf (pathsinv0 x x (pathsinv0 x x Coq_paths_refl))
        Coq_paths_refl (pathsinv0inv0 x x Coq_paths_refl)
        (inversePathOver x x (pathsinv0 x x Coq_paths_refl) y y
          (inversePathOver x x Coq_paths_refl y y (identityPathOver x y))))
      Coq_paths_refl)

(** val inversePathOverWeq :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> (('a1, 'a2) coq_PathOver, ('a1,
    'a2) coq_PathOver) weq **)

let inversePathOverWeq x x' p y y' =
  { pr1 = (inversePathOver x x' p y y'); pr2 = (fun s -> { pr1 = { pr1 =
    (inversePathOver' x' x p y' y s); pr2 =
    (inverseInversePathOver2 x' x p y' y s) }; pr2 = (fun _ ->
    Coq_paths_refl) }) }

(** val inversePathOverWeq' :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> (('a1, 'a2) coq_PathOver, ('a1,
    'a2) coq_PathOver) weq **)

let inversePathOverWeq' x x' p y y' =
  { pr1 = (inversePathOver' x x' p y y'); pr2 = (fun s -> { pr1 = { pr1 =
    (inversePathOver x' x p y' y s); pr2 =
    (inverseInversePathOver1 x' x p y' y s) }; pr2 = (fun _ ->
    Coq_paths_refl) }) }

(** val coq_PathOverConstant_id :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> coq_UU paths **)

let coq_PathOverConstant_id _ _ _ _ _ =
  Coq_paths_refl

(** val coq_PathOverConstant_map1 :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
    coq_PathOver **)

let coq_PathOverConstant_map1 _ _ _ _ _ x0 =
  Obj.magic x0

(** val coq_PathOverConstant_map1_eq1 :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths ->
    ('a1, 'a2) coq_PathOver paths **)

let coq_PathOverConstant_map1_eq1 _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val coq_PathOverConstant_map1_eq2 :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths ->
    ('a1, 'a2) coq_PathOver paths **)

let coq_PathOverConstant_map1_eq2 _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val coq_PathOverConstant_map2 :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> 'a2
    paths **)

let coq_PathOverConstant_map2 _ _ _ _ _ x0 =
  Obj.magic x0

(** val coq_PathOverConstant_map2_apd :
    'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths paths **)

let coq_PathOverConstant_map2_apd _ _ _ _ =
  Coq_paths_refl

(** val coq_PathOverConstant_map2_eq1 :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver
    -> 'a2 paths -> 'a2 paths paths **)

let coq_PathOverConstant_map2_eq1 x x' p z z' _ q _ =
  pathsinv0
    (pathscomp0 z z' z' (coq_PathOverConstant_map2 x x' p z z' q)
      Coq_paths_refl) (coq_PathOverConstant_map2 x x' p z z' q)
    (pathscomp0rid z z' (coq_PathOverConstant_map2 x x' p z z' q))

(** val coq_PathOverConstant_map2_eq2 :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
    coq_PathOver -> 'a2 paths paths **)

let coq_PathOverConstant_map2_eq2 _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val coq_PathOverConstant_map1_map2 :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths paths **)

let coq_PathOverConstant_map1_map2 _ _ _ _ _ _ =
  Coq_paths_refl

(** val coq_Lemma023 :
    'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> ('a1,
    'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver)
    isweq **)

let coq_Lemma023 _ _ _ _ _ _ _ _ _ =
  idisweq

(** val composePathOver_weq :
    'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> ('a1,
    'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver)
    weq **)

let composePathOver_weq a1 a2 a3 b1 b2 b3 p1 p2 q =
  make_weq (composePathOver a1 a2 a3 p1 p2 b1 b2 b3 q)
    (coq_Lemma023 a1 a2 a3 b1 b2 b3 p1 p2 q)

(** val coq_Lemma0_2_4 :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
    (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver) isweq **)

let coq_Lemma0_2_4 _ _ _ _ _ _ _ =
  idisweq

(** val cp :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
    (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver) weq **)

let cp a1 a2 p q _UU03b1_ b1 b2 =
  make_weq (transportf p q _UU03b1_) (coq_Lemma0_2_4 a1 a2 b1 b2 p q _UU03b1_)

(** val composePathOverPath_compute :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver
    -> 'a2 paths -> ('a1, 'a2) coq_PathOver paths **)

let composePathOverPath_compute _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val composePathPathOver_compute :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
    coq_PathOver -> ('a1, 'a2) coq_PathOver paths **)

let composePathPathOver_compute _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val cp_idpath :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver paths **)

let cp_idpath _ _ _ _ _ _ =
  Coq_paths_refl

(** val cp_left :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
    'a2 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2)
    coq_PathOver paths **)

let cp_left _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val cp_right :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
    'a2 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2)
    coq_PathOver paths **)

let cp_right _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val cp_in_family :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a2 -> 'a1 paths) -> 'a3 -> 'a3
    -> ('a2 -> ('a1, 'a3) coq_PathOver) -> ('a1, 'a3) coq_PathOver paths **)

let cp_in_family _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val cp_irrelevance :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
    'a1 paths paths -> 'a1 isofhlevel -> (('a1, 'a2) coq_PathOver, ('a1, 'a2)
    coq_PathOver) weq paths **)

let cp_irrelevance a1 a2 b1 b2 p q _UU03b1_ _UU03b2_ ih =
  maponpaths (fun _UU03b1_0 -> cp a1 a2 p q _UU03b1_0 b1 b2) _UU03b1_
    _UU03b2_ (Obj.magic ih a1 a2 p q _UU03b1_ _UU03b2_).pr1

(** val coq_Unnamed_thm :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
    ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> coq_UU paths **)

let coq_Unnamed_thm _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val inverse_cp_p :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
    ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths **)

let inverse_cp_p _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val inverse_cp_p' :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
    ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1 paths, ('a1,
    'a2) coq_PathOver) coq_PathOver -> ('a1 paths, ('a1, 'a2) coq_PathOver)
    coq_PathOver **)

let inverse_cp_p' _ _ _ _ =
  inversePathOver

(** val inverse_cp_p'' :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
    ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1 paths, ('a1,
    'a2) coq_PathOver) coq_PathOver -> ('a1 paths, ('a1, 'a2) coq_PathOver)
    coq_PathOver **)

let inverse_cp_p'' _ _ _ _ _ _ _ _ _ _ =
  Obj.magic Coq_paths_refl

(** val inverse_cp_p_compare :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
    ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1 paths, ('a1,
    'a2) coq_PathOver) coq_PathOver -> ('a1 paths, ('a1, 'a2) coq_PathOver)
    coq_PathOver paths **)

let inverse_cp_p_compare _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val cp_inverse_cp :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
    ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths **)

let cp_inverse_cp _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val composePathOverRightInverse :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver paths **)

let composePathOverRightInverse _ _ _ _ _ _ =
  Coq_paths_refl

(** val composePathOverLeftInverse :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> ('a1,
    'a2) coq_PathOver paths **)

let composePathOverLeftInverse _ _ _ _ _ _ =
  Coq_paths_refl

(** val cp_pathscomp0 :
    'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1
    paths paths -> 'a1 paths paths -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2)
    coq_PathOver paths **)

let cp_pathscomp0 _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val apstar :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths ->
    'a1 paths paths -> 'a1 paths paths -> 'a1 paths paths **)

let apstar a1 a2 a3 p p' q q' x x0 = a1
  (* maponpaths_12 (pathscomp0 a1 a2 a3) p p' x q q' x0 *)

(** val cp_apstar :
    'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths ->
    'a1 paths paths -> 'a1 paths paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2)
    coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths **)

let cp_apstar _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val cp_apstar' :
    'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
    ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths **)

let cp_apstar' _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val pathOverEquations :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 paths -> 'a2 paths ->
    'a1 paths -> __ paths **)

let pathOverEquations f g x _ e _ _ =
  maponpaths (Obj.magic __) e (pathscomp0 (f x) (g x) (g x) e Coq_paths_refl)
    (pathsinv0 (pathscomp0 (f x) (g x) (g x) e Coq_paths_refl) e
      (pathscomp0rid (f x) (g x) e))

(** val pathOverEquations1 :
    ('a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> __
    paths **)

let pathOverEquations1 f x _ e _ _ =
  maponpaths (Obj.magic __) e (pathscomp0 (f x) x x e Coq_paths_refl)
    (pathsinv0 (pathscomp0 (f x) x x e Coq_paths_refl) e
      (pathscomp0rid (f x) x e))

(** val mapPathOver :
    'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a2 -> ('a1,
    'a2) coq_PathOver -> ('a1, 'a3) coq_PathOver **)

let mapPathOver _ _ _ _ _ _ _ =
  Obj.magic Coq_paths_refl

(** val binopPathOver :
    'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a2 -> 'a2 ->
    'a3 -> 'a3 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a3) coq_PathOver -> ('a1,
    'a4) coq_PathOver **)

let binopPathOver _ _ _ _ _ _ _ _ _ _ =
  Obj.magic Coq_paths_refl

type ('x, 'x0, 'y) pullBackFamily = 'y

(** val pullBackSection : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3 **)

let pullBackSection g f x =
  f (g x)

(** val pullBackPointOver :
    ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> ('a1, 'a2, 'a3)
    pullBackFamily **)

let pullBackPointOver _ _ _ _ y =
  y

(** val pullBackPointOverWithSection :
    ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> ('a2 -> 'a3) -> ('a1, 'a2,
    'a3) pullBackFamily paths **)

let pullBackPointOverWithSection _ _ _ _ _ =
  Coq_paths_refl

(** val pullBackPointOverWithSection' :
    ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> ('a2 -> 'a3) -> 'a3
    paths -> ('a1, 'a2, 'a3) pullBackFamily paths **)

let pullBackPointOverWithSection' _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val pullBackPathOverPoint :
    ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> 'a3 -> 'a3 paths ->
    ('a1, 'a2, 'a3) pullBackFamily paths **)

let pullBackPathOverPoint g x x' r y y' t =
  maponpaths (pullBackPointOver g x x' r) y y' t

(** val pullBackPathOver :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths -> 'a1
    paths -> 'a2 paths -> 'a2 paths paths -> 'a3 -> 'a3 -> ('a2, 'a3)
    coq_PathOver -> ('a1, ('a1, 'a2, 'a3) pullBackFamily) coq_PathOver **)

let pullBackPathOver _ _ _ _ _ _ _ _ _ _ _ _ q =
  q

(** val pullBackPathOverPath :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths -> 'a1
    paths -> 'a2 paths -> 'a2 paths paths -> 'a3 -> 'a3 -> 'a3 -> ('a2, 'a3)
    coq_PathOver -> 'a3 paths -> ('a1, ('a1, 'a2, 'a3) pullBackFamily)
    coq_PathOver paths **)

let pullBackPathOverPath _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val pullBackPathPathOver :
    ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths -> 'a1
    paths -> 'a2 paths -> 'a2 paths paths -> 'a3 -> 'a3 -> 'a3 -> ('a2, 'a3)
    coq_PathOver -> 'a3 paths -> ('a1, ('a1, 'a2, 'a3) pullBackFamily)
    coq_PathOver paths **)

let pullBackPathPathOver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val transportf_to_pathover :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
    coq_PathOver **)

let transportf_to_pathover _ _ _ _ _ x0 =
  Obj.magic x0

(** val isweq_transportf_to_pathover :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a2 paths, ('a1, 'a2)
    coq_PathOver) isweq **)

let isweq_transportf_to_pathover x x' p y y' =
  isweq_iso (transportf_to_pathover x x' p y y') (fun x0 -> Obj.magic x0)
    (fun _ -> Coq_paths_refl) (fun _ -> Coq_paths_refl)

(** val transportf_weq_pathover :
    'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a2 paths, ('a1, 'a2)
    coq_PathOver) weq **)

let transportf_weq_pathover x x' p y y' =
  make_weq (transportf_to_pathover x x' p y y')
    (isweq_transportf_to_pathover x x' p y y')

module PathsOverNotations =
 struct
 end

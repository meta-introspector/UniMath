open Preamble
open Propositions
open Sets
open UnivalenceAxiom

(** val squash_to_hSet :
    hSet -> ('a1 -> pr1hSet) -> hProptoType -> hProptoType -> pr1hSet **)

let squash_to_hSet y f =
  Obj.magic squash_to_set (setproperty y) f

(** val squash_to_hSet_2' :
    hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProptoType -> hProptoType ->
    hProptoType -> pr1hSet **)

let squash_to_hSet_2' z f x0 =
  let c = (Obj.magic x0).pr1 in
  let d = (Obj.magic x0).pr2 in
  squash_to_set (isaset_forall_hSet (fun _ -> z)) (fun x ->
    squash_to_hSet z (f x) (Obj.magic (fun y y' -> d x y y'))) (fun x x' ->
    funextfun (squash_to_hSet z (f x) (Obj.magic (fun y y' -> d x y y')))
      (squash_to_hSet z (f x') (Obj.magic (fun y y' -> d x' y y')))
      (fun yn ->
      squash_to_prop yn
        (setproperty z
          (squash_to_hSet z (f x) (Obj.magic (fun y y' -> d x y y')) yn)
          (squash_to_hSet z (f x') (Obj.magic (fun y y' -> d x' y y')) yn))
        (fun y -> c x x' y)))

(** val eqset_to_path :
    hSet -> pr1hSet -> pr1hSet -> hProptoType -> pr1hSet paths **)

let eqset_to_path _ _ _ e =
  Obj.magic e

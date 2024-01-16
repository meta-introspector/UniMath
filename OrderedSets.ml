open PartA
open PartB
open Preamble
open Propositions
open Sets

(** val isTotalOrder : hSet -> pr1hSet hrel -> hProp **)

let isTotalOrder x r =
  make_hProp
    (isapropdirprod (isaprop_isPartialOrder x r) (isaprop_istotal x r))

(** val tot_nge_to_le :
    hSet -> pr1hSet hrel -> pr1hSet istotal -> pr1hSet -> pr1hSet ->
    hProptoType -> hProptoType **)

let tot_nge_to_le _ r tot x y nle =
  hdisjtoimpl (r y x) (tot x y) nle

(** val tot_nle_iff_gt :
    hSet -> pr1hSet hrel -> hProptoType -> pr1hSet -> pr1hSet ->
    (hProptoType, hProptoType) logeq **)

let tot_nle_iff_gt x r i =
  let tot = (Obj.magic i).pr2 in
  let refl = (Obj.magic i).pr1.pr1.pr2 in
  let anti = (Obj.magic i).pr1.pr2 in
  (fun x0 y -> { pr1 = (fun nle ->
  Obj.magic { pr1 = (tot_nge_to_le x r tot x0 y nle); pr2 = (fun _ ->
    Obj.magic nle (refl y)) }); pr2 = (fun yltx ->
  Obj.magic (fun xley ->
    let ylex = (Obj.magic yltx).pr1 in
    (Obj.magic yltx).pr2 (anti y x0 ylex xley))) })

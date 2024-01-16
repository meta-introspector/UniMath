open PartA
open PartB
open Preamble
open Propositions

(** val hequiv : hProp -> hProp -> hProp **)

let hequiv p q =
  hconj (himpl q) (himpl p)

(** val total2_hProp : hProp -> (hProptoType -> hProp) -> hProp **)

let total2_hProp x y =
  make_hProp (isaprop_total2 x y)

type 'x paths_from = 'x coconusfromt

(** val point_to : 'a1 -> 'a1 paths_from -> 'a1 **)

let point_to =
  coconusfromtpr1

(** val paths_from_path : 'a1 -> 'a1 paths_from -> 'a1 paths **)

let paths_from_path _ w =
  w.pr2

type 'x paths' = 'x paths

(** val idpath' : 'a1 -> 'a1 paths' **)

let idpath' _ =
  Coq_paths_refl

type 'x paths_to = 'x coconustot

(** val point_from : 'a1 -> 'a1 paths_to -> 'a1 **)

let point_from =
  coconustotpr1

(** val paths_to_path : 'a1 -> 'a1 paths_to -> 'a1 paths **)

let paths_to_path _ w =
  w.pr2

(** val iscontr_paths_to : 'a1 -> 'a1 paths_to iscontr **)

let iscontr_paths_to =
  iscontrcoconustot

(** val iscontr_paths_from : 'a1 -> 'a1 paths_from iscontr **)

let iscontr_paths_from =
  iscontrcoconusfromt

(** val paths_to_prop : 'a1 -> hProp **)

let paths_to_prop x =
  make_hProp (isapropifcontr (iscontr_paths_to x))

(** val paths_from_prop : 'a1 -> hProp **)

let paths_from_prop x =
  make_hProp (isapropifcontr (iscontr_paths_from x))

(** val squash_path : 'a1 -> 'a1 -> hProptoType paths **)

let squash_path x y =
  let x0 = hinhpr x in
  let x' = hinhpr y in (Obj.magic propproperty ishinh x0 x').pr1

open PartA
open PartB
open Preamble
open UnivalenceAxiom

(** val impred :
    nat -> ('a1 -> 'a2 isofhlevel) -> ('a1 -> 'a2) isofhlevel **)

let rec impred n x =
  match n with
  | O -> Obj.magic funcontr x
  | S n0 ->
    Obj.magic (fun x0 x' ->
      let is = fun t -> Obj.magic x t (x0 t) (x' t) in
      let is2 = impred n0 is in
      let u = toforallpaths x0 x' in
      let is3 = isweqtoforallpaths (Obj.magic x0) (Obj.magic x') in
      let v = invmap (make_weq (Obj.magic u) is3) in
      let is4 = isweqinvmap (make_weq (Obj.magic u) is3) in
      isofhlevelweqf n0 (make_weq v is4) is2)

(** val impred_isaprop : ('a1 -> 'a2 isaprop) -> ('a1 -> 'a2) isaprop **)

let impred_isaprop x =
  impred (S O) x

(** val isapropimpl : 'a2 isaprop -> ('a1 -> 'a2) isaprop **)

let isapropimpl isy =
  impred (S O) (fun _ -> isy)

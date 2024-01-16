open PartA
open PartB
open Propositions

(** val wma_dneg : 'a2 dneg -> ('a2 -> 'a1 neg) -> 'a1 neg **)

let wma_dneg dnp p =
  dnegnegtoneg (dnegf p dnp)

(** val dneg_decidable : 'a1 decidable dneg **)

let dneg_decidable _ =
  assert false (* absurd case *)

(** val wma_decidable : ('a2 decidable -> 'a1 neg) -> 'a1 neg **)

let wma_decidable x =
  wma_dneg dneg_decidable x

(** val negforall_to_existsneg' : hProptoType -> hProptoType dneg **)

let negforall_to_existsneg' nf c =
  Obj.magic nf (fun x -> neghexisttoforallneg (Obj.magic c) x)

open PartA
open PartB
open PartD
open Preamble
open Propositions
open UnivalenceAxiom

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val weq1 :
    (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU, hProptoType)
    total2 paths, (coq_UU paths, hProptoType paths) total2) weq **)

let weq1 _ p p' =
  total2_paths_equiv { pr1 = __; pr2 = p } { pr1 = __; pr2 = p' }

(** val ident_is_prop :
    (__ -> hProp) -> hProptoType -> hProptoType -> coq_UU paths ->
    hProptoType paths isaprop **)

let ident_is_prop p p0 p' w =
  isapropifcontr ((Obj.magic p __).pr2 (transportf __ __ w p0) p')

(** val weq2 :
    (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU paths,
    hProptoType paths) total2, coq_UU paths) weq **)

let weq2 p p0 p' =
  weqpr1 (fun z -> (Obj.magic p __).pr2 (transportf __ __ z p0) p')

(** val coq_Id_p_weq_Id :
    (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU, hProptoType)
    total2 paths, coq_UU paths) weq **)

let coq_Id_p_weq_Id p p0 p' =
  let f = weq1 p p0 p' in let g = weq2 p p0 p' in weqcomp f g

(** val iscontr_weq : 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) weq iscontr **)

let iscontr_weq cX cY =
  { pr1 = (weqcontrcontr cX cY); pr2 = (fun f ->
    subtypePath isapropisweq f (weqcontrcontr cX cY)
      (Obj.magic funextfun (Obj.magic f).pr1
        (weqcontrcontr (Obj.magic cX) (Obj.magic cY)).pr1 (fun x ->
        (Obj.magic cY).pr2 ((Obj.magic f).pr1 x)))) }

(** val isofhlevel0pathspace :
    'a1 iscontr -> 'a2 iscontr -> coq_UU paths iscontr **)

let isofhlevel0pathspace pX pY =
  let h = isofhlevelweqb O { pr1 = eqweqmap; pr2 = univalenceAxiom } in
  Obj.magic h (iscontr_weq pX pY)

(** val isofhlevelSnpathspace :
    nat -> 'a2 isofhlevel -> coq_UU paths isofhlevel **)

let isofhlevelSnpathspace n pY =
  isofhlevelweqb (S n) { pr1 = eqweqmap; pr2 = univalenceAxiom }
    (isofhlevelsnweqtohlevelsn n pY)

(** val isofhlevelpathspace :
    nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> coq_UU paths isofhlevel **)

let isofhlevelpathspace n x x0 =
  match n with
  | O -> Obj.magic isofhlevel0pathspace x x0
  | S n0 -> isofhlevelSnpathspace n0 x0

type coq_HLevel = (coq_UU, __ isofhlevel) total2

(** val isofhlevel_HLevel : nat -> coq_HLevel isofhlevel **)

let isofhlevel_HLevel n =
  Obj.magic (fun x x' ->
    let p = x.pr2 in
    let p' = x'.pr2 in
    isofhlevelweqb n
      (coq_Id_p_weq_Id (fun _ -> { pr1 = __; pr2 = (isapropisofhlevel n) }) p
        p') (isofhlevelpathspace n p p'))

(** val coq_UA_for_Predicates :
    (__ -> hProp) -> hProptoType -> hProptoType -> ((coq_UU, hProptoType)
    total2 paths, ('a1, 'a2) weq) weq **)

let coq_UA_for_Predicates p pX pX' =
  let f = coq_Id_p_weq_Id p pX pX' in
  let g = { pr1 = eqweqmap; pr2 = univalenceAxiom } in weqcomp f (Obj.magic g)

(** val coq_UA_for_HLevels :
    nat -> coq_HLevel -> coq_HLevel -> (coq_HLevel paths, (__, __) weq) weq **)

let coq_UA_for_HLevels n x0 =
  let pX = x0.pr2 in
  (fun x'0 ->
  let pX' = x'0.pr2 in
  coq_UA_for_Predicates (fun _ -> { pr1 = __; pr2 = (isapropisofhlevel n) })
    pX pX')

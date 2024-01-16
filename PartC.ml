open PartA
open PartB
open Preamble

(** val isinclii1 : ('a1, ('a1, 'a2) coprod) isincl **)

let isinclii1 y =
  let f = fun x -> Coq_ii1 x in
  let gf = fun x -> coprodtoboolsum (f x) in
  let gf' = fun x -> { pr1 = Coq_true; pr2 = x } in
  let h = fun _ -> Coq_paths_refl in
  let is1 = isofhlevelfsnfib O Coq_true (isasetbool Coq_true Coq_true) in
  let is2 = isofhlevelfhomot (S O) gf' gf h is1 in
  isofhlevelff (S O) f coprodtoboolsum is2
    (isofhlevelfweq (S (S O)) weqcoprodtoboolsum) y

(** val isinclii2 : ('a2, ('a1, 'a2) coprod) isincl **)

let isinclii2 y =
  let f = fun x -> Coq_ii2 x in
  let gf = fun y0 -> coprodtoboolsum (f y0) in
  let gf' = fun y0 -> { pr1 = Coq_false; pr2 = y0 } in
  let h = fun _ -> Coq_paths_refl in
  let is1 = isofhlevelfsnfib O Coq_false (isasetbool Coq_false Coq_false) in
  let is2 = isofhlevelfhomot (S O) gf' gf h is1 in
  isofhlevelff (S O) f coprodtoboolsum is2
    (isofhlevelfweq (S (S O)) weqcoprodtoboolsum) y

(** val weqhfibercoprodf1 :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a3 -> (('a1, 'a3) hfiber, (('a1, 'a2)
    coprod, ('a3, 'a4) coprod) hfiber) weq **)

let weqhfibercoprodf1 f g x' =
  let ix = fun x -> Coq_ii1 x in
  let ix' = fun x -> Coq_ii1 x in
  let fpg = coprodf f g in
  let w1 = samehfibers f ix' isinclii1 x' in
  let w2 = { pr1 = (hfibersgftog ix fpg (ix' x')); pr2 = (fun y ->
    let u = invezmaphf ix fpg (ix' x') y in
    let is = isweqinvezmaphf ix fpg (ix' x') y in
    iscontrweqb (make_weq u is)
      (let xy = y.pr1 in
       let e = y.pr2 in
       (match xy with
        | Coq_ii1 a -> iscontrhfiberofincl (fun x -> Coq_ii1 x) isinclii1 a
        | Coq_ii2 b -> fromempty (negpathsii2ii1 x' (g b) e)))) }
  in
  weqcomp w1 w2

(** val weqhfibercoprodf2 :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a4 -> (('a2, 'a4) hfiber, (('a1, 'a2)
    coprod, ('a3, 'a4) coprod) hfiber) weq **)

let weqhfibercoprodf2 f g y' =
  let iy = fun x -> Coq_ii2 x in
  let iy' = fun x -> Coq_ii2 x in
  let fpg = coprodf f g in
  let w1 = samehfibers g iy' isinclii2 y' in
  let w2 = { pr1 = (hfibersgftog iy fpg (iy' y')); pr2 = (fun y ->
    let u = invezmaphf iy fpg (iy' y') y in
    let is = isweqinvezmaphf iy fpg (iy' y') y in
    iscontrweqb (make_weq u is)
      (let xy = y.pr1 in
       let e = y.pr2 in
       (match xy with
        | Coq_ii1 a -> fromempty (negpathsii1ii2 (f a) y' e)
        | Coq_ii2 b -> iscontrhfiberofincl (fun x -> Coq_ii2 x) isinclii2 b))) }
  in
  weqcomp w1 w2

(** val isofhlevelfcoprodf :
    nat -> ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) isofhlevelf -> ('a2,
    'a4) isofhlevelf -> (('a1, 'a2) coprod, ('a3, 'a4) coprod) isofhlevelf **)

let isofhlevelfcoprodf n f g is1 is2 = function
| Coq_ii1 a -> isofhlevelweqf n (weqhfibercoprodf1 f g a) (is1 a)
| Coq_ii2 b -> isofhlevelweqf n (weqhfibercoprodf2 f g b) (is2 b)

(** val isofhlevelssncoprod :
    nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2) coprod isofhlevel **)

let isofhlevelssncoprod n isx isy =
  isofhlevelfromfun (S (S n))
    (let f = coprodf (fun _ -> Coq_tt) (fun _ -> Coq_tt) in
     let is1 =
       isofhlevelfcoprodf (S (S n)) (fun _ -> Coq_tt) (fun _ -> Coq_tt)
         (isofhleveltofun (S (S n)) isx) (isofhleveltofun (S (S n)) isy)
     in
     let is2 =
       isofhlevelweqb (S (S n)) boolascoprod (isofhlevelssnset n isasetbool)
     in
     isofhlevelfgf (S (S n)) f (fun _ -> Coq_tt) is1
       (isofhleveltofun (S (S n)) is2))

(** val isasetcoprod :
    'a1 isaset -> 'a2 isaset -> ('a1, 'a2) coprod isaset **)

let isasetcoprod isx isy =
  Obj.magic isofhlevelssncoprod O isx isy

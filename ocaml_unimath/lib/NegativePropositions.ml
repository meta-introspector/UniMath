open NaturalNumbers
open PartA
open PartB
open Preamble
open Propositions

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'p negProp = (coq_UU, (__ isaprop, ('p neg, __) logeq) dirprod) total2

(** val negProp_to_isaprop : 'a1 negProp -> __ isaprop **)

let negProp_to_isaprop nP =
  nP.pr2.pr1

(** val negProp_to_hProp : 'a1 negProp -> hProp **)

let negProp_to_hProp q =
  { pr1 = __; pr2 = (negProp_to_isaprop q) }

(** val negProp_to_iff : 'a1 negProp -> ('a1 neg, hProptoType) logeq **)

let negProp_to_iff nP =
  nP.pr2.pr2

(** val neg_to_negProp : 'a1 negProp -> 'a1 neg -> hProptoType **)

let neg_to_negProp nP np =
  (negProp_to_iff nP).pr1 np

type 'x neqPred = 'x -> 'x paths negProp

type 'x neqReln = 'x -> 'x -> 'x paths negProp

type 'x compl_ne = ('x, hProptoType) total2

(** val make_compl_ne :
    'a1 -> 'a1 neqPred -> 'a1 -> hProptoType -> 'a1 compl_ne **)

let make_compl_ne _ _ y ne =
  { pr1 = y; pr2 = ne }

(** val pr1compl_ne : 'a1 -> 'a1 neqPred -> 'a1 compl_ne -> 'a1 **)

let pr1compl_ne _ _ c =
  c.pr1

(** val recompl_ne :
    'a1 -> 'a1 neqPred -> ('a1 compl_ne, coq_unit) coprod -> 'a1 **)

let recompl_ne x neq_x = function
| Coq_ii1 a -> pr1compl_ne x neq_x a
| Coq_ii2 _ -> x

(** val invrecompl_ne :
    'a1 -> 'a1 neqPred -> 'a1 isisolated -> 'a1 -> ('a1 compl_ne, coq_unit)
    coprod **)

let invrecompl_ne x neq_x is y =
  let c = is y in
  (match c with
   | Coq_ii1 _ -> Coq_ii2 Coq_tt
   | Coq_ii2 b ->
     Coq_ii1 (make_compl_ne x neq_x y (neg_to_negProp (neq_x y) b)))

(** val isweqrecompl_ne :
    'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
    'a1) isweq **)

let isweqrecompl_ne x is neq_x =
  let f = recompl_ne x neq_x in
  let g = invrecompl_ne x neq_x is in
  isweq_iso f g (fun u ->
    let c = is (f u) in
    (match c with
     | Coq_ii1 a ->
       (match u with
        | Coq_ii1 _ -> assert false (* absurd case *)
        | Coq_ii2 _ ->
          pathscomp0 (g (f (Coq_ii2 Coq_tt))) (g x) (Coq_ii2 Coq_tt)
            (maponpaths g (f (Coq_ii2 Coq_tt)) x
              (pathsinv0 x (f (Coq_ii2 Coq_tt)) a))
            (let c0 = is x in
             match c0 with
             | Coq_ii1 _ -> Coq_paths_refl
             | Coq_ii2 _ -> assert false (* absurd case *)))
     | Coq_ii2 _ ->
       (match u with
        | Coq_ii1 a ->
          let y = a.pr1 in
          let neq = a.pr2 in
          let c0 = is y in
          (match c0 with
           | Coq_ii1 _ -> assert false (* absurd case *)
           | Coq_ii2 b ->
             let c1 = Coq_ii2 b in
             (match c1 with
              | Coq_ii1 _ -> assert false (* absurd case *)
              | Coq_ii2 b0 ->
                maponpaths (fun x0 -> Coq_ii1 x0)
                  (make_compl_ne x neq_x y (neg_to_negProp (neq_x y) b0))
                  { pr1 = y; pr2 = neq }
                  (maponpaths (fun x0 -> { pr1 = y; pr2 = x0 })
                    (neg_to_negProp (neq_x y) b0) neq
                    (proofirrelevance (neq_x y).pr2.pr1
                      (neg_to_negProp (neq_x y) b0) neq))))
        | Coq_ii2 _ ->
          let c0 = is x in
          (match c0 with
           | Coq_ii1 _ -> Coq_paths_refl
           | Coq_ii2 b -> fromempty (b Coq_paths_refl))))) (fun _ ->
    Coq_paths_refl)

(** val weqrecompl_ne :
    'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
    'a1) weq **)

let weqrecompl_ne x is neq_x =
  make_weq (recompl_ne x neq_x) (isweqrecompl_ne x is neq_x)

(** val natneq : nat -> nat -> nat paths negProp **)

let natneq m n =
  { pr1 = __; pr2 = { pr1 = (propproperty (natneq_hProp m n)); pr2 =
    (natneq_iff_neq m n) } }

type nat_compl = nat compl_ne

(** val weqdicompl : nat -> (nat, nat_compl) weq **)

let weqdicompl i =
  weq_iso (fun j -> { pr1 = (di i j); pr2 = (di_neq_i i j) }) (fun j ->
    si i j.pr1) (fun j ->
    let c = natlthorgeh j i in
    (match c with
     | Coq_ii1 _ ->
       let c0 = natlthorgeh i j in
       (match c0 with
        | Coq_ii1 _ -> assert false (* absurd case *)
        | Coq_ii2 _ -> Coq_paths_refl)
     | Coq_ii2 _ ->
       let c0 = natlthorgeh i (S j) in
       (match c0 with
        | Coq_ii1 _ ->
          internal_paths_rew_r (add (S O) j) (add j (S O))
            (plusminusnmm j (S O)) (natpluscomm (S O) j)
        | Coq_ii2 _ -> assert false (* absurd case *)))) (fun j ->
    let j0 = j.pr1 in
    let ne = j.pr2 in
    subtypePath (fun k -> negProp_to_isaprop (natneq i k)) { pr1 =
      (di i (si i j0)); pr2 = (di_neq_i i (si i j0)) } { pr1 = j0; pr2 = ne }
      (let c = natlthorgeh j0 i in
       match c with
       | Coq_ii1 _ ->
         let c0 = natlthorgeh i j0 in
         (match c0 with
          | Coq_ii1 _ -> assert false (* absurd case *)
          | Coq_ii2 _ ->
            let c1 = natlthorgeh j0 i in
            (match c1 with
             | Coq_ii1 _ -> Coq_paths_refl
             | Coq_ii2 _ -> assert false (* absurd case *)))
       | Coq_ii2 b ->
         let lt = natleh_neq i j0 b ne in
         let c0 = natlthorgeh i j0 in
         (match c0 with
          | Coq_ii1 _ ->
            let c1 = natlthorgeh (sub j0 (S O)) i in
            (match c1 with
             | Coq_ii1 a ->
               fromempty
                 (match j0 with
                  | O -> negnatlthn0 i lt
                  | S n ->
                    let lt' =
                      internal_paths_rew (add (S O) n) a (add n (S O))
                        (natpluscomm (S O) n)
                    in
                    let lt'0 =
                      internal_paths_rew (sub (add n (S O)) (S O)) lt' n
                        (plusminusnmm n (S O))
                    in
                    natlehneggth i n lt lt'0)
             | Coq_ii2 _ ->
               (match j0 with
                | O -> assert false (* absurd case *)
                | S n -> maponpaths (fun x -> S x) (sub n O) n (natminuseqn n)))
          | Coq_ii2 _ -> assert false (* absurd case *))))

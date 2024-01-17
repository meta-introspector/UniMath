open NaturalNumbers
open PartA
open PartB
open PartC
open Preamble
open Propositions
open Sets

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

(** val negProp_to_neg : 'a1 negProp -> hProptoType -> 'a1 neg **)

let negProp_to_neg nP np =
  (negProp_to_iff nP).pr2 np

(** val neg_to_negProp : 'a1 negProp -> 'a1 neg -> hProptoType **)

let neg_to_negProp nP np =
  (negProp_to_iff nP).pr1 np

type ('x, 'p) negPred = 'x -> 'p negProp

type ('x, 'p) negReln = 'x -> 'x -> 'p negProp

type 'x neqProp = 'x paths negProp

type 'x neqPred = 'x -> 'x paths negProp

type 'x neqReln = 'x -> 'x -> 'x paths negProp

(** val negProp_to_complementary :
    'a1 negProp -> (('a1, hProptoType) coprod, ('a1, hProptoType)
    complementary) logeq **)

let negProp_to_complementary q0 =
  let pr3 = q0.pr2 in
  let pr4 = pr3.pr2 in
  let s = pr4.pr2 in
  { pr1 = (fun pq -> { pr1 = (fun p q -> s q p); pr2 = pq }); pr2 = (fun x ->
  x.pr2) }

(** val negProp_to_uniqueChoice :
    'a1 negProp -> (('a1 isaprop, ('a1, hProptoType) coprod) dirprod, ('a1,
    hProptoType) coprod iscontr) logeq **)

let negProp_to_uniqueChoice q0 =
  let pr3 = q0.pr2 in
  let j = pr3.pr1 in
  { pr1 = (fun x ->
  let i = x.pr1 in
  let v = x.pr2 in
  { pr1 = v; pr2 = (fun w ->
  match v with
  | Coq_ii1 a ->
    (match w with
     | Coq_ii1 a0 ->
       maponpaths (fun x0 -> Coq_ii1 x0) a0 a (Obj.magic i a0 a).pr1
     | Coq_ii2 _ -> assert false (* absurd case *))
  | Coq_ii2 b ->
    (match w with
     | Coq_ii1 _ -> assert false (* absurd case *)
     | Coq_ii2 b0 ->
       maponpaths (fun x0 -> Coq_ii2 x0) b0 b (Obj.magic j b0 b).pr1)) });
  pr2 = (fun x ->
  let c = x.pr1 in
  let e = x.pr2 in
  { pr1 =
  (match c with
   | Coq_ii1 a ->
     invproofirrelevance (fun p p' ->
       Obj.magic equality_by_case (Coq_ii1 p) (Coq_ii1 p')
         (pathscomp0 (Coq_ii1 p) (Coq_ii1 a) (Coq_ii1 p') (e (Coq_ii1 p))
           (pathsinv0 (Coq_ii1 p') (Coq_ii1 a) (e (Coq_ii1 p')))))
   | Coq_ii2 _ ->
     invproofirrelevance (fun _ _ -> assert false (* absurd case *))); pr2 =
  c }) }

type 'x isisolated_ne = 'x -> ('x paths, hProptoType) coprod

(** val isisolated_to_isisolated_ne :
    'a1 -> 'a1 neqPred -> 'a1 isisolated -> 'a1 isisolated_ne **)

let isisolated_to_isisolated_ne _ neq_x i y =
  let c = i y in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 (neg_to_negProp (neq_x y) b))

(** val isisolated_ne_to_isisolated :
    'a1 -> 'a1 neqPred -> 'a1 isisolated_ne -> 'a1 isisolated **)

let isisolated_ne_to_isisolated _ neq_x i y =
  let c = i y in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 (negProp_to_neg (neq_x y) b))

type 't isolated_ne = ('t, 't isisolated_ne) total2

(** val make_isolated_ne :
    'a1 -> 'a1 neqReln -> 'a1 isisolated_ne -> 'a1 isolated_ne **)

let make_isolated_ne t _ i =
  { pr1 = t; pr2 = i }

(** val pr1isolated_ne : 'a1 neqReln -> 'a1 isolated_ne -> 'a1 **)

let pr1isolated_ne _ x =
  x.pr1

(** val isaproppathsfromisolated_ne :
    'a1 -> 'a1 neqPred -> 'a1 isisolated_ne -> 'a1 -> 'a1 paths isaprop **)

let isaproppathsfromisolated_ne x _ is y =
  invproofirrelevance (fun m n ->
    let a =
      pathscomp0 (transportf x y m (is x)) (is y) (transportf x y n (is x))
        (transport_section is x y m)
        (pathsinv0 (transportf x y n (is x)) (is y)
          (transport_section is x y n))
    in
    let c = is x in
    (match c with
     | Coq_ii1 a0 ->
       let b = transport_map (fun _ p -> Coq_ii1 p) x y m a0 in
       let c0 = transport_map (fun _ p -> Coq_ii1 p) x y n a0 in
       let d =
         equality_by_case (Coq_ii1 (transportf x y m a0)) (Coq_ii1
           (transportf x y n a0))
           (pathscomp0 (Coq_ii1 (transportf x y m a0))
             (transportf x y m (Coq_ii1 a0)) (Coq_ii1 (transportf x y n a0))
             (pathsinv0 (transportf x y m (Coq_ii1 a0)) (Coq_ii1
               (transportf x y m a0)) b)
             (pathscomp0 (transportf x y m (Coq_ii1 a0))
               (transportf x y n (Coq_ii1 a0)) (Coq_ii1
               (transportf x y n a0)) a c0))
       in
       let d0 =
         internal_paths_rew (transportf x y m a0) d (pathscomp0 x x y a0 m)
           (transportf_id1 x x y m a0)
       in
       let d1 =
         internal_paths_rew (transportf x y n a0) d0 (pathscomp0 x x y a0 n)
           (transportf_id1 x x y n a0)
       in
       pathscomp_cancel_left x x y a0 m n (Obj.magic d1)
     | Coq_ii2 _ -> assert false (* absurd case *)))

type 'x compl_ne = ('x, hProptoType) total2

(** val make_compl_ne :
    'a1 -> 'a1 neqPred -> 'a1 -> hProptoType -> 'a1 compl_ne **)

let make_compl_ne _ _ y ne =
  { pr1 = y; pr2 = ne }

(** val pr1compl_ne : 'a1 -> 'a1 neqPred -> 'a1 compl_ne -> 'a1 **)

let pr1compl_ne _ _ c =
  c.pr1

(** val make_negProp : 'a1 negProp **)

let make_negProp =
  { pr1 = __; pr2 = { pr1 = isapropneg; pr2 = (Obj.magic isrefl_logeq) } }

(** val make_neqProp : 'a1 -> 'a1 -> 'a1 neqProp **)

let make_neqProp _ _ =
  make_negProp

(** val isinclpr1compl_ne :
    'a1 -> 'a1 neqPred -> ('a1 compl_ne, 'a1) isincl **)

let isinclpr1compl_ne _ neq_x =
  isinclpr1 (fun y -> negProp_to_isaprop (neq_x y))

(** val compl_ne_weq_compl :
    'a1 -> 'a1 neqPred -> ('a1 compl, 'a1 compl_ne) weq **)

let compl_ne_weq_compl _ neq_x =
  weqfibtototal (fun y ->
    weqiff (negProp_to_iff (neq_x y)) isapropneg
      (negProp_to_isaprop (neq_x y)))

(** val compl_weq_compl_ne :
    'a1 -> 'a1 neqPred -> ('a1 compl_ne, 'a1 compl) weq **)

let compl_weq_compl_ne _ neq_x =
  weqfibtototal (fun y ->
    weqiff (issymm_logeq (negProp_to_iff (neq_x y)))
      (negProp_to_isaprop (neq_x y)) isapropneg)

(** val recompl_ne :
    'a1 -> 'a1 neqPred -> ('a1 compl_ne, coq_unit) coprod -> 'a1 **)

let recompl_ne x neq_x = function
| Coq_ii1 a -> pr1compl_ne x neq_x a
| Coq_ii2 _ -> x

(** val maponcomplincl_ne :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 neqPred -> 'a2 neqPred ->
    'a1 compl_ne -> 'a2 compl_ne **)

let maponcomplincl_ne f is x neq_x neq_fx c =
  let x' = c.pr1 in
  let neqx = c.pr2 in
  { pr1 = (f x'); pr2 =
  (neg_to_negProp (neq_fx (f x'))
    (negf (invmaponpathsincl f is x x') (negProp_to_neg (neq_x c.pr1) neqx))) }

(** val weqoncompl_ne :
    ('a1, 'a2) weq -> 'a1 -> 'a1 neqPred -> 'a2 neqPred -> ('a1 compl_ne, 'a2
    compl_ne) weq **)

let weqoncompl_ne w x neq_x neq_wx =
  weqcomp
    (weqfibtototal (fun x' ->
      weqiff
        (logeq_trans (issymm_logeq (negProp_to_iff (neq_x x')))
          (logeq_trans (logeqnegs (weq_to_iff (weqonpaths w x x')))
            (negProp_to_iff (neq_wx (pr1weq w x')))))
        (negProp_to_isaprop (neq_x x'))
        (negProp_to_isaprop (neq_wx (pr1weq w x'))))) (weqfp w)

(** val weqoncompl_ne_compute :
    ('a1, 'a2) weq -> 'a1 -> 'a1 neqPred -> 'a2 neqPred -> 'a1 compl_ne ->
    'a2 paths **)

let weqoncompl_ne_compute _ _ _ _ _ =
  Coq_paths_refl

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

(** val isweqrecompl_ne' :
    'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
    'a1) isweq **)



(** val weqrecompl_ne :
    'a1 -> 'a1 isisolated -> 'a1 neqPred -> (('a1 compl_ne, coq_unit) coprod,
    'a1) weq **)

let weqrecompl_ne x is neq_x =
  make_weq (recompl_ne x neq_x) (isweqrecompl_ne x is neq_x)

(** val isweqrecompl' :
    'a1 -> 'a1 isisolated -> (('a1 compl, coq_unit) coprod, 'a1) isweq **)

let isweqrecompl' x is =
  let neq_x = fun y -> make_neqProp x y in
  isweqhomot
    (pr1weq
      (weqcomp (weqcoprodf (compl_ne_weq_compl x neq_x) idweq)
        (weqrecompl_ne x is neq_x))) (recompl x) (fun _ -> Coq_paths_refl)
    (weqproperty
      (weqcomp (weqcoprodf (compl_ne_weq_compl x neq_x) idweq)
        (weqrecompl_ne x is neq_x)))

(** val iscotrans_to_istrans_negReln :
    'a1 hrel -> ('a1, hProptoType) negReln -> 'a1 isdeccotrans -> 'a1 istrans **)

let iscotrans_to_istrans_negReln _ nR i x1 x2 x3 nxy nyz =
  neg_to_negProp (nR x1 x3)
    (negf (i x1 x2 x3) (fun c ->
      match c with
      | Coq_ii1 a -> negProp_to_neg (nR x1 x2) nxy a
      | Coq_ii2 b -> negProp_to_neg (nR x2 x3) nyz b))

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

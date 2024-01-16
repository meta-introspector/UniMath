open NaturalNumbers
open PartA
open PartB
open PartD
open Preamble
open Propositions
open Propositions0

type minimal = nat -> hProptoType -> hProptoType

(** val isapropminimal : (nat -> hProp) -> nat -> minimal isaprop **)

let isapropminimal _ n =
  impred_isaprop (fun m -> isapropimpl (isasetbool (natgtb (S m) n) Coq_true))

type min_n_UUU = (nat, (hProptoType, minimal) dirprod) total2

(** val isapropmin_n : (nat -> hProp) -> min_n_UUU isaprop **)

let isapropmin_n p =
  isaproptotal2 (fun n -> isapropdirprod (p n).pr2 (isapropminimal p n))
    (fun n n' k k' ->
    let p0 = k.pr1 in
    let m = k.pr2 in
    let p' = k'.pr1 in
    let m' = k'.pr2 in isantisymmnatleh n n' (m n' p') (m' n p0))

(** val min_n : (nat -> hProp) -> hProp **)

let min_n p =
  make_hProp (isapropmin_n p)

type smaller =
  (nat, (hProptoType, (minimal, hProptoType) dirprod) dirprod) total2

(** val smaller_S : (nat -> hProp) -> nat -> smaller -> smaller **)

let smaller_S _ n k =
  let l = k.pr1 in
  let pmz = k.pr2 in
  let p = pmz.pr1 in
  let mz = pmz.pr2 in
  let m = mz.pr1 in
  let z = mz.pr2 in
  { pr1 = l; pr2 = { pr1 = p; pr2 = { pr1 = m; pr2 =
  (istransnatgth (S (S n)) (S n) l (natgthsnn (S n)) z) } } }

(** val bounded_search :
    (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) -> nat
    -> (smaller, nat -> hProptoType -> hProptoType neg) coprod **)

let rec bounded_search p p_dec = function
| O ->
  let x = p_dec O in
  (match x with
   | Coq_ii1 a ->
     Coq_ii1 { pr1 = O; pr2 = { pr1 = a; pr2 = { pr1 = (fun m _ ->
       natleh0n m); pr2 = (isreflnatleh O) } } }
   | Coq_ii2 b ->
     Coq_ii2 (fun l lleq0 ->
       let h = natleh0tois0 l lleq0 in internal_paths_rew_r l O b h))
| S n0 ->
  (match bounded_search p p_dec n0 with
   | Coq_ii1 a -> Coq_ii1 (smaller_S p n0 a)
   | Coq_ii2 b ->
     let x = p_dec (S n0) in
     (match x with
      | Coq_ii1 a ->
        Coq_ii1 { pr1 = (S n0); pr2 = { pr1 = a; pr2 = { pr1 = (fun m q ->
          let x0 = natgthorleh (S n0) m in
          (match x0 with
           | Coq_ii1 a0 -> fromempty (b m a0 q)
           | Coq_ii2 b0 -> b0)); pr2 = (isreflnatleh (S n0)) } } }
      | Coq_ii2 b0 ->
        Coq_ii2 (fun l q ->
          let x0 = natgthorleh l n0 in
          (match x0 with
           | Coq_ii1 a ->
             let h = isantisymmnatgeh l (S n0) a q in
             internal_paths_rew_r l (S n0) b0 h
           | Coq_ii2 b1 -> b l b1))))

(** val n_to_min_n :
    (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) -> nat
    -> hProptoType -> hProptoType **)

let n_to_min_n p p_dec n p0 =
  let x = bounded_search p p_dec n in
  (match x with
   | Coq_ii1 a ->
     let l = a.pr1 in
     let qmz = a.pr2 in
     let q = qmz.pr1 in
     let mz = qmz.pr2 in
     let m = mz.pr1 in Obj.magic { pr1 = l; pr2 = { pr1 = q; pr2 = m } }
   | Coq_ii2 b -> fromempty (b n (isreflnatgeh n) p0))

(** val prop_n_to_min_n :
    (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) ->
    hProptoType -> hProptoType **)

let prop_n_to_min_n p p_dec p_inhab =
  hinhuniv (min_n p) (fun x ->
    let n = x.pr1 in let p0 = x.pr2 in n_to_min_n p p_dec n p0) p_inhab

(** val minimal_n :
    (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) ->
    hProptoType -> (nat, hProptoType) total2 **)

let minimal_n p p_dec p_inhab =
  let h = prop_n_to_min_n p p_dec p_inhab in
  let n = (Obj.magic h).pr1 in
  let pl = (Obj.magic h).pr2 in let p0 = pl.pr1 in { pr1 = n; pr2 = p0 }

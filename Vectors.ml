open NaturalNumbers
open PartA
open PartB
open Preamble
open Propositions
open StandardFiniteSets
open UnivalenceAxiom

type __ = Obj.t

(** val stn_extens : nat -> stn -> stn -> nat paths -> stn paths **)

let stn_extens n i j p =
  subtypePath' i j p (propproperty (natlth (stntonat n j) n))

(** val fromstn0 : stn -> 'a1 **)

let fromstn0 i =
  fromempty (negnatlthn0 i.pr1 i.pr2)

type 'a vec = __

(** val vnil : 'a1 vec **)

let vnil =
  Obj.magic Coq_tt

(** val vcons : nat -> 'a1 -> 'a1 vec -> 'a1 vec **)

let vcons _ x v =
  Obj.magic { pr1 = x; pr2 = v }

(** val drop : nat -> (stn -> 'a1) -> stn -> 'a1 **)

let drop n f i =
  f (dni_firstelement n i)

(** val make_vec : nat -> (stn -> 'a1) -> 'a1 vec **)

let rec make_vec n f =
  match n with
  | O -> vnil
  | S n0 -> vcons n0 (f (firstelement n0)) (make_vec n0 (drop n0 f))

(** val hd : nat -> 'a1 vec -> 'a1 **)

let hd _ v =
  (Obj.magic v).pr1

(** val tl : nat -> 'a1 vec -> 'a1 vec **)

let tl _ v =
  (Obj.magic v).pr2

(** val el : nat -> 'a1 vec -> stn -> 'a1 **)

let rec el n v =
  match n with
  | O -> fromstn0
  | S n0 ->
    (fun i ->
      let j = i.pr1 in
      let jlt = i.pr2 in
      (match j with
       | O -> hd n0 v
       | S n1 -> el n0 (tl n0 v) { pr1 = n1; pr2 = jlt }))

(** val el_make_vec : nat -> (stn -> 'a1) -> (stn, 'a1) homot **)

let rec el_make_vec n f =
  match n with
  | O -> fromstn0
  | S n0 ->
    (fun i ->
      let j = i.pr1 in
      let jlt = i.pr2 in
      (match j with
       | O ->
         maponpaths f (firstelement n0) { pr1 = O; pr2 = jlt }
           (stn_extens (S n0) (firstelement n0) { pr1 = O; pr2 = jlt }
             Coq_paths_refl)
       | S n1 ->
         pathscomp0
           (el (S n0) (make_vec (S n0) f) { pr1 = (S n1); pr2 = jlt })
           (drop n0 f { pr1 = n1; pr2 = jlt })
           (f { pr1 = (S n1); pr2 = jlt })
           (el_make_vec n0 (drop n0 f) { pr1 = n1; pr2 = jlt })
           (maponpaths f (dni_firstelement n0 { pr1 = n1; pr2 = jlt })
             { pr1 = (S n1); pr2 = jlt } Coq_paths_refl)))

(** val el_make_vec_fun : nat -> (stn -> 'a1) -> (stn -> 'a1) paths **)

let el_make_vec_fun n f =
  Obj.magic funextfun (el n (make_vec n f)) f (el_make_vec n f)

(** val el_vcons_tl : nat -> 'a1 vec -> 'a1 -> stn -> 'a1 paths **)

let el_vcons_tl n v _ i =
  match n with
  | O -> fromstn0 i
  | S n0 ->
    maponpaths
      (let n1 = i.pr1 in
       fun jlt ->
       match n1 with
       | O -> hd n0 v
       | S n2 ->
         let rec f n3 v0 =
           match n3 with
           | O -> fromstn0
           | S n4 ->
             (fun i0 ->
               let n5 = i0.pr1 in
               (match n5 with
                | O -> hd n4 v0
                | S n6 -> f n4 (tl n4 v0) { pr1 = n6; pr2 = i0.pr2 }))
         in f n0 (tl n0 v) { pr1 = n2; pr2 = jlt }) i.pr2 i.pr2
      (proofirrelevance (propproperty (natlth i.pr1 (S n0))) i.pr2 i.pr2)

(** val drop_el : nat -> 'a1 vec -> stn -> 'a1 paths **)

let drop_el n v i =
  let x = (Obj.magic v).pr1 in
  let u = (Obj.magic v).pr2 in el_vcons_tl n u x i

(** val el_tl : nat -> 'a1 vec -> stn -> 'a1 paths **)

let el_tl n v i =
  internal_paths_rew_r (drop n (el (S n) v) i) (el n (tl n v) i)
    Coq_paths_refl (drop_el n v i)

(** val vec0_eq : 'a1 vec -> 'a1 vec -> 'a1 vec paths **)

let vec0_eq u v =
  proofirrelevancecontr (Obj.magic iscontrunit) u v

(** val vecS_eq :
    nat -> 'a1 vec -> 'a1 vec -> 'a1 paths -> 'a1 vec paths -> 'a1 vec paths **)

let vecS_eq _ u v p q =
  Obj.magic dirprod_paths u v p q

(** val vec_extens :
    nat -> 'a1 vec -> 'a1 vec -> (stn -> 'a1 paths) -> 'a1 vec paths **)

let rec vec_extens n u v h =
  match n with
  | O -> vec0_eq u v
  | S n0 ->
    vecS_eq n0 u v (h (firstelement n0))
      (vec_extens n0 (tl n0 u) (tl n0 v) (fun i ->
        internal_paths_rew_r (el n0 (tl n0 u) i) (drop n0 (el (S n0) u) i)
          (internal_paths_rew_r (el n0 (tl n0 v) i) (drop n0 (el (S n0) v) i)
            (h (dni_firstelement n0 i)) (el_tl n0 v i)) (el_tl n0 u i)))

(** val make_vec_el : nat -> 'a1 vec -> 'a1 vec paths **)

let make_vec_el n v =
  vec_extens n (make_vec n (el n v)) v (fun i ->
    internal_paths_rew_r (el n (make_vec n (el n v)) i) (el n v i)
      Coq_paths_refl (el_make_vec n (el n v) i))

(** val isweqvecfun : nat -> ('a1 vec, stn -> 'a1) isweq **)

let isweqvecfun n =
  isweq_iso (el n) (make_vec n) (make_vec_el n) (el_make_vec_fun n)

(** val weqvecfun : nat -> ('a1 vec, stn -> 'a1) weq **)

let weqvecfun n =
  make_weq (el n) (isweqvecfun n)

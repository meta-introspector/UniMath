open NaturalNumbers
open PartA
open PartB
open Preamble
open Propositions
open StandardFiniteSets
open UnivalenceAxiom

type __ = Obj.t

(** val stn_extens : nat -> stn -> stn -> nat paths -> stn paths **)

let stn_extens n i j p = n
  (* subtypePath' i j p (propproperty (natlth (stntonat n j) n)) *)

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

(** val el_vcons_hd : nat -> 'a1 vec -> 'a1 -> 'a1 paths **)

let el_vcons_hd _ _ _ =
  Coq_paths_refl

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

(** val isofhlevelvec : nat -> 'a1 isofhlevel -> nat -> 'a1 vec isofhlevel **)

let rec isofhlevelvec n is1 = function
| O -> isofhlevelcontr n iscontrunit
| S n0 -> isofhleveldirprod n is1 (isofhlevelvec n is1 n0)

(** val vec_ind :
    'a2 -> ('a1 -> nat -> 'a1 vec -> 'a2 -> 'a2) -> nat -> 'a1 vec -> 'a2 **)

let rec vec_ind hnil hcons n v =
  match n with
  | O -> transportb v vnil (vec0_eq v vnil) hnil
  | S n0 ->
    hcons (Obj.magic v).pr1 n0 (Obj.magic v).pr2
      (vec_ind hnil hcons n0 (Obj.magic v).pr2)

(** val vec_map : ('a1 -> 'a2) -> nat -> 'a1 vec -> 'a2 vec **)

let rec vec_map f n v =
  match n with
  | O -> vnil
  | S n0 -> vcons n0 (f (hd n0 v)) (vec_map f n0 (tl n0 v))

(** val hd_vec_map : ('a1 -> 'a2) -> nat -> 'a1 vec -> 'a2 paths **)

let hd_vec_map _ _ _ =
  Coq_paths_refl

(** val tl_vec_map : ('a1 -> 'a2) -> nat -> 'a1 vec -> 'a2 vec paths **)

let tl_vec_map _ _ _ =
  Coq_paths_refl

(** val el_vec_map : ('a1 -> 'a2) -> nat -> 'a1 vec -> stn -> 'a2 paths **)

let rec el_vec_map f n v i =
  match n with
  | O -> fromstn0 i
  | S n0 ->
    let j = i.pr1 in
    let jlt = i.pr2 in
    (match j with
     | O -> hd_vec_map f n0 v
     | S n1 ->
       pathscomp0 (el n0 (tl n0 (vec_map f (S n0) v)) (make_stn n0 n1 jlt))
         (drop n0 (el (S n0) (vec_map f (S n0) v)) (make_stn n0 n1 jlt))
         (f (el n0 (tl n0 v) (make_stn n0 n1 jlt)))
         (el_tl n0 (vec_map f (S n0) v) (make_stn n0 n1 jlt))
         (pathscomp0
           (drop n0 (el (S n0) (vec_map f (S n0) v)) (make_stn n0 n1 jlt))
           (f
             (el n0 (tl n0 v) { pr1 = (make_stn n0 n1 jlt).pr1; pr2 =
               (dni_firstelement n0 (make_stn n0 n1 jlt)).pr2 }))
           (f (el n0 (tl n0 v) (make_stn n0 n1 jlt)))
           (el_vec_map f n0 (tl n0 v) { pr1 = (make_stn n0 n1 jlt).pr1; pr2 =
             (dni_firstelement n0 (make_stn n0 n1 jlt)).pr2 })
           (maponpaths f
             (el n0 (tl n0 v) { pr1 = (make_stn n0 n1 jlt).pr1; pr2 =
               (dni_firstelement n0 (make_stn n0 n1 jlt)).pr2 })
             (el n0 (tl n0 v) (make_stn n0 n1 jlt))
             (maponpaths (el n0 (tl n0 v)) { pr1 = (make_stn n0 n1 jlt).pr1;
               pr2 = (dni_firstelement n0 (make_stn n0 n1 jlt)).pr2 }
               (make_stn n0 n1 jlt) Coq_paths_refl))))

(** val vec_map_as_make_vec :
    ('a1 -> 'a2) -> nat -> 'a1 vec -> 'a2 vec paths **)

let vec_map_as_make_vec f n v =
  vec_extens n (vec_map f n v) (make_vec n (fun i -> f (el n v i))) (fun i ->
    internal_paths_rew_r (el n (vec_map f n v) i) (f (el n v i))
      (internal_paths_rew_r (el n (make_vec n (fun i0 -> f (el n v i0))) i)
        (f (el n v i)) Coq_paths_refl
        (el_make_vec n (fun i0 -> f (el n v i0)) i)) (el_vec_map f n v i))

(** val vec_foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> nat -> 'a1 vec -> 'a2 **)

let vec_foldr f b n =
  vec_ind b (fun a _ _ acc -> f a acc) n

(** val vec_foldr1 : ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 vec -> 'a1 **)

let rec vec_foldr1 f = function
| O -> hd O
| S n0 -> Obj.magic uncurry (fun x u -> f x (vec_foldr1 f n0 u))

(** val vec_append : nat -> 'a1 vec -> nat -> 'a1 vec -> 'a1 vec **)

let vec_append m u n v =
  vec_ind v (fun x p _ w -> vcons (add p n) x w) m u

(** val vec_map_id : nat -> 'a1 vec -> 'a1 vec paths **)

let vec_map_id n v =
  vec_ind Coq_paths_refl (fun x n0 xs hPxs ->
    maponpaths (vcons n0 x) (vec_map idfun n0 xs) xs hPxs) n v

(** val vec_map_comp :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> nat -> 'a1 vec -> 'a3 vec paths **)

let vec_map_comp f g n v =
  vec_ind Coq_paths_refl (fun x n0 xs hPxs ->
    vecS_eq n0 (vec_map (funcomp f g) (S n0) (vcons n0 x xs))
      (funcomp (vec_map f (S n0)) (vec_map g (S n0)) (vcons n0 x xs))
      Coq_paths_refl hPxs) n v

(** val vec_map_make_vec :
    nat -> (stn -> 'a1) -> ('a1 -> 'a2) -> 'a2 vec paths **)

let vec_map_make_vec n g f =
  vec_extens n (vec_map f n (make_vec n g)) (make_vec n (funcomp g f))
    (fun i ->
    internal_paths_rew_r (el n (vec_map f n (make_vec n g)) i)
      (f (el n (make_vec n g) i))
      (internal_paths_rew_r (el n (make_vec n g) i) (g i)
        (internal_paths_rew_r (el n (make_vec n (funcomp g f)) i)
          (funcomp g f i) Coq_paths_refl (el_make_vec n (funcomp g f) i))
        (el_make_vec n g i)) (el_vec_map f n (make_vec n g) i))

(** val vec_append_lid : 'a1 vec -> nat -> ('a1 vec -> 'a1 vec) paths **)

let vec_append_lid _ _ =
  Coq_paths_refl

(** val vec_fill : 'a1 -> nat -> 'a1 vec **)

let rec vec_fill a = function
| O -> vnil
| S n0 -> vcons n0 a (vec_fill a n0)

(** val vec_map_const : nat -> 'a1 vec -> 'a2 -> 'a2 vec paths **)

let vec_map_const n v b =
  vec_ind Coq_paths_refl (fun _ n0 xs hPind ->
    maponpaths (vcons n0 b) (vec_map (fun _ -> b) n0 xs) (vec_fill b n0) hPind)
    n v

(** val vec_zip : nat -> 'a1 vec -> 'a2 vec -> ('a1, 'a2) dirprod vec **)

let rec vec_zip n v1 v2 =
  match n with
  | O -> vnil
  | S n0 ->
    let x1 = (Obj.magic v1).pr1 in
    let xs1 = (Obj.magic v1).pr2 in
    let x2 = (Obj.magic v2).pr1 in
    let xs2 = (Obj.magic v2).pr2 in
    vcons n0 { pr1 = x1; pr2 = x2 } (vec_zip n0 xs1 xs2)

open NaturalNumbers
open PartA
open Preamble
open Propositions

type __ = Obj.t

(** val nat_dist : nat -> nat -> nat **)

let rec nat_dist m n =
  match m with
  | O -> n
  | S m0 -> (match n with
             | O -> m
             | S n0 -> nat_dist m0 n0)

module Discern =
 struct
  type nat_discern = __

  (** val helper_A : nat -> nat -> nat paths -> nat_discern **)

  let rec helper_A m n =
    match m with
    | O ->
      (match n with
       | O -> (fun _ -> Obj.magic Coq_tt)
       | S n0 -> Obj.magic negpathssx0 n0)
    | S n0 ->
      (match n with
       | O -> Obj.magic negpathssx0 n0
       | S n1 -> helper_A n0 n1)

  (** val helper_B : nat -> nat -> nat_discern -> nat paths **)

  let rec helper_B m n =
    match m with
    | O ->
      (match n with
       | O -> (fun _ -> Coq_paths_refl)
       | S _ -> Obj.magic fromempty)
    | S _ ->
      (match n with
       | O -> Obj.magic fromempty
       | S _ -> (fun _ -> Coq_paths_refl))

  (** val nat_dist_anti : nat -> nat -> nat paths -> nat paths **)

  let nat_dist_anti m n i =
    helper_B m n (helper_A m n i)
 end

(** val nat_dist_symm : nat -> nat -> nat paths **)

let rec nat_dist_symm m n =
  match m with
  | O -> Coq_paths_refl
  | S n0 -> (match n with
             | O -> Coq_paths_refl
             | S n1 -> nat_dist_symm n0 n1)

(** val nat_dist_ge : nat -> nat -> hProptoType -> nat paths **)

let rec nat_dist_ge m n =
  match m with
  | O -> (fun _ -> Coq_paths_refl)
  | S n0 ->
    (match n with
     | O -> (fun _ -> Coq_paths_refl)
     | S n1 -> nat_dist_ge n0 n1)

(** val nat_dist_m0 : nat -> nat paths **)

let nat_dist_m0 _ =
  Coq_paths_refl

(** val nat_dist_plus : nat -> nat -> nat paths **)

let rec nat_dist_plus m n =
  match m with
  | O -> nat_dist_m0 n
  | S n0 -> nat_dist_plus n0 n

(** val nat_dist_le : nat -> nat -> hProptoType -> nat paths **)

let rec nat_dist_le m n =
  match m with
  | O -> (fun _ -> Coq_paths_refl)
  | S n0 ->
    (match n with
     | O -> (fun _ -> Coq_paths_refl)
     | S n1 -> nat_dist_le n0 n1)

(** val nat_dist_minus : nat -> nat -> hProptoType -> nat paths **)

let nat_dist_minus m n e =
  let k = sub n m in
  let b = pathsinv0 (add (sub n m) m) n (minusplusnmm n m e) in
  let b0 = internal_paths_rew (sub n m) b k Coq_paths_refl in
  internal_paths_rew_r n (add k m)
    (internal_paths_rew_r (nat_dist k (add k m)) (nat_dist (add k m) k)
      (nat_dist_plus k m) (nat_dist_symm k (add k m))) b0

(** val nat_dist_gt : nat -> nat -> hProptoType -> nat paths **)

let rec nat_dist_gt m n x =
  match m with
  | O -> fromempty (nopathsfalsetotrue (Obj.magic x))
  | S n0 ->
    (match n with
     | O -> maponpaths (fun x0 -> S x0) (nat_dist n0 O) n0 (nat_dist_m0 n0)
     | S n1 -> nat_dist_gt n0 n1 x)

(** val nat_dist_S : nat -> nat -> nat paths **)

let nat_dist_S _ _ =
  Coq_paths_refl

(** val natleorle : nat -> nat -> (hProptoType, hProptoType) coprod **)

let natleorle m n =
  let c = natgthorleh m n in
  (match c with
   | Coq_ii1 a -> Coq_ii2 (natlthtoleh n m a)
   | Coq_ii2 b -> Coq_ii1 b)

(** val nat_dist_trans : nat -> nat -> nat -> hProptoType **)

let nat_dist_trans x y z =
  let c = natleorle x y in
  (match c with
   | Coq_ii1 a ->
     internal_paths_rew_r (nat_dist x y) (sub y x)
       (let c0 = natleorle y z in
        match c0 with
        | Coq_ii1 a0 ->
          let u = istransnatgeh z y x a0 a in
          internal_paths_rew_r (nat_dist y z) (sub z y)
            (internal_paths_rew_r (nat_dist x z) (sub z x)
              (natlehandplusrinv (sub z x) (add (sub y x) (sub z y)) x
                (internal_paths_rew_r (add (sub z x) x) z
                  (internal_paths_rew_r (add (add (sub y x) (sub z y)) x)
                    (add x (add (sub y x) (sub z y)))
                    (internal_paths_rew (add (add x (sub y x)) (sub z y))
                      (internal_paths_rew_r (add x (sub y x))
                        (add (sub y x) x)
                        (internal_paths_rew_r (add (sub y x) x) y
                          (internal_paths_rew_r (add y (sub z y))
                            (add (sub z y) y)
                            (internal_paths_rew_r (add (sub z y) y) z
                              (isreflnatleh z) (minusplusnmm z y a0))
                            (natpluscomm y (sub z y))) (minusplusnmm y x a))
                        (natpluscomm x (sub y x)))
                      (add x (add (sub y x) (sub z y)))
                      (natplusassoc x (sub y x) (sub z y)))
                    (natpluscomm (add (sub y x) (sub z y)) x))
                  (minusplusnmm z x u))) (nat_dist_le x z u))
            (nat_dist_le y z a0)
        | Coq_ii2 b ->
          internal_paths_rew_r (nat_dist y z) (sub y z)
            (let c1 = natleorle x z in
             match c1 with
             | Coq_ii1 a0 ->
               internal_paths_rew_r (nat_dist x z) (sub z x)
                 (natlehandplusrinv (sub z x) (add (sub y x) (sub y z)) x
                   (internal_paths_rew_r (add (sub z x) x) z
                     (internal_paths_rew_r (add (add (sub y x) (sub y z)) x)
                       (add x (add (sub y x) (sub y z)))
                       (internal_paths_rew (add (add x (sub y x)) (sub y z))
                         (internal_paths_rew_r (add x (sub y x))
                           (add (sub y x) x)
                           (internal_paths_rew_r (add (sub y x) x) y
                             (natlehandplusrinv z (add y (sub y z)) z
                               (internal_paths_rew_r
                                 (add (add y (sub y z)) z)
                                 (add y (add (sub y z) z))
                                 (internal_paths_rew_r (add (sub y z) z) y
                                   (istransnatleh (add z z) (add y z)
                                     (add y y) (natlehandplusr z y z b)
                                     (natlehandplusl z y y b))
                                   (minusplusnmm y z b))
                                 (natplusassoc y (sub y z) z)))
                             (minusplusnmm y x a)) (natpluscomm x (sub y x)))
                         (add x (add (sub y x) (sub y z)))
                         (natplusassoc x (sub y x) (sub y z)))
                       (natpluscomm (add (sub y x) (sub y z)) x))
                     (minusplusnmm z x a0))) (nat_dist_le x z a0)
             | Coq_ii2 b0 ->
               internal_paths_rew_r (nat_dist x z) (sub x z)
                 (natlehandplusrinv (sub x z) (add (sub y x) (sub y z)) z
                   (internal_paths_rew_r (add (sub x z) z) x
                     (internal_paths_rew_r (add (add (sub y x) (sub y z)) z)
                       (add (sub y x) (add (sub y z) z))
                       (internal_paths_rew_r (add (sub y z) z) y
                         (internal_paths_rew_r (add (sub y x) y)
                           (add y (sub y x))
                           (natlehandplusrinv x (add y (sub y x)) x
                             (internal_paths_rew_r (add (add y (sub y x)) x)
                               (add y (add (sub y x) x))
                               (internal_paths_rew_r (add (sub y x) x) y
                                 (istransnatleh (add x x) (add x y) (add y y)
                                   (natlehandplusl x y x a)
                                   (natlehandplusr x y y a))
                                 (minusplusnmm y x a))
                               (natplusassoc y (sub y x) x)))
                           (natpluscomm (sub y x) y)) (minusplusnmm y z b))
                       (natplusassoc (sub y x) (sub y z) z))
                     (minusplusnmm x z b0))) (nat_dist_ge x z b0))
            (nat_dist_ge y z b)) (nat_dist_le x y a)
   | Coq_ii2 b ->
     internal_paths_rew_r (nat_dist x y) (sub x y)
       (let c0 = natleorle z y in
        match c0 with
        | Coq_ii1 a ->
          let w = istransnatleh z y x a b in
          internal_paths_rew_r (nat_dist x z) (sub x z)
            (internal_paths_rew_r (nat_dist y z) (sub y z)
              (natlehandplusrinv (sub x z) (add (sub x y) (sub y z)) z
                (internal_paths_rew_r (add (sub x z) z) x
                  (internal_paths_rew_r (add (add (sub x y) (sub y z)) z)
                    (add (sub x y) (add (sub y z) z))
                    (internal_paths_rew_r (add (sub y z) z) y
                      (internal_paths_rew_r (add (sub x y) y) x
                        (isreflnatleh x) (minusplusnmm x y b))
                      (minusplusnmm y z a))
                    (natplusassoc (sub x y) (sub y z) z))
                  (minusplusnmm x z w))) (nat_dist_ge y z a))
            (nat_dist_ge x z w)
        | Coq_ii2 b0 ->
          internal_paths_rew_r (nat_dist y z) (sub z y)
            (let c1 = natleorle x z in
             match c1 with
             | Coq_ii1 a ->
               internal_paths_rew_r (nat_dist x z) (sub z x)
                 (natlehandplusrinv (sub z x) (add (sub x y) (sub z y)) x
                   (internal_paths_rew_r (add (sub z x) x) z
                     (natlehandpluslinv z (add (add (sub x y) (sub z y)) x) y
                       (internal_paths_rew_r
                         (add (add (sub x y) (sub z y)) x)
                         (add (sub x y) (add (sub z y) x))
                         (internal_paths_rew
                           (add (add y (sub x y)) (add (sub z y) x))
                           (internal_paths_rew_r (add y (sub x y))
                             (add (sub x y) y)
                             (internal_paths_rew_r (add (sub x y) y) x
                               (natlehandplusrinv (add y z)
                                 (add x (add (sub z y) x)) y
                                 (internal_paths_rew_r
                                   (add (add x (add (sub z y) x)) y)
                                   (add x (add (add (sub z y) x) y))
                                   (internal_paths_rew_r
                                     (add (add (sub z y) x) y)
                                     (add (sub z y) (add x y))
                                     (internal_paths_rew_r (add x y)
                                       (add y x)
                                       (internal_paths_rew
                                         (add (add (sub z y) y) x)
                                         (internal_paths_rew_r
                                           (add (sub z y) y) z
                                           (internal_paths_rew_r (add z x)
                                             (add x z)
                                             (internal_paths_rew
                                               (add (add x x) z)
                                               (internal_paths_rew_r
                                                 (add (add y z) y)
                                                 (add y (add z y))
                                                 (internal_paths_rew_r
                                                   (add z y) (add y z)
                                                   (internal_paths_rew
                                                     (add (add y y) z)
                                                     (natlehandplusr
                                                       (add y y) (add x x) z
                                                       (istransnatleh
                                                         (add y y) (add x y)
                                                         (add x x)
                                                         (natlehandplusr y x
                                                           y b)
                                                         (natlehandplusl y x
                                                           x b)))
                                                     (add y (add y z))
                                                     (natplusassoc y y z))
                                                   (natpluscomm z y))
                                                 (natplusassoc y z y))
                                               (add x (add x z))
                                               (natplusassoc x x z))
                                             (natpluscomm z x))
                                           (minusplusnmm z y b0))
                                         (add (sub z y) (add y x))
                                         (natplusassoc (sub z y) y x))
                                       (natpluscomm x y))
                                     (natplusassoc (sub z y) x y))
                                   (natplusassoc x (add (sub z y) x) y)))
                               (minusplusnmm x y b))
                             (natpluscomm y (sub x y)))
                           (add y (add (sub x y) (add (sub z y) x)))
                           (natplusassoc y (sub x y) (add (sub z y) x)))
                         (natplusassoc (sub x y) (sub z y) x)))
                     (minusplusnmm z x a))) (nat_dist_le x z a)
             | Coq_ii2 b1 ->
               internal_paths_rew_r (nat_dist x z) (sub x z)
                 (natlehandplusrinv (sub x z) (add (sub x y) (sub z y)) z
                   (internal_paths_rew_r (add (sub x z) z) x
                     (natlehandpluslinv x (add (add (sub x y) (sub z y)) z) y
                       (internal_paths_rew_r
                         (add (add (sub x y) (sub z y)) z)
                         (add (sub x y) (add (sub z y) z))
                         (internal_paths_rew
                           (add (add y (sub x y)) (add (sub z y) z))
                           (internal_paths_rew_r (add y (sub x y))
                             (add (sub x y) y)
                             (internal_paths_rew_r (add (sub x y) y) x
                               (natlehandplusrinv (add y x)
                                 (add x (add (sub z y) z)) y
                                 (internal_paths_rew_r
                                   (add (add x (add (sub z y) z)) y)
                                   (add x (add (add (sub z y) z) y))
                                   (internal_paths_rew_r
                                     (add (add (sub z y) z) y)
                                     (add (sub z y) (add z y))
                                     (internal_paths_rew_r (add z y)
                                       (add y z)
                                       (internal_paths_rew
                                         (add (add (sub z y) y) z)
                                         (internal_paths_rew_r
                                           (add (sub z y) y) z
                                           (internal_paths_rew_r (add y x)
                                             (add x y)
                                             (internal_paths_rew_r
                                               (add (add x y) y)
                                               (add x (add y y))
                                               (natlehandplusl (add y y)
                                                 (add z z) x
                                                 (istransnatleh (add y y)
                                                   (add z y) (add z z)
                                                   (natlehandplusr y z y b0)
                                                   (natlehandplusl y z z b0)))
                                               (natplusassoc x y y))
                                             (natpluscomm y x))
                                           (minusplusnmm z y b0))
                                         (add (sub z y) (add y z))
                                         (natplusassoc (sub z y) y z))
                                       (natpluscomm z y))
                                     (natplusassoc (sub z y) z y))
                                   (natplusassoc x (add (sub z y) z) y)))
                               (minusplusnmm x y b))
                             (natpluscomm y (sub x y)))
                           (add y (add (sub x y) (add (sub z y) z)))
                           (natplusassoc y (sub x y) (add (sub z y) z)))
                         (natplusassoc (sub x y) (sub z y) z)))
                     (minusplusnmm x z b1))) (nat_dist_ge x z b1))
            (nat_dist_le y z b0)) (nat_dist_ge x y b))

(** val natleplusminus : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natleplusminus k m n i =
  natlehandplusrinv k (sub n m) m
    (internal_paths_rew_r (add (sub n m) m) n i
      (minusplusnmm n m (istransnatleh m (add k m) n (natlehmplusnm k m) i)))

(** val natltminus1 : nat -> nat -> hProptoType -> hProptoType **)

let natltminus1 m n i =
  let a = natlthp1toleh m (sub n (S O)) in
  let b = natleh0n m in
  let c = natlehlthtrans O m n b i in
  let d = natlthtolehsn O n c in
  let e = minusplusnmm n (S O) d in
  internal_paths_rew (add (sub n (S O)) (S O)) a n e i

(** val natminusminusassoc : nat -> nat -> nat -> nat paths **)

let rec natminusminusassoc m n k =
  match m with
  | O -> Coq_paths_refl
  | S n0 ->
    (match n with
     | O ->
       internal_paths_rew_r (sub (S n0) O) (S n0) Coq_paths_refl
         (natminuseqn (S n0))
     | S n1 -> natminusminusassoc n0 n1 k)

(** val natminusplusltcomm :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natminusplusltcomm m n k i p =
  let a = natlehandplusr m (sub n k) k p in
  let b = minusplusnmm n k i in
  let a0 = internal_paths_rew (add (sub n k) k) a n b in
  natleplusminus k m n
    (internal_paths_rew_r (add k m) (add m k) a0 (natpluscomm k m))

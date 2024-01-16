open DecSet
open Lists
open Maybe
open NaturalNumbers
open PartA
open Preamble
open Propositions
open Sets
open Vectors

(** val head : 'a1 list -> 'a1 maybe **)

let head x =
  list_ind nothing (fun x0 _ _ -> Coq_ii1 x0) x

(** val tail : 'a1 list -> 'a1 list maybe **)

let tail x =
  list_ind nothing (fun _ xs _ -> Coq_ii1 xs) x

(** val list_head_cons : 'a1 -> 'a1 list -> 'a1 maybe paths **)

let list_head_cons _ _ =
  Coq_paths_refl

(** val list_tail_cons : 'a1 -> 'a1 list -> 'a1 list maybe paths **)

let list_tail_cons _ _ =
  Coq_paths_refl

(** val cons_inj1 :
    'a1 -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths -> 'a1 paths **)

let cons_inj1 a1 a2 r1 r2 h =
  let h0 = maponpaths head (cons a1 r1) (cons a2 r2) h in
  ii1_injectivity a1 a2 h0

(** val cons_inj2 :
    'a1 -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths -> 'a1 list paths **)

let cons_inj2 a1 a2 r1 r2 h =
  let h0 = maponpaths tail (cons a1 r1) (cons a2 r2) h in
  ii1_injectivity r1 r2 h0

(** val negpathsconsnil : 'a1 -> 'a1 list -> 'a1 list paths neg **)

let negpathsconsnil a l x =
  let x0 = maponpaths (fun t -> t.pr1) (cons a l) nil x in
  negpathssx0 l.pr1 x0

(** val negpathsnilcons : 'a1 -> 'a1 list -> 'a1 list paths neg **)

let negpathsnilcons a l x =
  let x0 = pathsinv0 nil (cons a l) x in negpathsconsnil a l x0

(** val length_cons : 'a1 -> 'a1 list -> nat paths **)

let length_cons _ _ =
  Coq_paths_refl

(** val length_zero_back : 'a1 list -> nat paths -> 'a1 list paths **)

let length_zero_back l =
  list_ind (fun _ -> Coq_paths_refl) (fun _ _ _ _ -> assert false
    (* absurd case *)) l

(** val length_one_back :
    'a1 list -> nat paths -> ('a1, 'a1 list paths) total2 **)

let length_one_back l _ =
  let pr3 = l.pr2 in
  let x = (Obj.magic pr3).pr1 in { pr1 = x; pr2 = Coq_paths_refl }

(** val length_concatenate : 'a1 list -> 'a1 list -> nat paths **)

let length_concatenate l1 l2 =
  list_ind Coq_paths_refl (fun _ xs iH ->
    maponpaths (fun x -> S x) (length (concatenate xs l2))
      (add (length xs) (length l2)) iH) l1

(** val length_sublist1 : 'a1 list -> 'a1 list -> hProptoType **)

let length_sublist1 l1 l2 =
  internal_paths_rew_r (length (concatenate l1 l2))
    (add (length l1) (length l2)) (natlehnplusnm (length l1) (length l2))
    (length_concatenate l1 l2)

(** val length_sublist2 : 'a1 list -> 'a1 list -> hProptoType **)

let length_sublist2 l1 l2 =
  internal_paths_rew_r (length (concatenate l1 l2))
    (add (length l1) (length l2))
    (internal_paths_rew_r (add (length l1) (length l2))
      (add (length l2) (length l1)) (natlehnplusnm (length l2) (length l1))
      (natpluscomm (length l1) (length l2))) (length_concatenate l1 l2)

(** val length_map : 'a1 list -> ('a1 -> 'a2) -> nat paths **)

let length_map l f =
  list_ind Coq_paths_refl (fun _ xs hPind ->
    maponpaths (fun x -> S x) (length (map f xs)) (length xs) hPind) l

(** val listset : hSet -> hSet **)

let listset a =
  make_hSet (Obj.magic isofhlevellist O (setproperty a))

(** val fill : 'a1 -> nat -> 'a1 list **)

let fill a n =
  { pr1 = n; pr2 = (vec_fill a n) }

(** val map_const : 'a2 -> 'a1 list -> 'a2 list paths **)

let map_const b l =
  list_ind Coq_paths_refl (fun _ xs hPind ->
    maponpaths (cons b) (map (fun _ -> b) xs) (fill b (length xs)) hPind) l

(** val length_fill : 'a1 -> nat -> nat paths **)

let length_fill _ _ =
  Coq_paths_refl

(** val drop : 'a1 list -> nat -> 'a1 list **)

let rec drop l = function
| O -> idfun l
| S n0 -> list_ind nil (fun _ xs _ -> drop xs n0) l

(** val drop_nil : nat -> 'a1 list paths **)

let drop_nil _ =
  Coq_paths_refl

(** val drop_zero : 'a1 list -> 'a1 list paths **)

let drop_zero l =
  list_ind Coq_paths_refl (fun _ _ _ -> Coq_paths_refl) l

(** val drop_step : 'a1 -> 'a1 list -> nat -> 'a1 list paths **)

let drop_step _ _ _ =
  Coq_paths_refl

(** val drop_full : 'a1 list -> 'a1 list paths **)

let drop_full l =
  list_ind Coq_paths_refl (fun _ _ x -> x) l

(** val drop_concatenate :
    'a1 list -> 'a1 list -> nat -> hProptoType -> 'a1 list paths **)

let rec drop_concatenate l1 l2 n nok =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    list_ind (fun _ -> assert false (* absurd case *)) (fun x xs _ sok ->
      internal_paths_rew_r (concatenate (cons x xs) l2)
        (cons x (concatenate xs l2))
        (internal_paths_rew_r (drop (cons x (concatenate xs l2)) (S n0))
          (drop (concatenate xs l2) n0)
          (internal_paths_rew_r (drop (cons x xs) (S n0)) (drop xs n0)
            (drop_concatenate xs l2 n0 sok) (drop_step x xs n0))
          (drop_step x (concatenate xs l2) n0)) (concatenateStep x xs l2)) l1
      nok

(** val length_drop : 'a1 list -> nat -> nat paths **)

let length_drop l n =
  list_ind (fun n0 ->
    internal_paths_rew_r (drop nil n0) nil
      (let rec f = function
       | O -> Coq_paths_refl
       | S n2 ->
         internal_paths_rew (sub (sub O (S O)) n2) (f n2)
           (sub O (add (S O) n2)) (natminusminus O (S O) n2)
       in f n0) (drop_nil n0)) (fun x xs iH n0 ->
    match n0 with
    | O -> Coq_paths_refl
    | S n1 ->
      internal_paths_rew_r (drop (cons x xs) (S n1)) (drop xs n1)
        (internal_paths_rew_r (length (cons x xs)) (S (length xs)) (iH n1)
          (length_cons x xs)) (drop_step x xs n1)) l n

(** val prefix_remove :
    decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list maybe **)

let prefix_remove a l1 l2 =
  list_ind just (fun x _ hP ->
    list_ind nothing (fun y ys _ ->
      let d = decproperty a x y in
      (match d with
       | Coq_ii1 _ -> hP ys
       | Coq_ii2 _ -> nothing))) l1 l2

(** val prefix_remove_stepeq :
    decSet -> pr1decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list
    maybe paths **)

let prefix_remove_stepeq a x _ _ =
  let d = decproperty a x x in
  (match d with
   | Coq_ii1 _ -> Coq_paths_refl
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val prefix_remove_stepneq :
    decSet -> pr1decSet -> pr1decSet -> pr1decSet paths neg -> pr1decSet list
    -> pr1decSet list -> pr1decSet list maybe paths **)

let prefix_remove_stepneq a x1 x2 _ _ _ =
  let d = decproperty a x1 x2 in
  (match d with
   | Coq_ii1 _ -> assert false (* absurd case *)
   | Coq_ii2 _ -> Coq_paths_refl)

(** val prefix_remove_stepback :
    decSet -> pr1decSet -> pr1decSet -> pr1decSet list -> pr1decSet list ->
    pr1decSet list maybe paths neg -> pr1decSet paths **)

let prefix_remove_stepback a x1 x2 xs1 xs2 =
  let d = decproperty a x1 x2 in
  (fun hP ->
  match d with
  | Coq_ii1 a0 -> a0
  | Coq_ii2 b ->
    let hP0 =
      internal_paths_rew (prefix_remove a (cons x1 xs1) (cons x2 xs2)) hP
        nothing (prefix_remove_stepneq a x1 x2 b xs1 xs2)
    in
    fromempty (hP0 Coq_paths_refl))

(** val prefix_remove_back :
    decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list -> pr1decSet
    list maybe paths -> pr1decSet list paths **)

let prefix_remove_back a l1 l2 l3 =
  list_ind (fun l4 prefixnil -> just_injectivity l4 l3 prefixnil)
    (fun x1 xs1 hPind ->
    list_ind (fun _ -> assert false (* absurd case *)) (fun x2 xs2 _ hP ->
      let d = decproperty a x1 x2 in
      (match d with
       | Coq_ii1 a0 ->
         internal_paths_rew_r x1 x2
           (let hP0 = internal_paths_rew x1 hP x2 a0 in
            let hP1 =
              internal_paths_rew
                (prefix_remove a (cons x2 xs1) (cons x2 xs2)) hP0
                (prefix_remove a xs1 xs2) (prefix_remove_stepeq a x2 xs1 xs2)
            in
            internal_paths_rew_r (concatenate (cons x2 xs1) l3)
              (cons x2 (concatenate xs1 l3))
              (internal_paths_rew_r xs2 (concatenate xs1 l3) Coq_paths_refl
                (hPind xs2 hP1)) (concatenateStep x2 xs1 l3)) a0
       | Coq_ii2 _ -> assert false (* absurd case *)))) l1 l2

(** val prefix_remove_self :
    decSet -> pr1decSet list -> pr1decSet list maybe paths **)

let prefix_remove_self a l =
  list_ind Coq_paths_refl (fun x xs iH ->
    internal_paths_rew_r (prefix_remove a (cons x xs) (cons x xs))
      (prefix_remove a xs xs) iH (prefix_remove_stepeq a x xs xs)) l

type isprefix = pr1decSet list maybe paths neg

(** val isprefix_self : decSet -> pr1decSet list -> isprefix **)

let isprefix_self a l =
  internal_paths_rew_r (prefix_remove a l l) (just nil)
    (negpathsii1ii2 nil Coq_tt) (prefix_remove_self a l)

(** val prefix_remove_concatenate :
    decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list -> pr1decSet
    list -> pr1decSet list maybe paths -> pr1decSet list maybe paths **)

let prefix_remove_concatenate a l1 l2 l3 tl =
  list_ind (fun l4 prooftl ->
    let prooftl0 = ii1_injectivity l4 tl prooftl in
    internal_paths_rew_r l4 tl Coq_paths_refl prooftl0) (fun x xs hPind ->
    list_ind (fun _ -> assert false (* absurd case *)) (fun x2 x2s _ ->
      internal_paths_rew_r (concatenate (cons x2 x2s) l3)
        (cons x2 (concatenate x2s l3))
        (let d = decproperty a x x2 in
         match d with
         | Coq_ii1 a0 ->
           internal_paths_rew_r x x2
             (internal_paths_rew_r
               (prefix_remove a (cons x2 xs) (cons x2 x2s))
               (prefix_remove a xs x2s)
               (internal_paths_rew_r
                 (prefix_remove a (cons x2 xs) (cons x2 (concatenate x2s l3)))
                 (prefix_remove a xs (concatenate x2s l3)) (hPind x2s)
                 (prefix_remove_stepeq a x2 xs (concatenate x2s l3)))
               (prefix_remove_stepeq a x2 xs x2s)) a0
         | Coq_ii2 b ->
           internal_paths_rew_r (prefix_remove a (cons x xs) (cons x2 x2s))
             nothing (fun _ -> assert false (* absurd case *))
             (prefix_remove_stepneq a x x2 b xs x2s))
        (concatenateStep x2 x2s l3))) l1 l2

(** val prefix_remove_concatenate2 :
    decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list ->
    hProptoType -> pr1decSet list maybe paths -> pr1decSet list maybe paths **)

let prefix_remove_concatenate2 a l1 l2 l3 =
  list_ind (fun _ _ _ -> assert false (* absurd case *)) (fun x1 xs1 iH ->
    list_ind (fun _ _ -> assert false (* absurd case *))
      (fun x2 xs2 _ hlen hpref ->
      internal_paths_rew_r (concatenate (cons x2 xs2) l3)
        (cons x2 (concatenate xs2 l3))
        (let d = decproperty a x1 x2 in
         match d with
         | Coq_ii1 _ ->
           internal_paths_rew_r
             (prefix_remove a (cons x1 xs1) (cons x1 (concatenate xs2 l3)))
             (prefix_remove a xs1 (concatenate xs2 l3))
             (let hpref0 =
                internal_paths_rew
                  (prefix_remove a (cons x1 xs1) (cons x1 xs2)) hpref
                  (prefix_remove a xs1 xs2)
                  (prefix_remove_stepeq a x1 xs1 xs2)
              in
              iH xs2 hlen hpref0)
             (prefix_remove_stepeq a x1 xs1 (concatenate xs2 l3))
         | Coq_ii2 b ->
           prefix_remove_stepneq a x1 x2 b xs1 (concatenate xs2 l3))
        (concatenateStep x2 xs2 l3))) l1 l2

(** val prefix_remove_prefix :
    decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list maybe paths **)

let prefix_remove_prefix a l1 l2 =
  list_ind Coq_paths_refl (fun x xs iHl1 ->
    internal_paths_rew_r (concatenate (cons x xs) l2)
      (cons x (concatenate xs l2))
      (internal_paths_rew_r
        (prefix_remove a (cons x xs) (cons x (concatenate xs l2)))
        (prefix_remove a xs (concatenate xs l2)) iHl1
        (prefix_remove_stepeq a x xs (concatenate xs l2)))
      (concatenateStep x xs l2)) l1

(** val prefix_remove_drop :
    decSet -> pr1decSet list -> pr1decSet list -> pr1decSet list maybe paths
    neg -> pr1decSet list maybe paths **)

let prefix_remove_drop a l1 l2 =
  list_ind (fun _ _ -> Coq_paths_refl) (fun x1 xs1 iH ->
    list_ind (fun _ -> assert false (* absurd case *))
      (fun x2 xs2 _ prefixok ->
      let d = decproperty a x1 x2 in
      (match d with
       | Coq_ii1 _ ->
         internal_paths_rew_r (prefix_remove a (cons x1 xs1) (cons x1 xs2))
           (prefix_remove a xs1 xs2)
           (let prefixok0 =
              internal_paths_rew
                (prefix_remove a (cons x1 xs1) (cons x1 xs2)) prefixok
                (prefix_remove a xs1 xs2) (prefix_remove_stepeq a x1 xs1 xs2)
            in
            iH xs2 prefixok0) (prefix_remove_stepeq a x1 xs1 xs2)
       | Coq_ii2 _ -> assert false (* absurd case *)))) l1 l2

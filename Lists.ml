open NaturalNumbers
open PartA
open PartB
open Preamble
open StandardFiniteSets
open Vectors

type 'a list = (nat, 'a vec) total2

(** val nil : 'a1 list **)

let nil =
  { pr1 = O; pr2 = vnil }

(** val cons : 'a1 -> 'a1 list -> 'a1 list **)

let cons x xs =
  { pr1 = (S xs.pr1); pr2 = (vcons xs.pr1 x xs.pr2) }

(** val list_ind :
    'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let list_ind hnil hcons xs =
  let n = xs.pr1 in
  let xs0 = xs.pr2 in
  let rec f n0 xs1 =
    match n0 with
    | O -> hnil
    | S n1 ->
      let x = (Obj.magic xs1).pr1 in
      let xs2 = (Obj.magic xs1).pr2 in
      hcons x { pr1 = n1; pr2 = xs2 } (f n1 xs2)
  in f n xs0

(** val list_ind_compute_2 :
    'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 paths **)

let list_ind_compute_2 _ _ _ _ =
  Coq_paths_refl

(** val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let foldr f b =
  list_ind b (fun a _ b' -> f a b')

(** val length : 'a1 list -> nat **)

let length x =
  x.pr1

(** val foldr1 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 list -> 'a1 **)

let foldr1 f a =
  list_ind a (fun a' l fl -> list_ind a' (fun _ _ _ -> f a' fl) l)

(** val foldr1_map :
    ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 list -> 'a2 **)

let foldr1_map f b h =
  list_ind b (fun a' l fl -> list_ind (h a') (fun _ _ _ -> f (h a') fl) l)

(** val nth : 'a1 list -> stn -> 'a1 **)

let nth x =
  el x.pr1 x.pr2

(** val functionToList' : nat -> (stn -> 'a1) -> 'a1 vec **)

let rec functionToList' n f =
  match n with
  | O -> Obj.magic Coq_tt
  | S n0 ->
    Obj.magic { pr1 = (Obj.magic f { pr1 = O; pr2 = Coq_paths_refl }); pr2 =
      (functionToList' n0
        (funcomp (dni n0 { pr1 = O; pr2 = (Obj.magic Coq_paths_refl) }) f)) }

(** val functionToList : nat -> (stn -> 'a1) -> 'a1 list **)

let functionToList n f =
  { pr1 = n; pr2 = (make_vec n f) }

(** val coq_Unnamed_thm : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths **)

let coq_Unnamed_thm _ _ _ _ =
  Coq_paths_refl

(** val coq_Unnamed_thm0 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths **)

let coq_Unnamed_thm0 _ _ _ _ =
  Coq_paths_refl

(** val coq_Unnamed_thm1 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths **)

let coq_Unnamed_thm1 _ _ _ _ =
  Coq_paths_refl

(** val coq_Unnamed_thm2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths **)

let coq_Unnamed_thm2 _ _ _ _ =
  Coq_paths_refl

(** val coq_Unnamed_thm3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 list paths **)

let coq_Unnamed_thm3 _ _ _ _ =
  Coq_paths_refl

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let map f =
  foldr (fun a l -> cons (f a) l) nil

(** val mapStep : ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 list paths **)

let mapStep _ _ _ =
  Coq_paths_refl

(** val foldr_nil : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a2 paths **)

let foldr_nil _ _ =
  Coq_paths_refl

(** val foldr_cons :
    ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 -> 'a1 list -> 'a2 paths **)

let foldr_cons _ _ _ _ =
  Coq_paths_refl

(** val map_nil : ('a1 -> 'a2) -> 'a2 list paths **)

let map_nil _ =
  Coq_paths_refl

(** val map_cons : ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 list paths **)

let map_cons _ _ _ =
  Coq_paths_refl

(** val map_compose :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 list -> 'a3 list paths **)

let map_compose f g xs =
  list_ind Coq_paths_refl (fun x xs0 iH ->
    internal_paths_rew_r (map (funcomp f g) (cons x xs0))
      (cons (funcomp f g x) (map (funcomp f g) xs0))
      (internal_paths_rew_r (map f (cons x xs0)) (cons (f x) (map f xs0))
        (internal_paths_rew_r (map g (cons (f x) (map f xs0)))
          (cons (g (f x)) (map g (map f xs0)))
          (internal_paths_rew_r (map (funcomp f g) xs0) (map g (map f xs0))
            Coq_paths_refl iH) (map_cons g (f x) (map f xs0)))
        (map_cons f x xs0)) (map_cons (funcomp f g) x xs0)) xs

(** val map_idfun : 'a1 list -> 'a1 list paths **)

let map_idfun xs =
  list_ind Coq_paths_refl (fun x xs0 iH ->
    internal_paths_rew_r (map idfun (cons x xs0))
      (cons (idfun x) (map idfun xs0))
      (internal_paths_rew_r (map idfun xs0) xs0 Coq_paths_refl iH)
      (map_cons idfun x xs0)) xs

(** val map_homot :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a1 list -> 'a2 list
    paths **)

let map_homot f g h xs =
  list_ind Coq_paths_refl (fun x xs0 iH ->
    internal_paths_rew_r (map f (cons x xs0)) (cons (f x) (map f xs0))
      (internal_paths_rew_r (map g (cons x xs0)) (cons (g x) (map g xs0))
        (internal_paths_rew_r (f x) (g x)
          (internal_paths_rew_r (map f xs0) (map g xs0) Coq_paths_refl iH)
          (h x)) (map_cons g x xs0)) (map_cons f x xs0)) xs

(** val foldr1_nil : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 paths **)

let foldr1_nil _ _ =
  Coq_paths_refl

(** val foldr1_cons_nil : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 paths **)

let foldr1_cons_nil _ _ _ =
  Coq_paths_refl

(** val foldr1_cons :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 list -> 'a1 paths **)

let foldr1_cons _ _ _ _ _ =
  Coq_paths_refl

(** val foldr1_map_nil :
    ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a2 paths **)

let foldr1_map_nil _ _ _ =
  Coq_paths_refl

(** val foldr1_map_cons_nil :
    ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 -> 'a2 paths **)

let foldr1_map_cons_nil _ _ _ _ =
  Coq_paths_refl

(** val foldr1_map_cons :
    ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 list ->
    'a2 paths **)

let foldr1_map_cons _ _ _ _ _ _ =
  Coq_paths_refl

(** val foldr1_foldr1_map :
    ('a2 -> 'a2 -> 'a2) -> 'a2 -> ('a1 -> 'a2) -> 'a1 list -> 'a2 paths **)

let foldr1_foldr1_map f b h xs =
  let pr3 = xs.pr1 in
  let xs0 = xs.pr2 in
  (match pr3 with
   | O -> Coq_paths_refl
   | S n ->
     let rec f0 n0 xs1 =
       match n0 with
       | O -> Coq_paths_refl
       | S n1 ->
         let m = (Obj.magic xs1).pr1 in
         let pr4 = (Obj.magic xs1).pr2 in
         let k = pr4.pr1 in
         let xs2 = pr4.pr2 in
         let iHinst = Obj.magic f0 n1 { pr1 = k; pr2 = xs2 } in
         internal_paths_rew_r
           (map h (cons m (cons k { pr1 = n1; pr2 = xs2 })))
           (cons (h m) (map h (cons k { pr1 = n1; pr2 = xs2 })))
           (internal_paths_rew_r (map h (cons k { pr1 = n1; pr2 = xs2 }))
             (cons (h k) (map h { pr1 = n1; pr2 = xs2 }))
             (internal_paths_rew_r
               (foldr1 f b
                 (cons (h m) (cons (h k) (map h { pr1 = n1; pr2 = xs2 }))))
               (f (h m)
                 (foldr1 f b (cons (h k) (map h { pr1 = n1; pr2 = xs2 }))))
               (let iHinst0 =
                  internal_paths_rew (map h (cons k { pr1 = n1; pr2 = xs2 }))
                    iHinst (cons (h k) (map h { pr1 = n1; pr2 = xs2 }))
                    (map_cons h k { pr1 = n1; pr2 = xs2 })
                in
                internal_paths_rew
                  (foldr1_map f b h (cons k { pr1 = n1; pr2 = xs2 }))
                  (foldr1_map_cons f b h m k { pr1 = n1; pr2 = xs2 })
                  (foldr1 f b (cons (h k) (map h { pr1 = n1; pr2 = xs2 })))
                  iHinst0)
               (foldr1_cons f b (h m) (h k) (map h { pr1 = n1; pr2 = xs2 })))
             (map_cons h k { pr1 = n1; pr2 = xs2 }))
           (map_cons h m (cons k { pr1 = n1; pr2 = xs2 }))
     in f0 n xs0)

(** val concatenate : 'a1 list -> 'a1 list -> 'a1 list **)

let concatenate r s =
  foldr cons s r

(** val concatenateStep : 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths **)

let concatenateStep _ _ _ =
  Coq_paths_refl

(** val nil_concatenate : 'a1 list -> 'a1 list paths **)

let nil_concatenate _ =
  Coq_paths_refl

(** val concatenate_nil : 'a1 list -> 'a1 list paths **)

let concatenate_nil r =
  list_ind Coq_paths_refl (fun x xs p ->
    maponpaths (cons x) (concatenate xs nil) xs p) r

(** val assoc_concatenate :
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 list paths **)

let assoc_concatenate r s t =
  list_ind Coq_paths_refl (fun x xs p ->
    internal_paths_rew_r (concatenate (cons x xs) s)
      (cons x (concatenate xs s))
      (internal_paths_rew_r (concatenate (cons x (concatenate xs s)) t)
        (cons x (concatenate (concatenate xs s) t))
        (internal_paths_rew_r (concatenate (cons x xs) (concatenate s t))
          (cons x (concatenate xs (concatenate s t)))
          (internal_paths_rew_r (concatenate (concatenate xs s) t)
            (concatenate xs (concatenate s t)) Coq_paths_refl p)
          (concatenateStep x xs (concatenate s t)))
        (concatenateStep x (concatenate xs s) t)) (concatenateStep x xs s)) r

(** val map_concatenate :
    ('a1 -> 'a2) -> 'a1 list -> 'a1 list -> 'a2 list paths **)

let map_concatenate f r s =
  list_ind Coq_paths_refl (fun x xs p ->
    internal_paths_rew_r (map f (cons x xs)) (cons (f x) (map f xs))
      (internal_paths_rew_r (concatenate (cons x xs) s)
        (cons x (concatenate xs s))
        (internal_paths_rew_r (concatenate (cons (f x) (map f xs)) (map f s))
          (cons (f x) (concatenate (map f xs) (map f s)))
          (internal_paths_rew_r (map f (cons x (concatenate xs s)))
            (cons (f x) (map f (concatenate xs s)))
            (internal_paths_rew_r (map f (concatenate xs s))
              (concatenate (map f xs) (map f s)) Coq_paths_refl p)
            (mapStep f x (concatenate xs s)))
          (concatenateStep (f x) (map f xs) (map f s)))
        (concatenateStep x xs s)) (mapStep f x xs)) r

(** val foldr_concatenate : ('a1 -> 'a2) -> 'a1 list -> 'a2 list paths **)

let foldr_concatenate f l =
  list_ind Coq_paths_refl (fun x l0 iH ->
    internal_paths_rew_r (map (fun x0 -> cons (f x0) nil) (cons x l0))
      (cons (cons (f x) nil) (map (fun x0 -> cons (f x0) nil) l0))
      (internal_paths_rew_r (map f (cons x l0)) (cons (f x) (map f l0))
        (internal_paths_rew_r
          (foldr concatenate nil
            (cons (cons (f x) nil) (map (fun x0 -> cons (f x0) nil) l0)))
          (concatenate (cons (f x) nil)
            (foldr concatenate nil (map (fun x0 -> cons (f x0) nil) l0)))
          (internal_paths_rew_r
            (foldr concatenate nil (map (fun x0 -> cons (f x0) nil) l0))
            (map f l0) Coq_paths_refl iH)
          (foldr_cons concatenate nil (cons (f x) nil)
            (map (fun x0 -> cons (f x0) nil) l0))) (map_cons f x l0))
      (map_cons (fun x0 -> cons (f x0) nil) x l0)) l

(** val foldr1_concatenate : ('a1 -> 'a2) -> 'a1 list -> 'a2 list paths **)

let foldr1_concatenate f l =
  list_ind Coq_paths_refl (fun x ->
    list_ind (fun _ -> Coq_paths_refl) (fun x' l0 _ iH ->
      maponpaths (cons (f x)) (map f (cons x' l0))
        (foldr1 concatenate nil
          (map (fun x0 -> cons (f x0) nil) (cons x' l0))) iH)) l

(** val append : 'a1 -> 'a1 list -> 'a1 list **)

let append x l =
  concatenate l (cons x nil)

(** val appendStep : 'a1 -> 'a1 -> 'a1 list -> 'a1 list paths **)

let appendStep _ _ _ =
  Coq_paths_refl

(** val append_concatenate : 'a1 -> 'a1 list -> 'a1 list -> 'a1 list paths **)

let append_concatenate x l s =
  assoc_concatenate l s (cons x nil)

(** val map_append : ('a1 -> 'a2) -> 'a1 -> 'a1 list -> 'a2 list paths **)

let map_append f x r =
  map_concatenate f r (cons x nil)

(** val reverse : 'a1 list -> 'a1 list **)

let reverse x =
  foldr append nil x

(** val reverse_nil : 'a1 list paths **)

let reverse_nil =
  Coq_paths_refl

(** val reverseStep : 'a1 -> 'a1 list -> 'a1 list paths **)

let reverseStep _ _ =
  Coq_paths_refl

(** val map_reverse : ('a1 -> 'a2) -> 'a1 list -> 'a2 list paths **)

let map_reverse f r =
  list_ind Coq_paths_refl (fun x xs p ->
    internal_paths_rew_r (map f (cons x xs)) (cons (f x) (map f xs))
      (internal_paths_rew_r (reverse (cons x xs)) (append x (reverse xs))
        (internal_paths_rew_r (reverse (cons (f x) (map f xs)))
          (append (f x) (reverse (map f xs)))
          (internal_paths_rew_r (map f (append x (reverse xs)))
            (append (f x) (map f (reverse xs)))
            (internal_paths_rew_r (map f (reverse xs)) (reverse (map f xs))
              Coq_paths_refl p) (map_append f x (reverse xs)))
          (reverseStep (f x) (map f xs))) (reverseStep x xs)) (mapStep f x xs))
    r

(** val reverse_concatenate : 'a1 list -> 'a1 list -> 'a1 list paths **)

let reverse_concatenate l s =
  list_ind Coq_paths_refl (fun x xs p ->
    internal_paths_rew_r (concatenate (cons x xs) s)
      (cons x (concatenate xs s))
      (internal_paths_rew_r (reverse (cons x (concatenate xs s)))
        (append x (reverse (concatenate xs s)))
        (internal_paths_rew_r (reverse (cons x xs)) (append x (reverse xs))
          (internal_paths_rew_r (reverse (concatenate xs s))
            (concatenate (reverse s) (reverse xs))
            (internal_paths_rew_r
              (append x (concatenate (reverse s) (reverse xs)))
              (concatenate (reverse s) (append x (reverse xs)))
              Coq_paths_refl (append_concatenate x (reverse s) (reverse xs)))
            p) (reverseStep x xs)) (reverseStep x (concatenate xs s)))
      (concatenateStep x xs s)) l

(** val reverse_append : 'a1 -> 'a1 list -> 'a1 list paths **)

let reverse_append x l =
  internal_paths_rew_r (reverse (concatenate l (cons x nil)))
    (concatenate (reverse (cons x nil)) (reverse l))
    (internal_paths_rew_r (reverse (cons x nil)) (append x (reverse nil))
      (internal_paths_rew_r (reverse nil) nil Coq_paths_refl reverse_nil)
      (reverseStep x nil)) (reverse_concatenate l (cons x nil))

(** val reverse_reverse : 'a1 list -> 'a1 list paths **)

let reverse_reverse r =
  list_ind Coq_paths_refl (fun x xs p ->
    internal_paths_rew_r (reverse (cons x xs)) (append x (reverse xs))
      (internal_paths_rew_r (reverse (append x (reverse xs)))
        (cons x (reverse (reverse xs)))
        (internal_paths_rew_r (reverse (reverse xs)) xs Coq_paths_refl p)
        (reverse_append x (reverse xs))) (reverseStep x xs)) r

(** val flatten : 'a1 list list -> 'a1 list **)

let flatten x =
  list_ind nil (fun s _ f -> concatenate s f) x

(** val flattenStep : 'a1 list -> 'a1 list list -> 'a1 list paths **)

let flattenStep x m =
  internal_paths_rew_r
    (list_ind nil (fun s _ f -> concatenate s f) (cons x m))
    (concatenate x (list_ind nil (fun s _ f -> concatenate s f) m))
    Coq_paths_refl (list_ind_compute_2 nil (fun s _ f -> concatenate s f) x m)

(** val isofhlevellist : nat -> 'a1 isofhlevel -> 'a1 list isofhlevel **)

let isofhlevellist n is1 =
  isofhleveltotal2 (S (S n))
    (Obj.magic (fun m k -> isofhlevelsnprop n (isasetnat m k))) (fun m ->
    isofhlevelvec (S (S n)) is1 m)

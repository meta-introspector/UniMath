open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a coq_sig = 'a
  (* singleton inductive, whose constructor was exist *)

(** val sig_rect : ('a1 -> __ -> 'a2) -> 'a1 -> 'a2 **)

let sig_rect f s =
  f s __

(** val sig_rec : ('a1 -> __ -> 'a2) -> 'a1 -> 'a2 **)

let sig_rec f s =
  f s __

type 'a sig2 = 'a
  (* singleton inductive, whose constructor was exist2 *)

(** val sig2_rect : ('a1 -> __ -> __ -> 'a2) -> 'a1 sig2 -> 'a2 **)

let sig2_rect f s =
  f s __ __

(** val sig2_rec : ('a1 -> __ -> __ -> 'a2) -> 'a1 sig2 -> 'a2 **)

let sig2_rec f s =
  f s __ __

type ('a, 'p) sigT =
| Coq_existT of 'a * 'p

(** val sigT_rect : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) sigT -> 'a3 **)

let sigT_rect f = function
| Coq_existT (x, p) -> f x p

(** val sigT_rec : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) sigT -> 'a3 **)

let sigT_rec f = function
| Coq_existT (x, p) -> f x p

type ('a, 'p, 'q) sigT2 =
| Coq_existT2 of 'a * 'p * 'q

(** val sigT2_rect :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a3) sigT2 -> 'a4 **)

let sigT2_rect f = function
| Coq_existT2 (x, p, q) -> f x p q

(** val sigT2_rec :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a3) sigT2 -> 'a4 **)

let sigT2_rec f = function
| Coq_existT2 (x, p, q) -> f x p q

(** val proj1_sig : 'a1 -> 'a1 **)

let proj1_sig e =
  e

(** val sig_of_sig2 : 'a1 sig2 -> 'a1 **)

let sig_of_sig2 x =
  x

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| Coq_existT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| Coq_existT (_, h) -> h

module SigTNotations =
 struct
 end

(** val sigT_of_sigT2 : ('a1, 'a2, 'a3) sigT2 -> ('a1, 'a2) sigT **)

let sigT_of_sigT2 x =
  Coq_existT ((let Coq_existT2 (a, _, _) = x in a),
    (let Coq_existT2 (_, p, _) = x in p))

(** val projT3 : ('a1, 'a2, 'a3) sigT2 -> 'a3 **)

let projT3 = function
| Coq_existT2 (_, _, c) -> c

(** val sig_of_sigT : ('a1, __) sigT -> 'a1 **)

let sig_of_sigT =
  projT1

(** val sigT_of_sig : 'a1 -> ('a1, __) sigT **)

let sigT_of_sig x =
  Coq_existT (x, __)

(** val sig2_of_sigT2 : ('a1, __, __) sigT2 -> 'a1 sig2 **)

let sig2_of_sigT2 x =
  projT1 (sigT_of_sigT2 x)

(** val sigT2_of_sig2 : 'a1 sig2 -> ('a1, __, __) sigT2 **)

let sigT2_of_sig2 x =
  Coq_existT2 ((sig_of_sig2 x), __, __)

(** val sigT_of_prod : ('a1, 'a2) prod -> ('a1, 'a2) sigT **)

let sigT_of_prod p =
  Coq_existT ((fst p), (snd p))

(** val prod_of_sigT : ('a1, 'a2) sigT -> ('a1, 'a2) prod **)

let prod_of_sigT s =
  Coq_pair ((projT1 s), (projT2 s))

(** val eq_sigT_rect :
    ('a1, 'a2) sigT -> ('a1, 'a2) sigT -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_sigT_rect _ _ f =
  f __ __

(** val eq_sigT_rec :
    ('a1, 'a2) sigT -> ('a1, 'a2) sigT -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_sigT_rec =
  eq_sigT_rect

(** val eq_sigT_rect_existT_l :
    'a1 -> 'a2 -> ('a1, 'a2) sigT -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_sigT_rect_existT_l u1 u2 v f =
  eq_sigT_rect (Coq_existT (u1, u2)) v f

(** val eq_sigT_rect_existT_r :
    ('a1, 'a2) sigT -> 'a1 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_sigT_rect_existT_r u v1 v2 f =
  eq_sigT_rect u (Coq_existT (v1, v2)) f

(** val eq_sigT_rect_existT :
    'a1 -> 'a2 -> 'a1 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_sigT_rect_existT u1 u2 v1 v2 f =
  eq_sigT_rect (Coq_existT (u1, u2)) (Coq_existT (v1, v2)) f

(** val eq_sigT_rect_uncurried :
    ('a1, 'a2) sigT -> ('a1, 'a2) sigT -> (__ -> 'a3) -> 'a3 **)

let eq_sigT_rect_uncurried u v f =
  eq_sigT_rect u v (fun _ _ -> f __)

(** val eq_sigT_rec_uncurried :
    ('a1, 'a2) sigT -> ('a1, 'a2) sigT -> (__ -> 'a3) -> 'a3 **)

let eq_sigT_rec_uncurried =
  eq_sigT_rect_uncurried

(** val eq_sig_rect : 'a1 -> 'a1 -> (__ -> __ -> 'a2) -> 'a2 **)

let eq_sig_rect _ _ f =
  f __ __

(** val eq_sig_rec : 'a1 -> 'a1 -> (__ -> __ -> 'a2) -> 'a2 **)

let eq_sig_rec =
  eq_sig_rect

(** val eq_sig_rect_exist_l : 'a1 -> 'a1 -> (__ -> __ -> 'a2) -> 'a2 **)

let eq_sig_rect_exist_l =
  eq_sig_rect

(** val eq_sig_rect_exist_r : 'a1 -> 'a1 -> (__ -> __ -> 'a2) -> 'a2 **)

let eq_sig_rect_exist_r =
  eq_sig_rect

(** val eq_sig_rect_exist : 'a1 -> 'a1 -> (__ -> __ -> 'a2) -> 'a2 **)

let eq_sig_rect_exist =
  eq_sig_rect

(** val eq_sig_rect_uncurried : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2 **)

let eq_sig_rect_uncurried u v f =
  eq_sig_rect u v (fun _ _ -> f __)

(** val eq_sig_rec_uncurried : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2 **)

let eq_sig_rec_uncurried =
  eq_sig_rect_uncurried

(** val eq_sigT2_rect :
    ('a1, 'a2, 'a3) sigT2 -> ('a1, 'a2, 'a3) sigT2 -> (__ -> __ -> __ -> 'a4)
    -> 'a4 **)

let eq_sigT2_rect _ _ f =
  f __ __ __

(** val eq_sigT2_rec :
    ('a1, 'a2, 'a3) sigT2 -> ('a1, 'a2, 'a3) sigT2 -> (__ -> __ -> __ -> 'a4)
    -> 'a4 **)

let eq_sigT2_rec =
  eq_sigT2_rect

(** val eq_sigT2_rect_existT2_l :
    'a1 -> 'a2 -> 'a3 -> ('a1, 'a2, 'a3) sigT2 -> (__ -> __ -> __ -> 'a4) ->
    'a4 **)

let eq_sigT2_rect_existT2_l u1 u2 u3 v f =
  eq_sigT2_rect (Coq_existT2 (u1, u2, u3)) v f

(** val eq_sigT2_rect_existT2_r :
    ('a1, 'a2, 'a3) sigT2 -> 'a1 -> 'a2 -> 'a3 -> (__ -> __ -> __ -> 'a4) ->
    'a4 **)

let eq_sigT2_rect_existT2_r u v1 v2 v3 f =
  eq_sigT2_rect u (Coq_existT2 (v1, v2, v3)) f

(** val eq_sigT2_rect_existT2 :
    'a1 -> 'a2 -> 'a3 -> 'a1 -> 'a2 -> 'a3 -> (__ -> __ -> __ -> 'a4) -> 'a4 **)

let eq_sigT2_rect_existT2 u1 u2 u3 v1 v2 v3 f =
  eq_sigT2_rect (Coq_existT2 (u1, u2, u3)) (Coq_existT2 (v1, v2, v3)) f

(** val eq_sigT2_rect_uncurried :
    ('a1, 'a2, 'a3) sigT2 -> ('a1, 'a2, 'a3) sigT2 -> (__ -> 'a4) -> 'a4 **)

let eq_sigT2_rect_uncurried u v f =
  eq_sigT2_rect u v (fun _ _ _ -> f __)

(** val eq_sigT2_rec_uncurried :
    ('a1, 'a2, 'a3) sigT2 -> ('a1, 'a2, 'a3) sigT2 -> (__ -> 'a4) -> 'a4 **)

let eq_sigT2_rec_uncurried =
  eq_sigT2_rect_uncurried

(** val eq_sig2_rect :
    'a1 sig2 -> 'a1 sig2 -> (__ -> __ -> __ -> 'a2) -> 'a2 **)

let eq_sig2_rect _ _ f =
  f __ __ __

(** val eq_sig2_rec :
    'a1 sig2 -> 'a1 sig2 -> (__ -> __ -> __ -> 'a2) -> 'a2 **)

let eq_sig2_rec =
  eq_sig2_rect

(** val eq_sig2_rect_exist2_l :
    'a1 -> 'a1 sig2 -> (__ -> __ -> __ -> 'a2) -> 'a2 **)

let eq_sig2_rect_exist2_l =
  eq_sig2_rect

(** val eq_sig2_rect_exist2_r :
    'a1 sig2 -> 'a1 -> (__ -> __ -> __ -> 'a2) -> 'a2 **)

let eq_sig2_rect_exist2_r =
  eq_sig2_rect

(** val eq_sig2_rect_exist2 : 'a1 -> 'a1 -> (__ -> __ -> __ -> 'a2) -> 'a2 **)

let eq_sig2_rect_exist2 =
  eq_sig2_rect

(** val eq_sig2_rect_uncurried :
    'a1 sig2 -> 'a1 sig2 -> (__ -> 'a2) -> 'a2 **)

let eq_sig2_rect_uncurried u v f =
  eq_sig2_rect u v (fun _ _ _ -> f __)

(** val eq_sig2_rec_uncurried : 'a1 sig2 -> 'a1 sig2 -> (__ -> 'a2) -> 'a2 **)

let eq_sig2_rec_uncurried =
  eq_sig2_rect_uncurried

type sumbool =
| Coq_left
| Coq_right

(** val sumbool_rect : (__ -> 'a1) -> (__ -> 'a1) -> sumbool -> 'a1 **)

let sumbool_rect f f0 = function
| Coq_left -> f __
| Coq_right -> f0 __

(** val sumbool_rec : (__ -> 'a1) -> (__ -> 'a1) -> sumbool -> 'a1 **)

let sumbool_rec f f0 = function
| Coq_left -> f __
| Coq_right -> f0 __

type 'a sumor =
| Coq_inleft of 'a
| Coq_inright

(** val sumor_rect : ('a1 -> 'a2) -> (__ -> 'a2) -> 'a1 sumor -> 'a2 **)

let sumor_rect f f0 = function
| Coq_inleft a -> f a
| Coq_inright -> f0 __

(** val sumor_rec : ('a1 -> 'a2) -> (__ -> 'a2) -> 'a1 sumor -> 'a2 **)

let sumor_rec f f0 = function
| Coq_inleft a -> f a
| Coq_inright -> f0 __

(** val coq_Choice : ('a1 -> 'a2) -> ('a1 -> 'a2) **)

let coq_Choice h =
  h

(** val coq_Choice2 :
    ('a1 -> ('a2, 'a3) sigT) -> ('a1 -> 'a2, 'a1 -> 'a3) sigT **)

let coq_Choice2 h =
  Coq_existT ((fun z -> projT1 (h z)), (fun z ->
    let s = h z in let Coq_existT (_, r) = s in r))

(** val bool_choice : ('a1 -> sumbool) -> ('a1 -> bool) **)

let bool_choice h z =
  match h z with
  | Coq_left -> Coq_true
  | Coq_right -> Coq_false

(** val dependent_choice : ('a1 -> 'a1) -> 'a1 -> (nat -> 'a1) **)

let rec dependent_choice h x0 = function
| O -> x0
| S n' -> h (dependent_choice h x0 n')

type 'a coq_Exc = 'a option

(** val value : 'a1 -> 'a1 option **)

let value x =
  Some x

(** val error : 'a1 option **)

let error =
  None

(** val except : __ -> 'a1 **)

let except _ =
  assert false (* absurd case *)

(** val absurd_set : __ -> 'a1 **)

let absurd_set _ =
  assert false (* absurd case *)

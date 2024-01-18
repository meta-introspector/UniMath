open Datatypes

type __ = Obj.t

type 'a coq_sig = 'a
  (* singleton inductive, whose constructor was exist *)

val sig_rect : ('a1 -> __ -> 'a2) -> 'a1 -> 'a2

val sig_rec : ('a1 -> __ -> 'a2) -> 'a1 -> 'a2

type 'a sig2 = 'a
  (* singleton inductive, whose constructor was exist2 *)

val sig2_rect : ('a1 -> __ -> __ -> 'a2) -> 'a1 sig2 -> 'a2

val sig2_rec : ('a1 -> __ -> __ -> 'a2) -> 'a1 sig2 -> 'a2

type ('a, 'p) sigT =
| Coq_existT of 'a * 'p

val sigT_rect : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) sigT -> 'a3

val sigT_rec : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) sigT -> 'a3

type ('a, 'p, 'q) sigT2 =
| Coq_existT2 of 'a * 'p * 'q

val sigT2_rect : ('a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a3) sigT2 -> 'a4

val sigT2_rec : ('a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a3) sigT2 -> 'a4

val proj1_sig : 'a1 -> 'a1

val sig_of_sig2 : 'a1 sig2 -> 'a1

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2

module SigTNotations :
 sig
 end

val sigT_of_sigT2 : ('a1, 'a2, 'a3) sigT2 -> ('a1, 'a2) sigT

val projT3 : ('a1, 'a2, 'a3) sigT2 -> 'a3

val sig_of_sigT : ('a1, __) sigT -> 'a1

val sigT_of_sig : 'a1 -> ('a1, __) sigT

val sig2_of_sigT2 : ('a1, __, __) sigT2 -> 'a1 sig2

val sigT2_of_sig2 : 'a1 sig2 -> ('a1, __, __) sigT2

val sigT_of_prod : ('a1, 'a2) prod -> ('a1, 'a2) sigT

val prod_of_sigT : ('a1, 'a2) sigT -> ('a1, 'a2) prod

val eq_sigT_rect :
  ('a1, 'a2) sigT -> ('a1, 'a2) sigT -> (__ -> __ -> 'a3) -> 'a3

val eq_sigT_rec :
  ('a1, 'a2) sigT -> ('a1, 'a2) sigT -> (__ -> __ -> 'a3) -> 'a3

val eq_sigT_rect_existT_l :
  'a1 -> 'a2 -> ('a1, 'a2) sigT -> (__ -> __ -> 'a3) -> 'a3

val eq_sigT_rect_existT_r :
  ('a1, 'a2) sigT -> 'a1 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val eq_sigT_rect_existT : 'a1 -> 'a2 -> 'a1 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val eq_sigT_rect_uncurried :
  ('a1, 'a2) sigT -> ('a1, 'a2) sigT -> (__ -> 'a3) -> 'a3

val eq_sigT_rec_uncurried :
  ('a1, 'a2) sigT -> ('a1, 'a2) sigT -> (__ -> 'a3) -> 'a3

val eq_sig_rect : 'a1 -> 'a1 -> (__ -> __ -> 'a2) -> 'a2

val eq_sig_rec : 'a1 -> 'a1 -> (__ -> __ -> 'a2) -> 'a2

val eq_sig_rect_exist_l : 'a1 -> 'a1 -> (__ -> __ -> 'a2) -> 'a2

val eq_sig_rect_exist_r : 'a1 -> 'a1 -> (__ -> __ -> 'a2) -> 'a2

val eq_sig_rect_exist : 'a1 -> 'a1 -> (__ -> __ -> 'a2) -> 'a2

val eq_sig_rect_uncurried : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2

val eq_sig_rec_uncurried : 'a1 -> 'a1 -> (__ -> 'a2) -> 'a2

val eq_sigT2_rect :
  ('a1, 'a2, 'a3) sigT2 -> ('a1, 'a2, 'a3) sigT2 -> (__ -> __ -> __ -> 'a4)
  -> 'a4

val eq_sigT2_rec :
  ('a1, 'a2, 'a3) sigT2 -> ('a1, 'a2, 'a3) sigT2 -> (__ -> __ -> __ -> 'a4)
  -> 'a4

val eq_sigT2_rect_existT2_l :
  'a1 -> 'a2 -> 'a3 -> ('a1, 'a2, 'a3) sigT2 -> (__ -> __ -> __ -> 'a4) -> 'a4

val eq_sigT2_rect_existT2_r :
  ('a1, 'a2, 'a3) sigT2 -> 'a1 -> 'a2 -> 'a3 -> (__ -> __ -> __ -> 'a4) -> 'a4

val eq_sigT2_rect_existT2 :
  'a1 -> 'a2 -> 'a3 -> 'a1 -> 'a2 -> 'a3 -> (__ -> __ -> __ -> 'a4) -> 'a4

val eq_sigT2_rect_uncurried :
  ('a1, 'a2, 'a3) sigT2 -> ('a1, 'a2, 'a3) sigT2 -> (__ -> 'a4) -> 'a4

val eq_sigT2_rec_uncurried :
  ('a1, 'a2, 'a3) sigT2 -> ('a1, 'a2, 'a3) sigT2 -> (__ -> 'a4) -> 'a4

val eq_sig2_rect : 'a1 sig2 -> 'a1 sig2 -> (__ -> __ -> __ -> 'a2) -> 'a2

val eq_sig2_rec : 'a1 sig2 -> 'a1 sig2 -> (__ -> __ -> __ -> 'a2) -> 'a2

val eq_sig2_rect_exist2_l : 'a1 -> 'a1 sig2 -> (__ -> __ -> __ -> 'a2) -> 'a2

val eq_sig2_rect_exist2_r : 'a1 sig2 -> 'a1 -> (__ -> __ -> __ -> 'a2) -> 'a2

val eq_sig2_rect_exist2 : 'a1 -> 'a1 -> (__ -> __ -> __ -> 'a2) -> 'a2

val eq_sig2_rect_uncurried : 'a1 sig2 -> 'a1 sig2 -> (__ -> 'a2) -> 'a2

val eq_sig2_rec_uncurried : 'a1 sig2 -> 'a1 sig2 -> (__ -> 'a2) -> 'a2

type sumbool =
| Coq_left
| Coq_right

val sumbool_rect : (__ -> 'a1) -> (__ -> 'a1) -> sumbool -> 'a1

val sumbool_rec : (__ -> 'a1) -> (__ -> 'a1) -> sumbool -> 'a1

type 'a sumor =
| Coq_inleft of 'a
| Coq_inright

val sumor_rect : ('a1 -> 'a2) -> (__ -> 'a2) -> 'a1 sumor -> 'a2

val sumor_rec : ('a1 -> 'a2) -> (__ -> 'a2) -> 'a1 sumor -> 'a2

val coq_Choice : ('a1 -> 'a2) -> ('a1 -> 'a2)

val coq_Choice2 : ('a1 -> ('a2, 'a3) sigT) -> ('a1 -> 'a2, 'a1 -> 'a3) sigT

val bool_choice : ('a1 -> sumbool) -> ('a1 -> bool)

val dependent_choice : ('a1 -> 'a1) -> 'a1 -> (nat -> 'a1)

type 'a coq_Exc = 'a option

val value : 'a1 -> 'a1 option

val error : 'a1 option

val except : __ -> 'a1

val absurd_set : __ -> 'a1

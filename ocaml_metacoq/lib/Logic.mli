
type __ = Obj.t

val coq_True_rect : 'a1 -> 'a1

val coq_True_rec : 'a1 -> 'a1

val coq_False_rect : __ -> 'a1

val coq_False_rec : __ -> 'a1

val and_rect : (__ -> __ -> 'a1) -> 'a1

val and_rec : (__ -> __ -> 'a1) -> 'a1

val eq_rect : 'a1 -> 'a2 -> 'a1 -> 'a2

val eq_rec : 'a1 -> 'a2 -> 'a1 -> 'a2

val eq_rec_r : 'a1 -> 'a2 -> 'a1 -> 'a2

val eq_rect_r : 'a1 -> 'a2 -> 'a1 -> 'a2

module EqNotations :
 sig
 end

val ex_rect : (__ -> __ -> 'a1) -> 'a1

val ex_rec : (__ -> __ -> 'a1) -> 'a1

val eq_ex_rect : (__ -> __ -> 'a1) -> 'a1

val eq_ex_rec : (__ -> __ -> 'a1) -> 'a1

val eq_ex_rect_ex_intro_l : (__ -> __ -> 'a1) -> 'a1

val eq_ex_rect_ex_intro_r : (__ -> __ -> 'a1) -> 'a1

val eq_ex_rect_ex_intro : (__ -> __ -> 'a1) -> 'a1

val eq_ex_rect_uncurried : (__ -> 'a1) -> 'a1

val eq_ex_rec_uncurried : (__ -> 'a1) -> 'a1

val ex2_rect : (__ -> __ -> __ -> 'a1) -> 'a1

val ex2_rec : (__ -> __ -> __ -> 'a1) -> 'a1

val eq_ex2_rect : (__ -> __ -> __ -> 'a1) -> 'a1

val eq_ex2_rec : (__ -> __ -> __ -> 'a1) -> 'a1

val eq_ex2_rect_ex_intro2_l : (__ -> __ -> __ -> 'a1) -> 'a1

val eq_ex2_rect_ex_intro2_r : (__ -> __ -> __ -> 'a1) -> 'a1

val eq_ex2_rect_ex_intro2 : (__ -> __ -> __ -> 'a1) -> 'a1

val eq_ex2_rect_uncurried : (__ -> 'a1) -> 'a1

val eq_ex2_rec_uncurried : (__ -> 'a1) -> 'a1

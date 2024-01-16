
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_True_rect : 'a1 -> 'a1 **)

let coq_True_rect f =
  f

(** val coq_True_rec : 'a1 -> 'a1 **)

let coq_True_rec f =
  f

(** val coq_False_rect : __ -> 'a1 **)

let coq_False_rect _ =
  assert false (* absurd case *)

(** val coq_False_rec : __ -> 'a1 **)

let coq_False_rec _ =
  assert false (* absurd case *)

(** val and_rect : (__ -> __ -> 'a1) -> 'a1 **)

let and_rect f =
  f __ __

(** val and_rec : (__ -> __ -> 'a1) -> 'a1 **)

let and_rec f =
  f __ __

(** val eq_rect : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let eq_rect _ f _ =
  f

(** val eq_rec : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let eq_rec _ f _ =
  f

(** val eq_rec_r : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let eq_rec_r _ h _ =
  h

(** val eq_rect_r : 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let eq_rect_r _ h _ =
  h

module EqNotations =
 struct
 end

(** val ex_rect : (__ -> __ -> 'a1) -> 'a1 **)

let ex_rect f =
  f __ __

(** val ex_rec : (__ -> __ -> 'a1) -> 'a1 **)

let ex_rec f =
  f __ __

(** val eq_ex_rect : (__ -> __ -> 'a1) -> 'a1 **)

let eq_ex_rect f =
  f __ __

(** val eq_ex_rec : (__ -> __ -> 'a1) -> 'a1 **)

let eq_ex_rec =
  eq_ex_rect

(** val eq_ex_rect_ex_intro_l : (__ -> __ -> 'a1) -> 'a1 **)

let eq_ex_rect_ex_intro_l =
  eq_ex_rect

(** val eq_ex_rect_ex_intro_r : (__ -> __ -> 'a1) -> 'a1 **)

let eq_ex_rect_ex_intro_r =
  eq_ex_rect

(** val eq_ex_rect_ex_intro : (__ -> __ -> 'a1) -> 'a1 **)

let eq_ex_rect_ex_intro =
  eq_ex_rect

(** val eq_ex_rect_uncurried : (__ -> 'a1) -> 'a1 **)

let eq_ex_rect_uncurried f =
  eq_ex_rect (fun _ _ -> f __)

(** val eq_ex_rec_uncurried : (__ -> 'a1) -> 'a1 **)

let eq_ex_rec_uncurried =
  eq_ex_rect_uncurried

(** val ex2_rect : (__ -> __ -> __ -> 'a1) -> 'a1 **)

let ex2_rect f =
  f __ __ __

(** val ex2_rec : (__ -> __ -> __ -> 'a1) -> 'a1 **)

let ex2_rec f =
  f __ __ __

(** val eq_ex2_rect : (__ -> __ -> __ -> 'a1) -> 'a1 **)

let eq_ex2_rect f =
  f __ __ __

(** val eq_ex2_rec : (__ -> __ -> __ -> 'a1) -> 'a1 **)

let eq_ex2_rec =
  eq_ex2_rect

(** val eq_ex2_rect_ex_intro2_l : (__ -> __ -> __ -> 'a1) -> 'a1 **)

let eq_ex2_rect_ex_intro2_l =
  eq_ex2_rect

(** val eq_ex2_rect_ex_intro2_r : (__ -> __ -> __ -> 'a1) -> 'a1 **)

let eq_ex2_rect_ex_intro2_r =
  eq_ex2_rect

(** val eq_ex2_rect_ex_intro2 : (__ -> __ -> __ -> 'a1) -> 'a1 **)

let eq_ex2_rect_ex_intro2 =
  eq_ex2_rect

(** val eq_ex2_rect_uncurried : (__ -> 'a1) -> 'a1 **)

let eq_ex2_rect_uncurried f =
  eq_ex2_rect (fun _ _ _ -> f __)

(** val eq_ex2_rec_uncurried : (__ -> 'a1) -> 'a1 **)

let eq_ex2_rec_uncurried =
  eq_ex2_rect_uncurried

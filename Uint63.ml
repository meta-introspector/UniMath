open BinInt
open BinNums
open Bool
open CarryType
open Datatypes
open Nat
open PrimInt63
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val size : nat **)

let size =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

module Uint63NotationsInternalB =
 struct
 end

(** val digits : int **)

let digits =
  (Uint63.of_int (63))

(** val max_int : int **)

let max_int =
  (Uint63.of_int (-1))

(** val get_digit : int -> int -> bool **)

let get_digit x p =
  ltb (Uint63.of_int (0)) (coq_land x (coq_lsl (Uint63.of_int (1)) p))

(** val set_digit : int -> int -> bool -> int **)

let set_digit x p b =
  match match leb (Uint63.of_int (0)) p with
        | Coq_true -> ltb p digits
        | Coq_false -> Coq_false with
  | Coq_true ->
    (match b with
     | Coq_true -> coq_lor x (coq_lsl (Uint63.of_int (1)) p)
     | Coq_false ->
       coq_land x (coq_lxor max_int (coq_lsl (Uint63.of_int (1)) p)))
  | Coq_false -> x

(** val is_zero : int -> bool **)

let is_zero i =
  eqb i (Uint63.of_int (0))

(** val is_even : int -> bool **)

let is_even i =
  is_zero (coq_land i (Uint63.of_int (1)))

(** val bit : int -> int -> bool **)

let bit i n =
  negb (is_zero (coq_lsl (coq_lsr i n) (sub digits (Uint63.of_int (1)))))

(** val opp : int -> int **)

let opp i =
  sub (Uint63.of_int (0)) i

(** val oppcarry : int -> int **)

let oppcarry i =
  sub max_int i

(** val succ : int -> int **)

let succ i =
  add i (Uint63.of_int (1))

(** val pred : int -> int **)

let pred i =
  sub i (Uint63.of_int (1))

(** val addcarry : int -> int -> int **)

let addcarry i j =
  add (add i j) (Uint63.of_int (1))

(** val subcarry : int -> int -> int **)

let subcarry i j =
  sub (sub i j) (Uint63.of_int (1))

(** val addc_def : int -> int -> int carry **)

let addc_def x y =
  let r = add x y in (match ltb r x with
                      | Coq_true -> C1 r
                      | Coq_false -> C0 r)

(** val addcarryc_def : int -> int -> int carry **)

let addcarryc_def x y =
  let r = addcarry x y in
  (match leb r x with
   | Coq_true -> C1 r
   | Coq_false -> C0 r)

(** val subc_def : int -> int -> int carry **)

let subc_def x y =
  match leb y x with
  | Coq_true -> C0 (sub x y)
  | Coq_false -> C1 (sub x y)

(** val subcarryc_def : int -> int -> int carry **)

let subcarryc_def x y =
  match ltb y x with
  | Coq_true -> C0 (sub (sub x y) (Uint63.of_int (1)))
  | Coq_false -> C1 (sub (sub x y) (Uint63.of_int (1)))

(** val diveucl_def : int -> int -> (int, int) prod **)

let diveucl_def x y =
  Coq_pair ((div x y), (coq_mod x y))

(** val addmuldiv_def : int -> int -> int -> int **)

let addmuldiv_def p x y =
  coq_lor (coq_lsl x p) (coq_lsr y (sub digits p))

module Uint63NotationsInternalC =
 struct
 end

(** val oppc : int -> int carry **)

let oppc i =
  subc (Uint63.of_int (0)) i

(** val succc : int -> int carry **)

let succc i =
  addc i (Uint63.of_int (1))

(** val predc : int -> int carry **)

let predc i =
  subc i (Uint63.of_int (1))

(** val compare_def : int -> int -> comparison **)

let compare_def x y =
  match ltb x y with
  | Coq_true -> Lt
  | Coq_false -> (match eqb x y with
                  | Coq_true -> Eq
                  | Coq_false -> Gt)

(** val to_Z_rec : nat -> int -> coq_Z **)

let rec to_Z_rec n i =
  match n with
  | O -> Z0
  | S n0 ->
    (match is_even i with
     | Coq_true -> Z.double (to_Z_rec n0 (coq_lsr i (Uint63.of_int (1))))
     | Coq_false ->
       Z.succ_double (to_Z_rec n0 (coq_lsr i (Uint63.of_int (1)))))

(** val to_Z : int -> coq_Z **)

let to_Z =
  to_Z_rec size

(** val of_pos_rec : nat -> positive -> int **)

let rec of_pos_rec n p =
  match n with
  | O -> (Uint63.of_int (0))
  | S n0 ->
    (match p with
     | Coq_xI p0 ->
       coq_lor (coq_lsl (of_pos_rec n0 p0) (Uint63.of_int (1)))
         (Uint63.of_int (1))
     | Coq_xO p0 -> coq_lsl (of_pos_rec n0 p0) (Uint63.of_int (1))
     | Coq_xH -> (Uint63.of_int (1)))

(** val of_pos : positive -> int **)

let of_pos =
  of_pos_rec size

(** val of_Z : coq_Z -> int **)

let of_Z = function
| Z0 -> (Uint63.of_int (0))
| Zpos p -> of_pos p
| Zneg p -> opp (of_pos p)

(** val wB : coq_Z **)

let wB =
  Z.pow (Zpos (Coq_xO Coq_xH)) (Z.of_nat size)

module Uint63NotationsInternalD =
 struct
 end

(** val sqrt_step : (int -> int -> int) -> int -> int -> int **)

let sqrt_step rec0 i j =
  let quo = div i j in
  (match ltb quo j with
   | Coq_true -> rec0 i (coq_lsr (add j quo) (Uint63.of_int (1)))
   | Coq_false -> j)

(** val iter_sqrt : nat -> (int -> int -> int) -> int -> int -> int **)

let rec iter_sqrt n rec0 i j =
  let quo = div i j in
  (match ltb quo j with
   | Coq_true ->
     (match n with
      | O -> rec0 i (coq_lsr (add j quo) (Uint63.of_int (1)))
      | S n0 ->
        iter_sqrt n0 (iter_sqrt n0 rec0) i
          (coq_lsr (add j quo) (Uint63.of_int (1))))
   | Coq_false -> j)

(** val sqrt : int -> int **)

let sqrt i =
  match compare (Uint63.of_int (1)) i with
  | Eq -> (Uint63.of_int (1))
  | Lt -> iter_sqrt size (fun _ j -> j) i (coq_lsr i (Uint63.of_int (1)))
  | Gt -> (Uint63.of_int (0))

(** val high_bit : int **)

let high_bit =
  coq_lsl (Uint63.of_int (1)) (sub digits (Uint63.of_int (1)))

(** val sqrt2_step :
    (int -> int -> int -> int) -> int -> int -> int -> int **)

let sqrt2_step rec0 ih il j =
  match ltb ih j with
  | Coq_true ->
    let Coq_pair (quo, _) = diveucl_21 ih il j in
    (match ltb quo j with
     | Coq_true ->
       (match addc j quo with
        | C0 m1 -> rec0 ih il (coq_lsr m1 (Uint63.of_int (1)))
        | C1 m1 -> rec0 ih il (add (coq_lsr m1 (Uint63.of_int (1))) high_bit))
     | Coq_false -> j)
  | Coq_false -> j

(** val iter2_sqrt :
    nat -> (int -> int -> int -> int) -> int -> int -> int -> int **)

let rec iter2_sqrt n rec0 ih il j =
  match ltb ih j with
  | Coq_true ->
    let Coq_pair (quo, _) = diveucl_21 ih il j in
    (match ltb quo j with
     | Coq_true ->
       (match addc j quo with
        | C0 m1 ->
          (match n with
           | O -> rec0 ih il (coq_lsr m1 (Uint63.of_int (1)))
           | S n0 ->
             iter2_sqrt n0 (iter2_sqrt n0 rec0) ih il
               (coq_lsr m1 (Uint63.of_int (1))))
        | C1 m1 ->
          (match n with
           | O -> rec0 ih il (add (coq_lsr m1 (Uint63.of_int (1))) high_bit)
           | S n0 ->
             iter2_sqrt n0 (iter2_sqrt n0 rec0) ih il
               (add (coq_lsr m1 (Uint63.of_int (1))) high_bit)))
     | Coq_false -> j)
  | Coq_false -> j

(** val sqrt2 : int -> int -> (int, int carry) prod **)

let sqrt2 ih il =
  let s = iter2_sqrt size (fun _ _ j -> j) ih il max_int in
  let Coq_pair (ih1, il1) = mulc s s in
  (match subc il il1 with
   | C0 il2 ->
     (match ltb ih1 ih with
      | Coq_true -> Coq_pair (s, (C1 il2))
      | Coq_false -> Coq_pair (s, (C0 il2)))
   | C1 il2 ->
     (match ltb ih1 (sub ih (Uint63.of_int (1))) with
      | Coq_true -> Coq_pair (s, (C1 il2))
      | Coq_false -> Coq_pair (s, (C0 il2))))

(** val gcd_rec : nat -> int -> int -> int **)

let rec gcd_rec guard i j =
  match guard with
  | O -> (Uint63.of_int (1))
  | S p ->
    (match eqb j (Uint63.of_int (0)) with
     | Coq_true -> i
     | Coq_false -> gcd_rec p j (coq_mod i j))

(** val gcd : int -> int -> int **)

let gcd =
  gcd_rec (Nat.mul (S (S O)) size)

(** val eqs : int -> int -> sumbool **)

let eqs i j =
  match eqb i j with
  | Coq_true -> Coq_left
  | Coq_false -> Coq_right

(** val cast : int -> int -> (__ -> __ -> __) option **)

let cast i j =
  match eqb i j with
  | Coq_true -> Some (fun _ hi -> hi)
  | Coq_false -> None

(** val eqo : int -> int -> __ option **)

let eqo i j =
  match eqb i j with
  | Coq_true -> Some __
  | Coq_false -> None

(** val eqbP : int -> int -> reflect **)

let eqbP x y =
  iff_reflect (eqb x y)

(** val ltbP : int -> int -> reflect **)

let ltbP x y =
  iff_reflect (ltb x y)

(** val lebP : int -> int -> reflect **)

let lebP x y =
  iff_reflect (leb x y)

(** val b2i : bool -> int **)

let b2i = function
| Coq_true -> (Uint63.of_int (1))
| Coq_false -> (Uint63.of_int (0))

module Uint63Notations =
 struct
 end

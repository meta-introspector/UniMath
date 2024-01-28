open BinNat
open BinNums
open Bool
open Byte
open Datatypes
open Specif

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val ascii_rect :
    (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
    ascii -> 'a1 **)

let ascii_rect f = function
| Ascii (b, b0, b1, b2, b3, b4, b5, b6) -> f b b0 b1 b2 b3 b4 b5 b6

(** val ascii_rec :
    (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
    ascii -> 'a1 **)

let ascii_rec f = function
| Ascii (b, b0, b1, b2, b3, b4, b5, b6) -> f b b0 b1 b2 b3 b4 b5 b6

(** val zero : ascii **)

let zero =
  Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
    Coq_false, Coq_false)

(** val one : ascii **)

let one =
  Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_false, Coq_false,
    Coq_false, Coq_false)

(** val shift : bool -> ascii -> ascii **)

let shift c = function
| Ascii (a1, a2, a3, a4, a5, a6, a7, _) ->
  Ascii (c, a1, a2, a3, a4, a5, a6, a7)

(** val ascii_dec : ascii -> ascii -> sumbool **)

let ascii_dec a b =
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  (match bool_dec b0 b8 with
   | Coq_left ->
     (match bool_dec b1 b9 with
      | Coq_left ->
        (match bool_dec b2 b10 with
         | Coq_left ->
           (match bool_dec b3 b11 with
            | Coq_left ->
              (match bool_dec b4 b12 with
               | Coq_left ->
                 (match bool_dec b5 b13 with
                  | Coq_left ->
                    (match bool_dec b6 b14 with
                     | Coq_left -> bool_dec b7 b15
                     | Coq_right -> Coq_right)
                  | Coq_right -> Coq_right)
               | Coq_right -> Coq_right)
            | Coq_right -> Coq_right)
         | Coq_right -> Coq_right)
      | Coq_right -> Coq_right)
   | Coq_right -> Coq_right)

(** val eqb : ascii -> ascii -> bool **)

let eqb a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | Coq_true -> eqb a1 b1
                                       | Coq_false -> Coq_false with
                                 | Coq_true -> eqb a2 b2
                                 | Coq_false -> Coq_false with
                           | Coq_true -> eqb a3 b3
                           | Coq_false -> Coq_false with
                     | Coq_true -> eqb a4 b4
                     | Coq_false -> Coq_false with
               | Coq_true -> eqb a5 b5
               | Coq_false -> Coq_false with
         | Coq_true -> eqb a6 b6
         | Coq_false -> Coq_false with
   | Coq_true -> eqb a7 b7
   | Coq_false -> Coq_false)

(** val eqb_spec : ascii -> ascii -> reflect **)

let eqb_spec a b =
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = a in
  let Ascii (b8, b9, b10, b11, b12, b13, b14, b15) = b in
  (match eqb_spec b0 b8 with
   | ReflectT ->
     (match eqb_spec b1 b9 with
      | ReflectT ->
        (match eqb_spec b2 b10 with
         | ReflectT ->
           (match eqb_spec b3 b11 with
            | ReflectT ->
              (match eqb_spec b4 b12 with
               | ReflectT ->
                 (match eqb_spec b5 b13 with
                  | ReflectT ->
                    (match eqb_spec b6 b14 with
                     | ReflectT -> eqb_spec b7 b15
                     | ReflectF -> ReflectF)
                  | ReflectF -> ReflectF)
               | ReflectF -> ReflectF)
            | ReflectF -> ReflectF)
         | ReflectF -> ReflectF)
      | ReflectF -> ReflectF)
   | ReflectF -> ReflectF)

(** val ascii_of_pos : positive -> ascii **)

let ascii_of_pos =
  let rec loop n p =
    match n with
    | O -> zero
    | S n' ->
      (match p with
       | Coq_xI p' -> shift Coq_true (loop n' p')
       | Coq_xO p' -> shift Coq_false (loop n' p')
       | Coq_xH -> one)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : coq_N -> ascii **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : nat -> ascii **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val coq_N_of_digits : bool list -> coq_N **)

let rec coq_N_of_digits = function
| Coq_nil -> N0
| Coq_cons (b, l') ->
  N.add (match b with
         | Coq_true -> Npos Coq_xH
         | Coq_false -> N0)
    (N.mul (Npos (Coq_xO Coq_xH)) (coq_N_of_digits l'))

(** val coq_N_of_ascii : ascii -> coq_N **)

let coq_N_of_ascii = function
| Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
  coq_N_of_digits (Coq_cons (a0, (Coq_cons (a1, (Coq_cons (a2, (Coq_cons (a3,
    (Coq_cons (a4, (Coq_cons (a5, (Coq_cons (a6, (Coq_cons (a7,
    Coq_nil))))))))))))))))

(** val nat_of_ascii : ascii -> nat **)

let nat_of_ascii a =
  N.to_nat (coq_N_of_ascii a)

(** val compare : ascii -> ascii -> comparison **)

let compare a b =
  N.compare (coq_N_of_ascii a) (coq_N_of_ascii b)

(** val ltb : ascii -> ascii -> bool **)

let ltb a b =
  match compare a b with
  | Lt -> Coq_true
  | _ -> Coq_false

(** val leb : ascii -> ascii -> bool **)

let leb a b =
  match compare a b with
  | Gt -> Coq_false
  | _ -> Coq_true

(** val ascii_of_byte : byte -> ascii **)

let ascii_of_byte b =
  let Coq_pair (b0, p) = to_bits b in
  let Coq_pair (b1, p0) = p in
  let Coq_pair (b2, p1) = p0 in
  let Coq_pair (b3, p2) = p1 in
  let Coq_pair (b4, p3) = p2 in
  let Coq_pair (b5, p4) = p3 in
  let Coq_pair (b6, b7) = p4 in Ascii (b0, b1, b2, b3, b4, b5, b6, b7)

(** val byte_of_ascii : ascii -> byte **)

let byte_of_ascii = function
| Ascii (b0, b1, b2, b3, b4, b5, b6, b7) ->
  of_bits (Coq_pair (b0, (Coq_pair (b1, (Coq_pair (b2, (Coq_pair (b3,
    (Coq_pair (b4, (Coq_pair (b5, (Coq_pair (b6, b7))))))))))))))

module AsciiSyntax =
 struct
 end

(** val coq_Space : ascii **)

let coq_Space =
  Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
    Coq_false, Coq_false)

(** val coq_DoubleQuote : ascii **)

let coq_DoubleQuote =
  Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
    Coq_false, Coq_false)

(** val coq_Beep : ascii **)

let coq_Beep =
  Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_false, Coq_false,
    Coq_false, Coq_false)

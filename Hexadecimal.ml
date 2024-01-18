open Datatypes
open Decimal
open Specif

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint
| Da of uint
| Db of uint
| Dc of uint
| Dd of uint
| De of uint
| Df of uint

(** val uint_rect :
    'a1 -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> uint -> 'a1 **)

let rec uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
| Nil -> f
| D0 u0 ->
  f0 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D1 u0 ->
  f1 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D2 u0 ->
  f2 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D3 u0 ->
  f3 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D4 u0 ->
  f4 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D5 u0 ->
  f5 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D6 u0 ->
  f6 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D7 u0 ->
  f7 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D8 u0 ->
  f8 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D9 u0 ->
  f9 u0 (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| Da u0 ->
  f10 u0
    (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| Db u0 ->
  f11 u0
    (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| Dc u0 ->
  f12 u0
    (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| Dd u0 ->
  f13 u0
    (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| De u0 ->
  f14 u0
    (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| Df u0 ->
  f15 u0
    (uint_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)

(** val uint_rec :
    'a1 -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 -> 'a1) -> (uint -> 'a1 ->
    'a1) -> (uint -> 'a1 -> 'a1) -> uint -> 'a1 **)

let rec uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
| Nil -> f
| D0 u0 ->
  f0 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D1 u0 ->
  f1 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D2 u0 ->
  f2 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D3 u0 ->
  f3 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D4 u0 ->
  f4 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D5 u0 ->
  f5 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D6 u0 ->
  f6 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D7 u0 ->
  f7 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D8 u0 ->
  f8 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| D9 u0 ->
  f9 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| Da u0 ->
  f10 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| Db u0 ->
  f11 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| Dc u0 ->
  f12 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| Dd u0 ->
  f13 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| De u0 ->
  f14 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)
| Df u0 ->
  f15 u0 (uint_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 u0)

type signed_int =
| Pos of uint
| Neg of uint

type hexadecimal =
| Hexadecimal of signed_int * uint
| HexadecimalExp of signed_int * uint * Decimal.signed_int

(** val uint_beq : uint -> uint -> bool **)

let rec uint_beq x y =
  match x with
  | Nil -> (match y with
            | Nil -> Coq_true
            | _ -> Coq_false)
  | D0 x0 -> (match y with
              | D0 x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | D1 x0 -> (match y with
              | D1 x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | D2 x0 -> (match y with
              | D2 x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | D3 x0 -> (match y with
              | D3 x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | D4 x0 -> (match y with
              | D4 x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | D5 x0 -> (match y with
              | D5 x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | D6 x0 -> (match y with
              | D6 x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | D7 x0 -> (match y with
              | D7 x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | D8 x0 -> (match y with
              | D8 x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | D9 x0 -> (match y with
              | D9 x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | Da x0 -> (match y with
              | Da x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | Db x0 -> (match y with
              | Db x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | Dc x0 -> (match y with
              | Dc x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | Dd x0 -> (match y with
              | Dd x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | De x0 -> (match y with
              | De x1 -> uint_beq x0 x1
              | _ -> Coq_false)
  | Df x0 -> (match y with
              | Df x1 -> uint_beq x0 x1
              | _ -> Coq_false)

(** val uint_eq_dec : uint -> uint -> sumbool **)

let uint_eq_dec x y =
  let b = uint_beq x y in
  (match b with
   | Coq_true -> Coq_left
   | Coq_false -> Coq_right)

(** val signed_int_beq : signed_int -> signed_int -> bool **)

let signed_int_beq x y =
  match x with
  | Pos d -> (match y with
              | Pos d0 -> uint_beq d d0
              | Neg _ -> Coq_false)
  | Neg d -> (match y with
              | Pos _ -> Coq_false
              | Neg d0 -> uint_beq d d0)

(** val signed_int_eq_dec : signed_int -> signed_int -> sumbool **)

let signed_int_eq_dec x y =
  let b = signed_int_beq x y in
  (match b with
   | Coq_true -> Coq_left
   | Coq_false -> Coq_right)

(** val hexadecimal_beq : hexadecimal -> hexadecimal -> bool **)

let hexadecimal_beq x y =
  match x with
  | Hexadecimal (i, f) ->
    (match y with
     | Hexadecimal (i0, f0) ->
       (match signed_int_beq i i0 with
        | Coq_true -> uint_beq f f0
        | Coq_false -> Coq_false)
     | HexadecimalExp (_, _, _) -> Coq_false)
  | HexadecimalExp (i, f, e) ->
    (match y with
     | Hexadecimal (_, _) -> Coq_false
     | HexadecimalExp (i0, f0, e0) ->
       (match signed_int_beq i i0 with
        | Coq_true ->
          (match uint_beq f f0 with
           | Coq_true -> Decimal.signed_int_beq e e0
           | Coq_false -> Coq_false)
        | Coq_false -> Coq_false))

(** val hexadecimal_eq_dec : hexadecimal -> hexadecimal -> sumbool **)

let hexadecimal_eq_dec x y =
  let b = hexadecimal_beq x y in
  (match b with
   | Coq_true -> Coq_left
   | Coq_false -> Coq_right)

(** val nb_digits : uint -> nat **)

let rec nb_digits = function
| Nil -> O
| D0 d0 -> S (nb_digits d0)
| D1 d0 -> S (nb_digits d0)
| D2 d0 -> S (nb_digits d0)
| D3 d0 -> S (nb_digits d0)
| D4 d0 -> S (nb_digits d0)
| D5 d0 -> S (nb_digits d0)
| D6 d0 -> S (nb_digits d0)
| D7 d0 -> S (nb_digits d0)
| D8 d0 -> S (nb_digits d0)
| D9 d0 -> S (nb_digits d0)
| Da d0 -> S (nb_digits d0)
| Db d0 -> S (nb_digits d0)
| Dc d0 -> S (nb_digits d0)
| Dd d0 -> S (nb_digits d0)
| De d0 -> S (nb_digits d0)
| Df d0 -> S (nb_digits d0)

(** val nzhead : uint -> uint **)

let rec nzhead d = match d with
| D0 d0 -> nzhead d0
| _ -> d

(** val unorm : uint -> uint **)

let unorm d =
  match nzhead d with
  | Nil -> D0 Nil
  | x -> x

(** val norm : signed_int -> signed_int **)

let norm = function
| Pos d0 -> Pos (unorm d0)
| Neg d0 -> (match nzhead d0 with
             | Nil -> Pos (D0 Nil)
             | x -> Neg x)

(** val opp : signed_int -> signed_int **)

let opp = function
| Pos d0 -> Neg d0
| Neg d0 -> Pos d0

(** val abs : signed_int -> uint **)

let abs = function
| Pos d0 -> d0
| Neg d0 -> d0

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')
  | Da d0 -> revapp d0 (Da d')
  | Db d0 -> revapp d0 (Db d')
  | Dc d0 -> revapp d0 (Dc d')
  | Dd d0 -> revapp d0 (Dd d')
  | De d0 -> revapp d0 (De d')
  | Df d0 -> revapp d0 (Df d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil

(** val app : uint -> uint -> uint **)

let app d d' =
  revapp (rev d) d'

(** val app_int : signed_int -> uint -> signed_int **)

let app_int d1 d2 =
  match d1 with
  | Pos d3 -> Pos (app d3 d2)
  | Neg d3 -> Neg (app d3 d2)

(** val nztail : uint -> (uint, nat) prod **)

let nztail d =
  let aux =
    let rec aux d_rev = match d_rev with
    | D0 d_rev0 -> let Coq_pair (r, n) = aux d_rev0 in Coq_pair (r, (S n))
    | _ -> Coq_pair (d_rev, O)
    in aux
  in
  let Coq_pair (r, n) = aux (rev d) in Coq_pair ((rev r), n)

(** val nztail_int : signed_int -> (signed_int, nat) prod **)

let nztail_int = function
| Pos d0 -> let Coq_pair (r, n) = nztail d0 in Coq_pair ((Pos r), n)
| Neg d0 -> let Coq_pair (r, n) = nztail d0 in Coq_pair ((Neg r), n)

(** val del_head : nat -> uint -> uint **)

let rec del_head n d =
  match n with
  | O -> d
  | S n0 ->
    (match d with
     | Nil -> D0 Nil
     | D0 d0 -> del_head n0 d0
     | D1 d0 -> del_head n0 d0
     | D2 d0 -> del_head n0 d0
     | D3 d0 -> del_head n0 d0
     | D4 d0 -> del_head n0 d0
     | D5 d0 -> del_head n0 d0
     | D6 d0 -> del_head n0 d0
     | D7 d0 -> del_head n0 d0
     | D8 d0 -> del_head n0 d0
     | D9 d0 -> del_head n0 d0
     | Da d0 -> del_head n0 d0
     | Db d0 -> del_head n0 d0
     | Dc d0 -> del_head n0 d0
     | Dd d0 -> del_head n0 d0
     | De d0 -> del_head n0 d0
     | Df d0 -> del_head n0 d0)

(** val del_head_int : nat -> signed_int -> uint **)

let del_head_int n = function
| Pos d0 -> del_head n d0
| Neg d0 -> del_head n d0

(** val del_tail : nat -> uint -> uint **)

let del_tail n d =
  rev (del_head n (rev d))

(** val del_tail_int : nat -> signed_int -> signed_int **)

let del_tail_int n = function
| Pos d0 -> Pos (del_tail n d0)
| Neg d0 -> Neg (del_tail n d0)

module Little =
 struct
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> Da d0
  | Da d0 -> Db d0
  | Db d0 -> Dc d0
  | Dc d0 -> Dd d0
  | Dd d0 -> De d0
  | De d0 -> Df d0
  | Df d0 -> D0 (succ d0)

  (** val double : uint -> uint **)

  let rec double = function
  | Nil -> Nil
  | D0 d0 -> D0 (double d0)
  | D1 d0 -> D2 (double d0)
  | D2 d0 -> D4 (double d0)
  | D3 d0 -> D6 (double d0)
  | D4 d0 -> D8 (double d0)
  | D5 d0 -> Da (double d0)
  | D6 d0 -> Dc (double d0)
  | D7 d0 -> De (double d0)
  | D8 d0 -> D0 (succ_double d0)
  | D9 d0 -> D2 (succ_double d0)
  | Da d0 -> D4 (succ_double d0)
  | Db d0 -> D6 (succ_double d0)
  | Dc d0 -> D8 (succ_double d0)
  | Dd d0 -> Da (succ_double d0)
  | De d0 -> Dc (succ_double d0)
  | Df d0 -> De (succ_double d0)

  (** val succ_double : uint -> uint **)

  and succ_double = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 (double d0)
  | D1 d0 -> D3 (double d0)
  | D2 d0 -> D5 (double d0)
  | D3 d0 -> D7 (double d0)
  | D4 d0 -> D9 (double d0)
  | D5 d0 -> Db (double d0)
  | D6 d0 -> Dd (double d0)
  | D7 d0 -> Df (double d0)
  | D8 d0 -> D1 (succ_double d0)
  | D9 d0 -> D3 (succ_double d0)
  | Da d0 -> D5 (succ_double d0)
  | Db d0 -> D7 (succ_double d0)
  | Dc d0 -> D9 (succ_double d0)
  | Dd d0 -> Db (succ_double d0)
  | De d0 -> Dd (succ_double d0)
  | Df d0 -> Df (succ_double d0)
 end

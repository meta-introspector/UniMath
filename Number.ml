open Datatypes
open Decimal
open Hexadecimal
open Specif

type uint =
| UIntDecimal of Decimal.uint
| UIntHexadecimal of Hexadecimal.uint

type signed_int =
| IntDecimal of Decimal.signed_int
| IntHexadecimal of Hexadecimal.signed_int

type number =
| Decimal of decimal
| Hexadecimal of hexadecimal

(** val uint_beq : uint -> uint -> bool **)

let uint_beq x y =
  match x with
  | UIntDecimal u ->
    (match y with
     | UIntDecimal u0 -> Decimal.uint_beq u u0
     | UIntHexadecimal _ -> Coq_false)
  | UIntHexadecimal u ->
    (match y with
     | UIntDecimal _ -> Coq_false
     | UIntHexadecimal u0 -> uint_beq u u0)

(** val uint_eq_dec : uint -> uint -> sumbool **)

let uint_eq_dec x y =
  let b = uint_beq x y in
  (match b with
   | Coq_true -> Coq_left
   | Coq_false -> Coq_right)

(** val signed_int_beq : signed_int -> signed_int -> bool **)

let signed_int_beq x y =
  match x with
  | IntDecimal i ->
    (match y with
     | IntDecimal i0 -> Decimal.signed_int_beq i i0
     | IntHexadecimal _ -> Coq_false)
  | IntHexadecimal i ->
    (match y with
     | IntDecimal _ -> Coq_false
     | IntHexadecimal i0 -> signed_int_beq i i0)

(** val signed_int_eq_dec : signed_int -> signed_int -> sumbool **)

let signed_int_eq_dec x y =
  let b = signed_int_beq x y in
  (match b with
   | Coq_true -> Coq_left
   | Coq_false -> Coq_right)

(** val number_beq : number -> number -> bool **)

let number_beq x y =
  match x with
  | Decimal d ->
    (match y with
     | Decimal d0 -> decimal_beq d d0
     | Hexadecimal _ -> Coq_false)
  | Hexadecimal h ->
    (match y with
     | Decimal _ -> Coq_false
     | Hexadecimal h0 -> hexadecimal_beq h h0)

(** val number_eq_dec : number -> number -> sumbool **)

let number_eq_dec x y =
  let b = number_beq x y in
  (match b with
   | Coq_true -> Coq_left
   | Coq_false -> Coq_right)

(** val uint_of_uint : uint -> uint **)

let uint_of_uint i =
  i

(** val int_of_int : signed_int -> signed_int **)

let int_of_int i =
  i

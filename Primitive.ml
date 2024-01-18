open BinInt
open BinPos
open Byte
open Classes
open Datatypes
open DecimalString
open FloatOps
open HexadecimalString
open MCString
open PrimFloat
open PrimInt63
open SpecFloat
open Specif
open Uint63
open Bytestring

type prim_tag =
| Coq_primInt
| Coq_primFloat

(** val coq_NoConfusionPackage_prim_tag : prim_tag coq_NoConfusionPackage **)

let coq_NoConfusionPackage_prim_tag =
  Build_NoConfusionPackage

(** val prim_tag_eqdec : prim_tag -> prim_tag -> prim_tag dec_eq **)

let prim_tag_eqdec x y =
  match x with
  | Coq_primInt ->
    (match y with
     | Coq_primInt -> Coq_left
     | Coq_primFloat -> Coq_right)
  | Coq_primFloat ->
    (match y with
     | Coq_primInt -> Coq_right
     | Coq_primFloat -> Coq_left)

(** val prim_tag_EqDec : prim_tag coq_EqDec **)

let prim_tag_EqDec =
  prim_tag_eqdec

(** val string_of_prim_int : int -> String.t **)

let string_of_prim_int i =
  string_of_Z (to_Z i)

(** val string_of_float : float -> String.t **)

let string_of_float f =
  match coq_Prim2SF f with
  | S754_zero sign ->
    (match sign with
     | Coq_true ->
       String.String (Coq_x2d, (String.String (Coq_x30, String.EmptyString)))
     | Coq_false -> String.String (Coq_x30, String.EmptyString))
  | S754_infinity sign ->
    (match sign with
     | Coq_true ->
       String.String (Coq_x2d, (String.String (Coq_x49, (String.String
         (Coq_x4e, (String.String (Coq_x46, (String.String (Coq_x49,
         (String.String (Coq_x4e, (String.String (Coq_x49, (String.String
         (Coq_x54, (String.String (Coq_x59,
         String.EmptyString)))))))))))))))))
     | Coq_false ->
       String.String (Coq_x49, (String.String (Coq_x4e, (String.String
         (Coq_x46, (String.String (Coq_x49, (String.String (Coq_x4e,
         (String.String (Coq_x49, (String.String (Coq_x54, (String.String
         (Coq_x59, String.EmptyString))))))))))))))))
  | S754_nan ->
    String.String (Coq_x4e, (String.String (Coq_x41, (String.String (Coq_x4e,
      String.EmptyString)))))
  | S754_finite (sign, p, z) ->
    let abs =
      String.append (String.String (Coq_x30, (String.String (Coq_x78,
        String.EmptyString))))
        (String.append
          (String.of_string (NilZero.string_of_uint (Pos.to_hex_uint p)))
          (String.append (String.String (Coq_x70, String.EmptyString))
            (String.of_string
              (DecimalString.NilZero.string_of_int (BinInt.Z.to_int z)))))
    in
    (match sign with
     | Coq_true ->
       String.append (String.String (Coq_x2d, String.EmptyString)) abs
     | Coq_false -> abs)

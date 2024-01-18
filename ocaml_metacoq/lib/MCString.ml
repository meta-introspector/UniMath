open BinNums
open BinPos
open Byte
open Datatypes
open Decimal
open PeanoNat
open Bytestring

(** val nl : String.t **)

let nl =
  String.String (Coq_x0a, String.EmptyString)

(** val string_of_list_aux :
    ('a1 -> String.t) -> String.t -> 'a1 list -> String.t **)

let rec string_of_list_aux f sep = function
| Coq_nil -> String.EmptyString
| Coq_cons (a, l0) ->
  (match l0 with
   | Coq_nil -> f a
   | Coq_cons (_, _) ->
     String.append (f a) (String.append sep (string_of_list_aux f sep l0)))

(** val string_of_list : ('a1 -> String.t) -> 'a1 list -> String.t **)

let string_of_list f l =
  String.append (String.String (Coq_x5b, String.EmptyString))
    (String.append
      (string_of_list_aux f (String.String (Coq_x2c, String.EmptyString)) l)
      (String.String (Coq_x5d, String.EmptyString)))

(** val print_list : ('a1 -> String.t) -> String.t -> 'a1 list -> String.t **)

let print_list =
  string_of_list_aux

(** val parens : bool -> String.t -> String.t **)

let parens top s =
  match top with
  | Coq_true -> s
  | Coq_false ->
    String.append (String.String (Coq_x28, String.EmptyString))
      (String.append s (String.String (Coq_x29, String.EmptyString)))

(** val string_of_uint : uint -> String.t **)

let rec string_of_uint = function
| Nil -> String.EmptyString
| D0 n0 -> String.String (Coq_x30, (string_of_uint n0))
| D1 n0 -> String.String (Coq_x31, (string_of_uint n0))
| D2 n0 -> String.String (Coq_x32, (string_of_uint n0))
| D3 n0 -> String.String (Coq_x33, (string_of_uint n0))
| D4 n0 -> String.String (Coq_x34, (string_of_uint n0))
| D5 n0 -> String.String (Coq_x35, (string_of_uint n0))
| D6 n0 -> String.String (Coq_x36, (string_of_uint n0))
| D7 n0 -> String.String (Coq_x37, (string_of_uint n0))
| D8 n0 -> String.String (Coq_x38, (string_of_uint n0))
| D9 n0 -> String.String (Coq_x39, (string_of_uint n0))

(** val string_of_nat : nat -> String.t **)

let string_of_nat n =
  string_of_uint (Nat.to_uint n)

(** val string_of_positive : positive -> String.t **)

let string_of_positive p =
  string_of_uint (Pos.to_uint p)

(** val string_of_Z : coq_Z -> String.t **)

let string_of_Z = function
| Z0 -> String.String (Coq_x30, String.EmptyString)
| Zpos p -> string_of_positive p
| Zneg p ->
  String.append (String.String (Coq_x2d, String.EmptyString))
    (string_of_positive p)

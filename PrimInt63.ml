open CarryType
open Datatypes

type int (* AXIOM TO BE REALIZED *)

type pos_neg_int63 =
| Pos of int
| Neg of int

(** val id_int : int -> int **)

let id_int x =
  x

type int_wrapper =
  int
  (* singleton inductive, whose constructor was wrap_int *)

(** val int_wrap : int_wrapper -> int **)

let int_wrap i =
  i

(** val printer : int_wrapper -> pos_neg_int63 **)

let printer x =
  Pos (int_wrap x)

(** val coq_parser : pos_neg_int63 -> int option **)

let coq_parser = function
| Pos p -> Some p
| Neg _ -> None

module Int63NotationsInternalA =
 struct
 end

module Uint63NotationsInternalA =
 struct
 end

(** val coq_lsl : int -> int -> int **)

let coq_lsl =
  failwith "AXIOM TO BE REALIZED"

(** val coq_lsr : int -> int -> int **)

let coq_lsr =
  failwith "AXIOM TO BE REALIZED"

(** val coq_land : int -> int -> int **)

let coq_land =
  failwith "AXIOM TO BE REALIZED"

(** val coq_lor : int -> int -> int **)

let coq_lor =
  failwith "AXIOM TO BE REALIZED"

(** val coq_lxor : int -> int -> int **)

let coq_lxor =
  failwith "AXIOM TO BE REALIZED"

(** val coq_asr : int -> int -> int **)

let coq_asr =
  failwith "AXIOM TO BE REALIZED"

(** val add : int -> int -> int **)

let add =
  failwith "AXIOM TO BE REALIZED"

(** val sub : int -> int -> int **)

let sub =
  failwith "AXIOM TO BE REALIZED"

(** val mul : int -> int -> int **)

let mul =
  failwith "AXIOM TO BE REALIZED"

(** val mulc : int -> int -> (int, int) prod **)

let mulc =
  failwith "AXIOM TO BE REALIZED"

(** val div : int -> int -> int **)

let div =
  failwith "AXIOM TO BE REALIZED"

(** val coq_mod : int -> int -> int **)

let coq_mod =
  failwith "AXIOM TO BE REALIZED"

(** val divs : int -> int -> int **)

let divs =
  failwith "AXIOM TO BE REALIZED"

(** val mods : int -> int -> int **)

let mods =
  failwith "AXIOM TO BE REALIZED"

(** val eqb : int -> int -> bool **)

let eqb =
  failwith "AXIOM TO BE REALIZED"

(** val ltb : int -> int -> bool **)

let ltb =
  failwith "AXIOM TO BE REALIZED"

(** val leb : int -> int -> bool **)

let leb =
  failwith "AXIOM TO BE REALIZED"

(** val ltsb : int -> int -> bool **)

let ltsb =
  failwith "AXIOM TO BE REALIZED"

(** val lesb : int -> int -> bool **)

let lesb =
  failwith "AXIOM TO BE REALIZED"

(** val addc : int -> int -> int carry **)

let addc =
  failwith "AXIOM TO BE REALIZED"

(** val addcarryc : int -> int -> int carry **)

let addcarryc =
  failwith "AXIOM TO BE REALIZED"

(** val subc : int -> int -> int carry **)

let subc =
  failwith "AXIOM TO BE REALIZED"

(** val subcarryc : int -> int -> int carry **)

let subcarryc =
  failwith "AXIOM TO BE REALIZED"

(** val diveucl : int -> int -> (int, int) prod **)

let diveucl =
  failwith "AXIOM TO BE REALIZED"

(** val diveucl_21 : int -> int -> int -> (int, int) prod **)

let diveucl_21 =
  failwith "AXIOM TO BE REALIZED"

(** val addmuldiv : int -> int -> int -> int **)

let addmuldiv =
  failwith "AXIOM TO BE REALIZED"

(** val compare : int -> int -> comparison **)

let compare =
  failwith "AXIOM TO BE REALIZED"

(** val compares : int -> int -> comparison **)

let compares =
  failwith "AXIOM TO BE REALIZED"

(** val head0 : int -> int **)

let head0 =
  failwith "AXIOM TO BE REALIZED"

(** val tail0 : int -> int **)

let tail0 =
  failwith "AXIOM TO BE REALIZED"

module PrimInt63Notations =
 struct
 end

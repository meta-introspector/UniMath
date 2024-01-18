open Ascii
open Byte
open Byte0
open ByteCompare
open ByteCompareSpec
open Classes
open Datatypes
open Nat
open OrdersAlt
open ReflectEq
open Specif
open String

val byte_parse : byte -> byte

val byte_print : byte -> byte

module String :
 sig
  type t =
  | EmptyString
  | String of byte * t

  val t_rect : 'a1 -> (byte -> t -> 'a1 -> 'a1) -> t -> 'a1

  val t_rec : 'a1 -> (byte -> t -> 'a1 -> 'a1) -> t -> 'a1

  val print : t -> byte list

  val parse : byte list -> t

  val append : t -> t -> t

  val to_string : t -> string

  val of_string : string -> t

  val rev : t -> t -> t

  val substring : nat -> nat -> t -> t

  val prefix : t -> t -> bool

  val index : nat -> t -> t -> nat option

  val length : t -> nat

  val contains : nat -> t list -> t -> bool

  val eqb : t -> t -> bool

  val compare : t -> t -> comparison

  val concat : t -> t list -> t
 end

type bs = String.t

module OT_byte :
 sig
  type t = byte

  val compare : t -> t -> byte OrderedType.coq_Compare

  val eq_dec : t -> t -> sumbool
 end

val byte_eqdec : byte coq_EqDec

module StringOT :
 sig
  type t = String.t

  val compare : String.t -> String.t -> comparison

  val reflect_eq_string : t coq_ReflectEq

  val eq_dec : t -> t -> sumbool
 end

module StringOTOrig :
 sig
  type t = String.t

  val eq_dec : String.t -> String.t -> sumbool

  val compare : String.t -> String.t -> String.t OrderedType.coq_Compare
 end

module Tree :
 sig
  type t =
  | Coq_string of String.t
  | Coq_append of t * t

  val t_rect : (String.t -> 'a1) -> (t -> 'a1 -> t -> 'a1 -> 'a1) -> t -> 'a1

  val t_rec : (String.t -> 'a1) -> (t -> 'a1 -> t -> 'a1 -> 'a1) -> t -> 'a1

  val to_rev_list_aux : t -> String.t list -> String.t list

  val to_string_acc : String.t -> String.t list -> String.t

  val to_string : t -> String.t

  val string_of_list_aux : ('a1 -> t) -> t -> 'a1 list -> t

  val string_of_list : ('a1 -> t) -> 'a1 list -> t

  val print_list : ('a1 -> t) -> t -> 'a1 list -> t

  val concat : t -> t list -> t

  val parens : bool -> t -> t
 end

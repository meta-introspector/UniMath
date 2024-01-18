open Ascii
open Bool
open Byte
open Datatypes
open List
open Specif

type string =
| EmptyString
| String of ascii * string

val string_rect : 'a1 -> (ascii -> string -> 'a1 -> 'a1) -> string -> 'a1

val string_rec : 'a1 -> (ascii -> string -> 'a1 -> 'a1) -> string -> 'a1

val string_dec : string -> string -> sumbool

val eqb : string -> string -> bool

val eqb_spec : string -> string -> reflect

val compare : string -> string -> comparison

val ltb : string -> string -> bool

val leb : string -> string -> bool

val append : string -> string -> string

val length : string -> nat

val get : nat -> string -> ascii option

val substring : nat -> nat -> string -> string

val concat : string -> string list -> string

val prefix : string -> string -> bool

val index : nat -> string -> string -> nat option

val findex : nat -> string -> string -> nat

val string_of_list_ascii : ascii list -> string

val list_ascii_of_string : string -> ascii list

val string_of_list_byte : byte list -> string

val list_byte_of_string : string -> byte list

module StringSyntax :
 sig
 end

val coq_HelloWorld : string

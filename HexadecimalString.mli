open Ascii
open Datatypes
open Hexadecimal
open String

val uint_of_char : ascii -> uint option -> uint option

module NilEmpty :
 sig
  val string_of_uint : uint -> string

  val uint_of_string : string -> uint option

  val string_of_int : signed_int -> string

  val int_of_string : string -> signed_int option
 end

module NilZero :
 sig
  val string_of_uint : uint -> string

  val uint_of_string : string -> uint option

  val string_of_int : signed_int -> string

  val int_of_string : string -> signed_int option
 end

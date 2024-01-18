open Bool
open Datatypes
open MCList
open MCReflect
open ReflectEq
open Specif

type __ = Obj.t

val option_get : 'a1 -> 'a1 option -> 'a1

type ('a, 'p) on_some = __

val on_SomeP : 'a1 option -> ('a1, __) sigT

type ('a, 'p) on_some_or_none = __

val option_default : ('a1 -> 'a2) -> 'a1 option -> 'a2 -> 'a2

val map_option_out : 'a1 option list -> 'a1 list option

val nth_map_option_out :
  (nat -> 'a1 -> 'a2 option) -> 'a1 list -> 'a2 list -> nat -> 'a2 -> ('a1,
  __) sigT

val option_map_Some : ('a1 -> 'a2) -> 'a1 option -> 'a2 -> ('a1, __) sigT

val reflect_option_default :
  ('a1 -> bool) -> ('a1 -> 'a2 reflectT) -> 'a1 option -> __ reflectT

val coq_ForOption_sig_pack : 'a1 option -> 'a1 option * __

val coq_ForOption_Signature : 'a1 option -> 'a1 option * __

val foroptb : ('a1 -> bool) -> 'a1 option -> bool

val foroptb2 : ('a1 -> 'a1 -> bool) -> 'a1 option -> 'a1 option -> bool

val option_extends_sig_pack :
  'a1 option -> 'a1 option -> ('a1 option * 'a1 option) * __

val option_extends_Signature :
  'a1 option -> 'a1 option -> ('a1 option * 'a1 option) * __

val option_extendsb : 'a1 coq_ReflectEq -> 'a1 option -> 'a1 option -> bool

val option_extendsT : 'a1 coq_ReflectEq -> 'a1 option -> 'a1 option -> reflect

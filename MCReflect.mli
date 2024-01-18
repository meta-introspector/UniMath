open Bool
open Datatypes

type __ = Obj.t

type 'a reflectT =
| ReflectT of 'a
| ReflectF

val reflectT_rect : ('a1 -> 'a2) -> (__ -> 'a2) -> bool -> 'a1 reflectT -> 'a2

val reflectT_rec : ('a1 -> 'a2) -> (__ -> 'a2) -> bool -> 'a1 reflectT -> 'a2

val reflectT_reflect : bool -> __ reflectT -> reflect

val reflect_reflectT : bool -> reflect -> __ reflectT

val equiv_reflectT : bool -> (__ -> 'a1) -> 'a1 reflectT

val elimT : bool -> 'a1 reflectT -> 'a1

val reflectT_subrelation' :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> 'a2 reflectT) -> 'a1 -> 'a1 -> 'a2

val reflectT_pred : ('a1 -> bool) -> 'a1 -> __ reflectT

val reflectT_pred2 : ('a1 -> 'a2 -> bool) -> 'a1 -> 'a2 -> __ reflectT

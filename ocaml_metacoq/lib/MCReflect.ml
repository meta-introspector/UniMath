open Bool
open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a reflectT =
| ReflectT of 'a
| ReflectF

(** val reflectT_rect :
    ('a1 -> 'a2) -> (__ -> 'a2) -> bool -> 'a1 reflectT -> 'a2 **)

let reflectT_rect f f0 _ = function
| ReflectT a -> f a
| ReflectF -> f0 __

(** val reflectT_rec :
    ('a1 -> 'a2) -> (__ -> 'a2) -> bool -> 'a1 reflectT -> 'a2 **)

let reflectT_rec f f0 _ = function
| ReflectT a -> f a
| ReflectF -> f0 __

(** val reflectT_reflect : bool -> __ reflectT -> reflect **)

let reflectT_reflect _ = function
| ReflectT _ -> Bool.ReflectT
| ReflectF -> Bool.ReflectF

(** val reflect_reflectT : bool -> reflect -> __ reflectT **)

let reflect_reflectT _ = function
| Bool.ReflectT -> ReflectT __
| Bool.ReflectF -> ReflectF

(** val equiv_reflectT : bool -> (__ -> 'a1) -> 'a1 reflectT **)

let equiv_reflectT b x =
  match b with
  | Coq_true -> ReflectT (x __)
  | Coq_false -> ReflectF

(** val elimT : bool -> 'a1 reflectT -> 'a1 **)

let elimT _ = function
| ReflectT t -> t
| ReflectF -> assert false (* absurd case *)

(** val reflectT_subrelation' :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> 'a2 reflectT) -> 'a1 -> 'a1 -> 'a2 **)

let reflectT_subrelation' _ x x0 y =
  let r0 = x x0 y in
  (match r0 with
   | ReflectT r -> r
   | ReflectF -> assert false (* absurd case *))

(** val reflectT_pred : ('a1 -> bool) -> 'a1 -> __ reflectT **)

let reflectT_pred p x =
  equiv_reflectT (p x) (Obj.magic __)

(** val reflectT_pred2 : ('a1 -> 'a2 -> bool) -> 'a1 -> 'a2 -> __ reflectT **)

let reflectT_pred2 p x y =
  equiv_reflectT (p x y) (Obj.magic __)

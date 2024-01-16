open Datatypes

type coq_Empty = |

(** val coq_Empty_rect : coq_Empty -> 'a1 **)

let coq_Empty_rect _ =
  assert false (* absurd case *)

(** val coq_Empty_rec : coq_Empty -> 'a1 **)

let coq_Empty_rec _ =
  assert false (* absurd case *)

(** val coq_Empty_case : coq_Empty -> 'a1 **)

let coq_Empty_case _ =
  assert false (* absurd case *)

(** val unit_rect : 'a1 -> coq_unit -> 'a1 **)

let unit_rect p _ =
  p

type ('a, 'b) prod = 'a * 'b

type ('a, 'b) coq_BiImpl = ('a -> 'b, 'b -> 'a) prod

type 'a coq_Id =
| Coq_id_refl

(** val coq_Id_rect : 'a1 -> 'a2 -> 'a1 -> 'a1 coq_Id -> 'a2 **)

let coq_Id_rect _ f _ _ =
  f

(** val coq_Id_rec : 'a1 -> 'a2 -> 'a1 -> 'a1 coq_Id -> 'a2 **)

let coq_Id_rec _ f _ _ =
  f

module Id_Notations =
 struct
 end

(** val id_sym : 'a1 -> 'a1 -> 'a1 coq_Id -> 'a1 coq_Id **)

let id_sym _ _ _ =
  Coq_id_refl

(** val id_trans :
    'a1 -> 'a1 -> 'a1 -> 'a1 coq_Id -> 'a1 coq_Id -> 'a1 coq_Id **)

let id_trans _ _ _ _ _ =
  Coq_id_refl

(** val transport : 'a1 -> 'a2 -> 'a1 -> 'a1 coq_Id -> 'a2 **)

let transport _ px _ _ =
  px

(** val coq_Id_rew : 'a1 -> 'a2 -> 'a1 -> 'a1 coq_Id -> 'a2 **)

let coq_Id_rew =
  transport

(** val coq_Id_case : 'a1 -> 'a1 -> 'a1 coq_Id -> 'a2 -> 'a2 **)

let coq_Id_case x y e px =
  transport x px y (id_sym y x e)

(** val coq_Id_rew_r : 'a1 -> 'a1 -> 'a2 -> 'a1 coq_Id -> 'a2 **)

let coq_Id_rew_r x y px e =
  transport y px x (id_sym x y e)

(** val coq_Id_rect_r : 'a1 -> 'a2 -> 'a1 -> 'a1 coq_Id -> 'a2 **)

let coq_Id_rect_r _ p _ _ =
  p

(** val id_inspect : 'a1 -> 'a1 * 'a1 coq_Id **)

let id_inspect x =
  x,Coq_id_refl

type 'a coq_HProp = 'a -> 'a -> 'a coq_Id

(** val is_hprop : 'a1 coq_HProp -> 'a1 -> 'a1 -> 'a1 coq_Id **)

let is_hprop hProp =
  hProp

type 'a coq_HSet = 'a -> 'a -> 'a coq_Id coq_HProp

(** val is_hset : 'a1 coq_HSet -> 'a1 -> 'a1 -> 'a1 coq_Id coq_HProp **)

let is_hset hSet =
  hSet

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

(** val sum_rect : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3 **)

let sum_rect f f0 = function
| Coq_inl a -> f a
| Coq_inr b -> f0 b

(** val sum_rec : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3 **)

let sum_rec f f0 = function
| Coq_inl a -> f a
| Coq_inr b -> f0 b

type ('a, 'b) coq_Sect = 'a -> 'a coq_Id

(** val ap : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 coq_Id -> 'a2 coq_Id **)

let ap _ _ _ _ =
  Coq_id_refl

type ('a, 'b) coq_IsEquiv = { equiv_inv : ('b -> 'a);
                              eisretr : ('b, 'a) coq_Sect;
                              eissect : ('a, 'b) coq_Sect;
                              eisadj : ('a -> 'b coq_Id coq_Id) }

(** val equiv_inv : ('a1 -> 'a2) -> ('a1, 'a2) coq_IsEquiv -> 'a2 -> 'a1 **)

let equiv_inv _ isEquiv =
  isEquiv.equiv_inv

(** val eisretr :
    ('a1 -> 'a2) -> ('a1, 'a2) coq_IsEquiv -> ('a2, 'a1) coq_Sect **)

let eisretr _ isEquiv =
  isEquiv.eisretr

(** val eissect :
    ('a1 -> 'a2) -> ('a1, 'a2) coq_IsEquiv -> ('a1, 'a2) coq_Sect **)

let eissect _ isEquiv =
  isEquiv.eissect

(** val eisadj :
    ('a1 -> 'a2) -> ('a1, 'a2) coq_IsEquiv -> 'a1 -> 'a2 coq_Id coq_Id **)

let eisadj _ isEquiv =
  isEquiv.eisadj

type ('a, 'b) coq_Equiv = { equiv_fun : ('a -> 'b);
                            equiv_isequiv : ('a, 'b) coq_IsEquiv }

(** val equiv_fun : ('a1, 'a2) coq_Equiv -> 'a1 -> 'a2 **)

let equiv_fun e =
  e.equiv_fun

(** val equiv_isequiv : ('a1, 'a2) coq_Equiv -> ('a1, 'a2) coq_IsEquiv **)

let equiv_isequiv e =
  e.equiv_isequiv

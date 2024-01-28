open Datatypes

type coq_Empty = |

val coq_Empty_rect : coq_Empty -> 'a1

val coq_Empty_rec : coq_Empty -> 'a1

val coq_Empty_case : coq_Empty -> 'a1

val unit_rect : 'a1 -> coq_unit -> 'a1

type ('a, 'b) prod = 'a * 'b

type ('a, 'b) coq_BiImpl = ('a -> 'b, 'b -> 'a) prod

type 'a coq_Id =
| Coq_id_refl

val coq_Id_rect : 'a1 -> 'a2 -> 'a1 -> 'a1 coq_Id -> 'a2

val coq_Id_rec : 'a1 -> 'a2 -> 'a1 -> 'a1 coq_Id -> 'a2

module Id_Notations :
 sig
 end

val id_sym : 'a1 -> 'a1 -> 'a1 coq_Id -> 'a1 coq_Id

val id_trans : 'a1 -> 'a1 -> 'a1 -> 'a1 coq_Id -> 'a1 coq_Id -> 'a1 coq_Id

val transport : 'a1 -> 'a2 -> 'a1 -> 'a1 coq_Id -> 'a2

val coq_Id_rew : 'a1 -> 'a2 -> 'a1 -> 'a1 coq_Id -> 'a2

val coq_Id_case : 'a1 -> 'a1 -> 'a1 coq_Id -> 'a2 -> 'a2

val coq_Id_rew_r : 'a1 -> 'a1 -> 'a2 -> 'a1 coq_Id -> 'a2

val coq_Id_rect_r : 'a1 -> 'a2 -> 'a1 -> 'a1 coq_Id -> 'a2

val id_inspect : 'a1 -> 'a1 * 'a1 coq_Id

type 'a coq_HProp = 'a -> 'a -> 'a coq_Id

val is_hprop : 'a1 coq_HProp -> 'a1 -> 'a1 -> 'a1 coq_Id

type 'a coq_HSet = 'a -> 'a -> 'a coq_Id coq_HProp

val is_hset : 'a1 coq_HSet -> 'a1 -> 'a1 -> 'a1 coq_Id coq_HProp

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

val sum_rect : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3

val sum_rec : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) sum -> 'a3

type ('a, 'b) coq_Sect = 'a -> 'a coq_Id

val ap : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 coq_Id -> 'a2 coq_Id

type ('a, 'b) coq_IsEquiv = { equiv_inv : ('b -> 'a);
                              eisretr : ('b, 'a) coq_Sect;
                              eissect : ('a, 'b) coq_Sect;
                              eisadj : ('a -> 'b coq_Id coq_Id) }

val equiv_inv : ('a1 -> 'a2) -> ('a1, 'a2) coq_IsEquiv -> 'a2 -> 'a1

val eisretr : ('a1 -> 'a2) -> ('a1, 'a2) coq_IsEquiv -> ('a2, 'a1) coq_Sect

val eissect : ('a1 -> 'a2) -> ('a1, 'a2) coq_IsEquiv -> ('a1, 'a2) coq_Sect

val eisadj :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_IsEquiv -> 'a1 -> 'a2 coq_Id coq_Id

type ('a, 'b) coq_Equiv = { equiv_fun : ('a -> 'b);
                            equiv_isequiv : ('a, 'b) coq_IsEquiv }

val equiv_fun : ('a1, 'a2) coq_Equiv -> 'a1 -> 'a2

val equiv_isequiv : ('a1, 'a2) coq_Equiv -> ('a1, 'a2) coq_IsEquiv

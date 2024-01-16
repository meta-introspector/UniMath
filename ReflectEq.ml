open Bool
open Classes
open Datatypes
open PeanoNat
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val reflectProp_sig_pack : bool -> bool * __ **)

let reflectProp_sig_pack x =
  x,__

(** val reflectProp_Signature : bool -> bool * __ **)

let reflectProp_Signature x =
  x,__

(** val reflectProp_reflect : bool -> reflect **)

let reflectProp_reflect = function
| Coq_true -> ReflectT
| Coq_false -> ReflectF

type 'a coq_ReflectEq =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_ReflectEq *)

(** val eqb : 'a1 coq_ReflectEq -> 'a1 -> 'a1 -> bool **)

let eqb reflectEq =
  reflectEq

(** val eqb_specT : 'a1 coq_ReflectEq -> 'a1 -> 'a1 -> reflect **)

let eqb_specT hR x y =
  reflectProp_reflect (eqb hR x y)

(** val coq_ReflectEq_EqDec : 'a1 coq_ReflectEq -> 'a1 coq_EqDec **)

let coq_ReflectEq_EqDec r x y =
  let filtered_var = eqb r x y in
  (match filtered_var with
   | Coq_true -> Coq_left
   | Coq_false -> Coq_right)

(** val eq_dec_to_bool : 'a1 coq_EqDec -> 'a1 -> 'a1 -> bool **)

let eq_dec_to_bool h x y =
  match eq_dec h x y with
  | Coq_left -> Coq_true
  | Coq_right -> Coq_false

(** val coq_EqDec_ReflectEq : 'a1 coq_EqDec -> 'a1 coq_ReflectEq **)

let coq_EqDec_ReflectEq =
  eq_dec_to_bool

(** val eq_option :
    ('a1 -> 'a1 -> bool) -> 'a1 option -> 'a1 option -> bool **)

let eq_option eqA u v =
  match u with
  | Some u0 -> (match v with
                | Some v0 -> eqA u0 v0
                | None -> Coq_false)
  | None -> (match v with
             | Some _ -> Coq_false
             | None -> Coq_true)

(** val reflect_option : 'a1 coq_ReflectEq -> 'a1 option coq_ReflectEq **)

let reflect_option hA =
  eq_option (eqb hA)

(** val eqb_list : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec eqb_list eqA l l' =
  match l with
  | Coq_nil ->
    (match l' with
     | Coq_nil -> Coq_true
     | Coq_cons (_, _) -> Coq_false)
  | Coq_cons (a, l0) ->
    (match l' with
     | Coq_nil -> Coq_false
     | Coq_cons (a', l'0) ->
       (match eqA a a' with
        | Coq_true -> eqb_list eqA l0 l'0
        | Coq_false -> Coq_false))

(** val reflect_list : 'a1 coq_ReflectEq -> 'a1 list coq_ReflectEq **)

let reflect_list rA =
  eqb_list (eqb rA)

(** val reflect_nat : nat coq_ReflectEq **)

let reflect_nat =
  Nat.eqb

(** val eq_bool : bool -> bool -> bool **)

let eq_bool b1 b2 =
  match b1 with
  | Coq_true -> b2
  | Coq_false -> negb b2

(** val reflect_bool : bool coq_ReflectEq **)

let reflect_bool =
  eq_bool

(** val eq_sig_true :
    ('a1 -> bool) -> 'a1 coq_ReflectEq -> 'a1 -> 'a1 -> bool **)

let eq_sig_true _ =
  eqb

(** val reflect_sig_true :
    ('a1 -> bool) -> 'a1 coq_ReflectEq -> 'a1 coq_ReflectEq **)

let reflect_sig_true =
  eq_sig_true

(** val eq_prod :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1, 'a2) prod -> ('a1,
    'a2) prod -> bool **)

let eq_prod eqA eqB x y =
  let Coq_pair (a1, b1) = x in
  let Coq_pair (a2, b2) = y in
  (match eqA a1 a2 with
   | Coq_true -> eqB b1 b2
   | Coq_false -> Coq_false)

(** val reflect_prod :
    'a1 coq_ReflectEq -> 'a2 coq_ReflectEq -> ('a1, 'a2) prod coq_ReflectEq **)

let reflect_prod x x0 =
  eq_prod (eqb x) (eqb x0)

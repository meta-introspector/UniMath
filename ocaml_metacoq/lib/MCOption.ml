open Bool
open Datatypes
open MCList
open MCReflect
open ReflectEq
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val option_get : 'a1 -> 'a1 option -> 'a1 **)

let option_get default = function
| Some x0 -> x0
| None -> default

type ('a, 'p) on_some = __

(** val on_SomeP : 'a1 option -> ('a1, __) sigT **)

let on_SomeP = function
| Some a -> Coq_existT (a, __)
| None -> assert false (* absurd case *)

type ('a, 'p) on_some_or_none = __

(** val option_default : ('a1 -> 'a2) -> 'a1 option -> 'a2 -> 'a2 **)

let option_default f o b =
  match o with
  | Some x -> f x
  | None -> b

(** val map_option_out : 'a1 option list -> 'a1 list option **)

let rec map_option_out = function
| Coq_nil -> Some Coq_nil
| Coq_cons (hd, tl) ->
  (match hd with
   | Some hd0 ->
     (match map_option_out tl with
      | Some tl0 -> Some (Coq_cons (hd0, tl0))
      | None -> None)
   | None -> None)

(** val nth_map_option_out :
    (nat -> 'a1 -> 'a2 option) -> 'a1 list -> 'a2 list -> nat -> 'a2 -> ('a1,
    __) sigT **)

let nth_map_option_out f l l' i _ =
  let rec f0 l0 _ i0 n =
    match l0 with
    | Coq_nil -> (fun _ _ -> assert false (* absurd case *))
    | Coq_cons (y, l1) ->
      let o = f n y in
      (match o with
       | Some _ ->
         let o0 = map_option_out (mapi_rec f l1 (S n)) in
         (fun _ ->
         match o0 with
         | Some l2 ->
           (match i0 with
            | O -> (fun _ -> Coq_existT (y, __))
            | S n0 -> f0 l1 l2 n0 (S n) __)
         | None -> (fun _ -> assert false (* absurd case *)))
       | None -> (fun _ _ -> assert false (* absurd case *)))
  in f0 l l' i O __ __

(** val option_map_Some :
    ('a1 -> 'a2) -> 'a1 option -> 'a2 -> ('a1, __) sigT **)

let option_map_Some _ o _ =
  match o with
  | Some a -> Coq_existT (a, __)
  | None -> assert false (* absurd case *)

(** val reflect_option_default :
    ('a1 -> bool) -> ('a1 -> 'a2 reflectT) -> 'a1 option -> __ reflectT **)

let reflect_option_default _ hp = function
| Some a -> Obj.magic hp a
| None -> ReflectT (Obj.magic Coq_tt)

(** val coq_ForOption_sig_pack : 'a1 option -> 'a1 option * __ **)

let coq_ForOption_sig_pack x =
  x,__

(** val coq_ForOption_Signature : 'a1 option -> 'a1 option * __ **)

let coq_ForOption_Signature x =
  x,__

(** val foroptb : ('a1 -> bool) -> 'a1 option -> bool **)

let foroptb p o =
  option_get Coq_true (option_map p o)

(** val foroptb2 :
    ('a1 -> 'a1 -> bool) -> 'a1 option -> 'a1 option -> bool **)

let foroptb2 p o o' =
  match o with
  | Some v -> (match o' with
               | Some v' -> p v v'
               | None -> Coq_false)
  | None -> (match o' with
             | Some _ -> Coq_false
             | None -> Coq_true)

(** val option_extends_sig_pack :
    'a1 option -> 'a1 option -> ('a1 option * 'a1 option) * __ **)

let option_extends_sig_pack x x0 =
  (x,x0),__

(** val option_extends_Signature :
    'a1 option -> 'a1 option -> ('a1 option * 'a1 option) * __ **)

let option_extends_Signature x x0 =
  (x,x0),__

(** val option_extendsb :
    'a1 coq_ReflectEq -> 'a1 option -> 'a1 option -> bool **)

let option_extendsb aeq x y =
  match x with
  | Some t1 -> (match y with
                | Some t2 -> eqb aeq t1 t2
                | None -> Coq_false)
  | None -> Coq_true

(** val option_extendsT :
    'a1 coq_ReflectEq -> 'a1 option -> 'a1 option -> reflect **)

let option_extendsT aeq x y =
  match x with
  | Some a ->
    (match y with
     | Some a0 ->
       let _evar_0_ = fun _ -> Bool.ReflectT in
       let _evar_0_0 = fun _ -> Bool.ReflectF in
       (match eqb aeq a a0 with
        | Coq_true -> _evar_0_ __
        | Coq_false -> _evar_0_0 __)
     | None -> Bool.ReflectF)
  | None -> Bool.ReflectT

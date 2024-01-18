open All_Forall
open Datatypes
open PeanoNat
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'm coq_Monad = { ret : (__ -> __ -> 'm);
                      bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val ret : 'a1 coq_Monad -> 'a2 -> 'a1 **)

let ret monad x =
  Obj.magic monad.ret __ x

(** val bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let bind monad x x0 =
  Obj.magic monad.bind __ __ x x0

type ('e, 'm) coq_MonadExc = { raise : (__ -> 'e -> 'm);
                               catch : (__ -> 'm -> ('e -> 'm) -> 'm) }

(** val raise : ('a1, 'a2) coq_MonadExc -> 'a1 -> 'a2 **)

let raise monadExc x =
  monadExc.raise __ x

(** val catch : ('a1, 'a2) coq_MonadExc -> 'a2 -> ('a1 -> 'a2) -> 'a2 **)

let catch monadExc x x0 =
  monadExc.catch __ x x0

module MCMonadNotation =
 struct
 end

(** val option_monad : __ option coq_Monad **)

let option_monad =
  { ret = (fun _ a -> Some a); bind = (fun _ _ m f ->
    match m with
    | Some a -> f a
    | None -> None) }

(** val id_monad : __ coq_Monad **)

let id_monad =
  { ret = (fun _ a -> a); bind = (fun _ _ m f -> f m) }

(** val option_monad_exc : (coq_unit, __ option) coq_MonadExc **)

let option_monad_exc =
  { raise = (fun _ _ -> None); catch = (fun _ m f ->
    match m with
    | Some a -> Some a
    | None -> f Coq_tt) }

(** val mapopt : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option **)

let rec mapopt f = function
| Coq_nil -> ret (Obj.magic option_monad) Coq_nil
| Coq_cons (x, xs) ->
  bind (Obj.magic option_monad) (Obj.magic f x) (fun x' ->
    bind (Obj.magic option_monad) (mapopt f xs) (fun xs' ->
      ret (Obj.magic option_monad) (Coq_cons (x', xs'))))

(** val monad_map : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1 **)

let rec monad_map m f = function
| Coq_nil -> ret m Coq_nil
| Coq_cons (x, l0) ->
  bind m (f x) (fun x' ->
    bind m (monad_map m f l0) (fun l' -> ret m (Coq_cons (x', l'))))

(** val monad_option_map :
    'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 option -> 'a1 **)

let monad_option_map m f = function
| Some x -> bind m (f x) (fun x' -> ret m (Some x'))
| None -> ret m None

(** val monad_fold_left :
    'a1 coq_Monad -> ('a2 -> 'a3 -> 'a1) -> 'a3 list -> 'a2 -> 'a1 **)

let rec monad_fold_left m g l x =
  match l with
  | Coq_nil -> ret m x
  | Coq_cons (y, l0) -> bind m (g x y) (fun x' -> monad_fold_left m g l0 x')

(** val monad_fold_right :
    'a1 coq_Monad -> ('a2 -> 'a3 -> 'a1) -> 'a3 list -> 'a2 -> 'a1 **)

let rec monad_fold_right m g l x =
  match l with
  | Coq_nil -> ret m x
  | Coq_cons (y, l0) -> bind m (monad_fold_right m g l0 x) (fun l' -> g l' y)

(** val monad_map_i_aux :
    'a1 coq_Monad -> (nat -> 'a2 -> 'a1) -> nat -> 'a2 list -> 'a1 **)

let rec monad_map_i_aux m h n0 = function
| Coq_nil -> ret m Coq_nil
| Coq_cons (x, l0) ->
  bind m (h n0 x) (fun x' ->
    bind m (monad_map_i_aux m h (S n0) l0) (fun l' ->
      ret m (Coq_cons (x', l'))))

(** val monad_map_i :
    'a1 coq_Monad -> (nat -> 'a2 -> 'a1) -> 'a2 list -> 'a1 **)

let monad_map_i m h =
  monad_map_i_aux m h O

(** val monad_map2 :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> ('a3 -> 'a4 -> 'a1) -> 'a2 ->
    'a3 list -> 'a4 list -> 'a1 **)

let rec monad_map2 m mE f e l l' =
  match l with
  | Coq_nil ->
    (match l' with
     | Coq_nil -> ret m Coq_nil
     | Coq_cons (_, _) -> raise mE e)
  | Coq_cons (x, l0) ->
    (match l' with
     | Coq_nil -> raise mE e
     | Coq_cons (y, l'0) ->
       bind m (f x y) (fun x' ->
         bind m (monad_map2 m mE f e l0 l'0) (fun xs' ->
           ret m (Coq_cons (x', xs')))))

(** val monad_iter : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1 **)

let monad_iter m f l =
  monad_fold_left m (fun _ -> f) l Coq_tt

(** val monad_All : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1 **)

let rec monad_All m f = function
| Coq_nil -> ret m All_nil
| Coq_cons (a, l0) ->
  bind m (f a) (fun x ->
    bind m (monad_All m f l0) (fun y -> ret m (All_cons (a, l0, x, y))))

(** val monad_All2 :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> 'a2 -> ('a3 -> 'a4 -> 'a1) ->
    'a3 list -> 'a4 list -> 'a1 **)

let rec monad_All2 m m' wrong_sizes f l1 l2 =
  match l1 with
  | Coq_nil ->
    (match l2 with
     | Coq_nil -> ret m All2_nil
     | Coq_cons (_, _) -> raise m' wrong_sizes)
  | Coq_cons (a, l3) ->
    (match l2 with
     | Coq_nil -> raise m' wrong_sizes
     | Coq_cons (b, l4) ->
       bind m (f a b) (fun x ->
         bind m (monad_All2 m m' wrong_sizes f l3 l4) (fun y ->
           ret m (All2_cons (a, b, l3, l4, x, y)))))

(** val monad_prod : 'a1 coq_Monad -> 'a1 -> 'a1 -> 'a1 **)

let monad_prod m x y =
  bind m x (fun x0 -> bind m y (fun y0 -> ret m (Coq_pair (x0, y0))))

(** val check_dec :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> 'a2 -> sumbool -> 'a1 **)

let check_dec m m' e = function
| Coq_left -> ret m __
| Coq_right -> raise m' e

(** val check_eq_true :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> bool -> 'a2 -> 'a1 **)

let check_eq_true m m' b e =
  match b with
  | Coq_true -> ret m __
  | Coq_false -> raise m' e

(** val check_eq_nat :
    'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> nat -> nat -> 'a2 -> 'a1 **)

let check_eq_nat m m' n m0 e =
  match Nat.eq_dec n m0 with
  | Coq_left -> ret m __
  | Coq_right -> raise m' e

(** val monad_Alli :
    'a1 coq_Monad -> (nat -> 'a2 -> 'a1) -> 'a2 list -> nat -> 'a1 **)

let rec monad_Alli m f l n =
  match l with
  | Coq_nil -> ret m __
  | Coq_cons (a, l0) ->
    bind m (f n a) (fun _ ->
      bind m (monad_Alli m f l0 (S n)) (fun _ -> ret m __))

(** val monad_Alli_All :
    'a1 coq_Monad -> (nat -> 'a2 -> __ -> 'a1) -> 'a2 list -> nat -> 'a1 **)

let rec monad_Alli_All m f l n =
  match l with
  | Coq_nil -> ret m __
  | Coq_cons (a, l0) ->
    bind m (f n a __) (fun _ ->
      bind m (monad_Alli_All m f l0 (S n)) (fun _ -> ret m __))

(** val monad_Alli_nth_gen :
    'a1 coq_Monad -> 'a2 list -> nat -> (nat -> 'a2 -> __ -> 'a1) -> 'a1 **)

let rec monad_Alli_nth_gen m l k f =
  match l with
  | Coq_nil -> ret m __
  | Coq_cons (a, l0) ->
    bind m (f O a __) (fun _ ->
      bind m
        (monad_Alli_nth_gen m l0 (S k) (fun n x _ ->
          bind m (f (S n) x __) (fun _ -> ret m __))) (fun _ -> ret m __))

(** val monad_Alli_nth :
    'a1 coq_Monad -> 'a2 list -> (nat -> 'a2 -> __ -> 'a1) -> 'a1 **)

let monad_Alli_nth m l f =
  monad_Alli_nth_gen m l O f

(** val monad_All_All :
    'a1 coq_Monad -> ('a2 -> __ -> 'a1) -> 'a2 list -> 'a1 **)

let rec monad_All_All m f = function
| Coq_nil -> ret m __
| Coq_cons (a, l0) ->
  bind m (f a __) (fun _ -> bind m (monad_All_All m f l0) (fun _ -> ret m __))

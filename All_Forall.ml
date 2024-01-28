open Bool
open CRelationClasses
open Classes
open Compare_dec
open Datatypes
open EqdepFacts
open List
open MCList
open MCOption
open MCReflect
open MCRelations
open Nat
open Signature
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_Forall_sig_pack : 'a1 list -> 'a1 list * __ **)

let coq_Forall_sig_pack x =
  x,__

(** val coq_Forall_Signature : 'a1 list -> 'a1 list * __ **)

let coq_Forall_Signature x =
  x,__

(** val coq_Forall2_sig_pack :
    'a1 list -> 'a2 list -> ('a1 list * 'a2 list) * __ **)

let coq_Forall2_sig_pack x x0 =
  (x,x0),__

(** val coq_Forall2_Signature :
    'a1 list -> 'a2 list -> ('a1 list * 'a2 list) * __ **)

let coq_Forall2_Signature x x0 =
  (x,x0),__

type ('a, 'p) coq_All =
| All_nil
| All_cons of 'a * 'a list * 'p * ('a, 'p) coq_All

(** val coq_All_rect :
    'a3 -> ('a1 -> 'a1 list -> 'a2 -> ('a1, 'a2) coq_All -> 'a3 -> 'a3) ->
    'a1 list -> ('a1, 'a2) coq_All -> 'a3 **)

let rec coq_All_rect f f0 _ = function
| All_nil -> f
| All_cons (x, l, y, a0) -> f0 x l y a0 (coq_All_rect f f0 l a0)

(** val coq_All_rec :
    'a3 -> ('a1 -> 'a1 list -> 'a2 -> ('a1, 'a2) coq_All -> 'a3 -> 'a3) ->
    'a1 list -> ('a1, 'a2) coq_All -> 'a3 **)

let rec coq_All_rec f f0 _ = function
| All_nil -> f
| All_cons (x, l, y, a0) -> f0 x l y a0 (coq_All_rec f f0 l a0)

type ('a, 'p) coq_All_sig = ('a, 'p) coq_All

(** val coq_All_sig_pack :
    'a1 list -> ('a1, 'a2) coq_All -> 'a1 list * ('a1, 'a2) coq_All **)

let coq_All_sig_pack x all_var =
  x,all_var

(** val coq_All_Signature :
    'a1 list -> (('a1, 'a2) coq_All, 'a1 list, ('a1, 'a2) coq_All_sig)
    coq_Signature **)

let coq_All_Signature x all_var =
  x,all_var

(** val coq_NoConfusionPackage_All :
    ('a1 list * ('a1, 'a2) coq_All) coq_NoConfusionPackage **)

let coq_NoConfusionPackage_All =
  Build_NoConfusionPackage

type ('a, 'p) coq_Alli =
| Alli_nil
| Alli_cons of 'a * 'a list * 'p * ('a, 'p) coq_Alli

(** val coq_Alli_rect :
    (nat -> 'a3) -> (nat -> 'a1 -> 'a1 list -> 'a2 -> ('a1, 'a2) coq_Alli ->
    'a3 -> 'a3) -> nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> 'a3 **)

let rec coq_Alli_rect f f0 n _ = function
| Alli_nil -> f n
| Alli_cons (hd, tl, y, a0) ->
  f0 n hd tl y a0 (coq_Alli_rect f f0 (S n) tl a0)

(** val coq_Alli_rec :
    (nat -> 'a3) -> (nat -> 'a1 -> 'a1 list -> 'a2 -> ('a1, 'a2) coq_Alli ->
    'a3 -> 'a3) -> nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> 'a3 **)

let rec coq_Alli_rec f f0 n _ = function
| Alli_nil -> f n
| Alli_cons (hd, tl, y, a0) -> f0 n hd tl y a0 (coq_Alli_rec f f0 (S n) tl a0)

type ('a, 'p) coq_Alli_sig = ('a, 'p) coq_Alli

(** val coq_Alli_sig_pack :
    nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> (nat * 'a1 list) * ('a1, 'a2)
    coq_Alli **)

let coq_Alli_sig_pack n x alli_var =
  (n,x),alli_var

(** val coq_Alli_Signature :
    nat -> 'a1 list -> (('a1, 'a2) coq_Alli, nat * 'a1 list, ('a1, 'a2)
    coq_Alli_sig) coq_Signature **)

let coq_Alli_Signature n x alli_var =
  (n,x),alli_var

(** val coq_NoConfusionHomPackage_Alli :
    nat -> 'a1 list -> ('a1, 'a2) coq_Alli coq_NoConfusionPackage **)

let coq_NoConfusionHomPackage_Alli _ _ =
  Build_NoConfusionPackage

type ('a, 'b, 'r) coq_All2 =
| All2_nil
| All2_cons of 'a * 'b * 'a list * 'b list * 'r * ('a, 'b, 'r) coq_All2

(** val coq_All2_rect :
    'a4 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
    coq_All2 -> 'a4 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
    coq_All2 -> 'a4 **)

let rec coq_All2_rect f f0 _ _ = function
| All2_nil -> f
| All2_cons (x, y, l, l', y0, a0) ->
  f0 x y l l' y0 a0 (coq_All2_rect f f0 l l' a0)

(** val coq_All2_rec :
    'a4 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
    coq_All2 -> 'a4 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
    coq_All2 -> 'a4 **)

let rec coq_All2_rec f f0 _ _ = function
| All2_nil -> f
| All2_cons (x, y, l, l', y0, a0) ->
  f0 x y l l' y0 a0 (coq_All2_rec f f0 l l' a0)

type ('a, 'b, 'r) coq_All2_sig = ('a, 'b, 'r) coq_All2

(** val coq_All2_sig_pack :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 list * 'a2
    list) * ('a1, 'a2, 'a3) coq_All2 **)

let coq_All2_sig_pack x x0 all2_var =
  (x,x0),all2_var

(** val coq_All2_Signature :
    'a1 list -> 'a2 list -> (('a1, 'a2, 'a3) coq_All2, 'a1 list * 'a2 list,
    ('a1, 'a2, 'a3) coq_All2_sig) coq_Signature **)

let coq_All2_Signature x x0 all2_var =
  (x,x0),all2_var

(** val coq_NoConfusionHomPackage_All2 :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 coq_NoConfusionPackage **)

let coq_NoConfusionHomPackage_All2 _ _ =
  Build_NoConfusionPackage

type ('a, 'b, 'r, 'x) coq_All2_dep =
| All2_dep_nil
| All2_dep_cons of 'a * 'b * 'a list * 'b list * 'r * ('a, 'b, 'r) coq_All2
   * 'x * ('a, 'b, 'r, 'x) coq_All2_dep

(** val coq_All2_dep_rect :
    'a5 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
    coq_All2 -> 'a4 -> ('a1, 'a2, 'a3, 'a4) coq_All2_dep -> 'a5 -> 'a5) ->
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3, 'a4)
    coq_All2_dep -> 'a5 **)

let rec coq_All2_dep_rect f f0 _ _ _ = function
| All2_dep_nil -> f
| All2_dep_cons (x, y, l, l', r, rs, y0, a) ->
  f0 x y l l' r rs y0 a (coq_All2_dep_rect f f0 l l' rs a)

(** val coq_All2_dep_rec :
    'a5 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
    coq_All2 -> 'a4 -> ('a1, 'a2, 'a3, 'a4) coq_All2_dep -> 'a5 -> 'a5) ->
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3, 'a4)
    coq_All2_dep -> 'a5 **)

let rec coq_All2_dep_rec f f0 _ _ _ = function
| All2_dep_nil -> f
| All2_dep_cons (x, y, l, l', r, rs, y0, a) ->
  f0 x y l l' r rs y0 a (coq_All2_dep_rec f f0 l l' rs a)

type ('a, 'b, 'r, 'x) coq_All2_dep_sig = ('a, 'b, 'r, 'x) coq_All2_dep

(** val coq_All2_dep_sig_pack :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3, 'a4)
    coq_All2_dep -> ('a1 list * ('a2 list * ('a1, 'a2, 'a3)
    coq_All2)) * ('a1, 'a2, 'a3, 'a4) coq_All2_dep **)

let coq_All2_dep_sig_pack xs ys x all2_dep_var =
  (xs,(ys,x)),all2_dep_var

(** val coq_All2_dep_Signature :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> (('a1, 'a2, 'a3, 'a4)
    coq_All2_dep, 'a1 list * ('a2 list * ('a1, 'a2, 'a3) coq_All2), ('a1,
    'a2, 'a3, 'a4) coq_All2_dep_sig) coq_Signature **)

let coq_All2_dep_Signature xs ys x all2_dep_var =
  (xs,(ys,x)),all2_dep_var

(** val coq_NoConfusionHomPackage_All2_dep :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3, 'a4)
    coq_All2_dep coq_NoConfusionPackage **)

let coq_NoConfusionHomPackage_All2_dep _ _ _ =
  Build_NoConfusionPackage

(** val coq_Forall2_dep_sig_pack :
    'a1 list -> 'a2 list -> ('a1 list * ('a2 list * __)) * __ **)

let coq_Forall2_dep_sig_pack xs ys =
  (xs,(ys,__)),__

(** val coq_Forall2_dep_Signature :
    'a1 list -> 'a2 list -> ('a1 list * ('a2 list * __)) * __ **)

let coq_Forall2_dep_Signature xs ys =
  (xs,(ys,__)),__

type ('a, 'b, 'r) coq_All2i =
| All2i_nil
| All2i_cons of 'a * 'b * 'a list * 'b list * 'r * ('a, 'b, 'r) coq_All2i

(** val coq_All2i_rect :
    (nat -> 'a4) -> (nat -> 'a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 ->
    ('a1, 'a2, 'a3) coq_All2i -> 'a4 -> 'a4) -> nat -> 'a1 list -> 'a2 list
    -> ('a1, 'a2, 'a3) coq_All2i -> 'a4 **)

let rec coq_All2i_rect f f0 n _ _ = function
| All2i_nil -> f n
| All2i_cons (x, y, l, r, y0, a0) ->
  f0 n x y l r y0 a0 (coq_All2i_rect f f0 (S n) l r a0)

(** val coq_All2i_rec :
    (nat -> 'a4) -> (nat -> 'a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 ->
    ('a1, 'a2, 'a3) coq_All2i -> 'a4 -> 'a4) -> nat -> 'a1 list -> 'a2 list
    -> ('a1, 'a2, 'a3) coq_All2i -> 'a4 **)

let rec coq_All2i_rec f f0 n _ _ = function
| All2i_nil -> f n
| All2i_cons (x, y, l, r, y0, a0) ->
  f0 n x y l r y0 a0 (coq_All2i_rec f f0 (S n) l r a0)

type ('a, 'b, 'r) coq_All2i_sig = ('a, 'b, 'r) coq_All2i

(** val coq_All2i_sig_pack :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> (nat * ('a1
    list * 'a2 list)) * ('a1, 'a2, 'a3) coq_All2i **)

let coq_All2i_sig_pack n x x0 all2i_var =
  (n,(x,x0)),all2i_var

(** val coq_All2i_Signature :
    nat -> 'a1 list -> 'a2 list -> (('a1, 'a2, 'a3) coq_All2i, nat * ('a1
    list * 'a2 list), ('a1, 'a2, 'a3) coq_All2i_sig) coq_Signature **)

let coq_All2i_Signature n x x0 all2i_var =
  (n,(x,x0)),all2i_var

(** val coq_NoConfusionHomPackage_All2i :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i
    coq_NoConfusionPackage **)

let coq_NoConfusionHomPackage_All2i _ _ _ =
  Build_NoConfusionPackage

type ('a, 'b, 'c, 'r) coq_All3 =
| All3_nil
| All3_cons of 'a * 'b * 'c * 'a list * 'b list * 'c list * 'r
   * ('a, 'b, 'c, 'r) coq_All3

(** val coq_All3_rect :
    'a5 -> ('a1 -> 'a2 -> 'a3 -> 'a1 list -> 'a2 list -> 'a3 list -> 'a4 ->
    ('a1, 'a2, 'a3, 'a4) coq_All3 -> 'a5 -> 'a5) -> 'a1 list -> 'a2 list ->
    'a3 list -> ('a1, 'a2, 'a3, 'a4) coq_All3 -> 'a5 **)

let rec coq_All3_rect f f0 _ _ _ = function
| All3_nil -> f
| All3_cons (x, y, z, l, l', l'', y0, a0) ->
  f0 x y z l l' l'' y0 a0 (coq_All3_rect f f0 l l' l'' a0)

(** val coq_All3_rec :
    'a5 -> ('a1 -> 'a2 -> 'a3 -> 'a1 list -> 'a2 list -> 'a3 list -> 'a4 ->
    ('a1, 'a2, 'a3, 'a4) coq_All3 -> 'a5 -> 'a5) -> 'a1 list -> 'a2 list ->
    'a3 list -> ('a1, 'a2, 'a3, 'a4) coq_All3 -> 'a5 **)

let rec coq_All3_rec f f0 _ _ _ = function
| All3_nil -> f
| All3_cons (x, y, z, l, l', l'', y0, a0) ->
  f0 x y z l l' l'' y0 a0 (coq_All3_rec f f0 l l' l'' a0)

type ('a, 'b, 'c, 'r) coq_All3_sig = ('a, 'b, 'c, 'r) coq_All3

(** val coq_All3_sig_pack :
    'a1 list -> 'a2 list -> 'a3 list -> ('a1, 'a2, 'a3, 'a4) coq_All3 -> ('a1
    list * ('a2 list * 'a3 list)) * ('a1, 'a2, 'a3, 'a4) coq_All3 **)

let coq_All3_sig_pack x x0 x1 all3_var =
  (x,(x0,x1)),all3_var

(** val coq_All3_Signature :
    'a1 list -> 'a2 list -> 'a3 list -> (('a1, 'a2, 'a3, 'a4) coq_All3, 'a1
    list * ('a2 list * 'a3 list), ('a1, 'a2, 'a3, 'a4) coq_All3_sig)
    coq_Signature **)

let coq_All3_Signature x x0 x1 all3_var =
  (x,(x0,x1)),all3_var

(** val coq_NoConfusionHomPackage_All3 :
    'a1 list -> 'a2 list -> 'a3 list -> ('a1, 'a2, 'a3, 'a4) coq_All3
    coq_NoConfusionPackage **)

let coq_NoConfusionHomPackage_All3 _ _ _ =
  Build_NoConfusionPackage

(** val coq_Forall2_rect :
    'a3 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> __ -> __ -> 'a3 -> 'a3) ->
    'a1 list -> 'a2 list -> 'a3 **)

let rec coq_Forall2_rect hn hc l l' =
  match l with
  | Coq_nil ->
    (match l' with
     | Coq_nil -> hn
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | Coq_cons (a, l0) ->
    (match l' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (b, l1) ->
       let f = fun _ -> coq_Forall2_rect hn hc l0 l1 in
       hc a b l0 l1 __ __ (f __))

(** val coq_Forall2_rec :
    'a3 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> __ -> __ -> 'a3 -> 'a3) ->
    'a1 list -> 'a2 list -> 'a3 **)

let coq_Forall2_rec =
  coq_Forall2_rect

(** val coq_Forall2_dep_rect :
    'a3 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> __ -> __ -> __ -> __ -> 'a3
    -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 **)

let coq_Forall2_dep_rect hn hc l l' =
  coq_Forall2_rect (fun _ -> hn) (fun x y l0 l'0 _ _ iHa _ ->
    hc x y l0 l'0 __ __ __ __ (iHa __)) l l' __

(** val coq_Forall2_dep_rec :
    'a3 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> __ -> __ -> __ -> __ -> 'a3
    -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 **)

let coq_Forall2_dep_rec hn hc l l' =
  coq_Forall2_rect (fun _ -> hn) (fun x y l0 l'0 _ _ iHa _ ->
    hc x y l0 l'0 __ __ __ __ (iHa __)) l l' __

(** val alli : (nat -> 'a1 -> bool) -> nat -> 'a1 list -> bool **)

let rec alli p n = function
| Coq_nil -> Coq_true
| Coq_cons (hd, tl) ->
  (match p n hd with
   | Coq_true -> alli p (S n) tl
   | Coq_false -> Coq_false)

(** val allbiP :
    (nat -> 'a1 -> bool) -> nat -> 'a1 list -> (nat -> 'a1 -> 'a2 reflectT)
    -> ('a1, 'a2) coq_Alli reflectT **)

let allbiP p n l hp =
  equiv_reflectT (alli p n l) (fun _ ->
    let rec f l0 n0 =
      match l0 with
      | Coq_nil -> Alli_nil
      | Coq_cons (y, l1) ->
        Alli_cons (y, l1,
          (let r = hp n0 y in
           match r with
           | ReflectT p0 -> p0
           | ReflectF -> assert false (* absurd case *)), (f l1 (S n0)))
    in f l n)

(** val alli_Alli :
    (nat -> 'a1 -> bool) -> nat -> 'a1 list -> (__, ('a1, __) coq_Alli) iffT **)

let alli_Alli p n l =
  let r =
    allbiP p n l (fun i x ->
      let b = p i x in
      (match b with
       | Coq_true -> ReflectT __
       | Coq_false -> ReflectF))
  in
  (match r with
   | ReflectT a -> Coq_pair ((fun _ -> a), (Obj.magic __))
   | ReflectF ->
     Coq_pair ((fun _ -> assert false (* absurd case *)), (Obj.magic __)))

(** val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec forallb2 f l l' =
  match l with
  | Coq_nil ->
    (match l' with
     | Coq_nil -> Coq_true
     | Coq_cons (_, _) -> Coq_false)
  | Coq_cons (hd, tl) ->
    (match l' with
     | Coq_nil -> Coq_false
     | Coq_cons (hd', tl') ->
       (match f hd hd' with
        | Coq_true -> forallb2 f tl tl'
        | Coq_false -> Coq_false))

(** val forallbP :
    ('a1 -> bool) -> 'a1 list -> ('a1 -> reflect) -> reflect **)

let forallbP p l _ =
  iff_reflect (forallb p l)

(** val forallbP_cond :
    ('a1 -> bool) -> 'a1 list -> ('a1 -> __ -> reflect) -> reflect **)

let forallbP_cond p l _ =
  iff_reflect (forallb p l)

(** val map_eq_inj :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 list -> ('a1, __) coq_All **)

let rec map_eq_inj f g = function
| Coq_nil -> All_nil
| Coq_cons (y, l0) -> All_cons (y, l0, __, (map_eq_inj f g l0))

(** val forallb2_All2 :
    ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> ('a1, 'a2, __) coq_All2 **)

let rec forallb2_All2 p l l' =
  match l with
  | Coq_nil ->
    (match l' with
     | Coq_nil -> All2_nil
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | Coq_cons (y, l0) ->
    (match l' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (b, l1) ->
       All2_cons (y, b, l0, l1, __, (forallb2_All2 p l0 l1)))

(** val coq_All2P :
    ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> ('a1, 'a2, __) coq_All2
    reflectT **)

let coq_All2P p l l' =
  equiv_reflectT (forallb2 p l l') (fun _ -> forallb2_All2 p l l')

(** val coq_All2_refl :
    'a1 list -> ('a1 -> 'a2) -> ('a1, 'a1, 'a2) coq_All2 **)

let rec coq_All2_refl l hP =
  match l with
  | Coq_nil -> All2_nil
  | Coq_cons (y, l0) ->
    All2_cons (y, y, l0, l0, (hP y), (coq_All2_refl l0 hP))

(** val coq_All2_map_equiv :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a1 list -> 'a2 list -> (('a1, 'a2, 'a5)
    coq_All2, ('a3, 'a4, 'a5) coq_All2) iffT **)

let coq_All2_map_equiv f g l l' =
  Coq_pair ((fun x ->
    let rec f0 _ _ = function
    | All2_nil -> All2_nil
    | All2_cons (x0, y, l0, l'0, y0, a0) ->
      All2_cons ((f x0), (g y), (map f l0), (map g l'0), y0, (f0 l0 l'0 a0))
    in f0 l l' x),
    (let rec f0 l0 l'0 h =
       match l0 with
       | Coq_nil ->
         (match l'0 with
          | Coq_nil ->
            let h0 = (Coq_nil,Coq_nil),h in
            let h2 = let _,pr2 = h0 in pr2 in
            (match h2 with
             | All2_nil -> All2_nil
             | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
          | Coq_cons (_, _) -> assert false (* absurd case *))
       | Coq_cons (y, l1) ->
         (match l'0 with
          | Coq_nil -> assert false (* absurd case *)
          | Coq_cons (b, l2) ->
            let h0 = ((Coq_cons ((f y), (map f l1))),(Coq_cons ((g b),
              (map g l2)))),h
            in
            let h2 = let _,pr2 = h0 in pr2 in
            (match h2 with
             | All2_nil -> assert false (* absurd case *)
             | All2_cons (_, _, _, _, r, a) ->
               All2_cons (y, b, l1, l2, r, (f0 l1 l2 a))))
     in f0 l l'))

(** val coq_All2_map :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a5)
    coq_All2 -> ('a3, 'a4, 'a5) coq_All2 **)

let coq_All2_map f g l l' =
  let Coq_pair (x, _) = coq_All2_map_equiv f g l l' in x

(** val coq_All2_map_inv :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a1 list -> 'a2 list -> ('a3, 'a4, 'a5)
    coq_All2 -> ('a1, 'a2, 'a5) coq_All2 **)

let coq_All2_map_inv f g l l' =
  let Coq_pair (_, x) = coq_All2_map_equiv f g l l' in x

(** val coq_All2_All_mix_left :
    'a1 list -> 'a2 list -> ('a1, 'a3) coq_All -> ('a1, 'a2, 'a4) coq_All2 ->
    ('a1, 'a2, ('a3, 'a4) prod) coq_All2 **)

let rec coq_All2_All_mix_left _ _ x = function
| All2_nil -> All2_nil
| All2_cons (x1, y, l, l', y0, a) ->
  All2_cons (x1, y, l, l',
    (match x with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x2, _) -> Coq_pair (x2, y0)),
    (coq_All2_All_mix_left l l'
      (match x with
       | All_nil -> assert false (* absurd case *)
       | All_cons (_, _, _, x2) -> x2) a))

(** val coq_All2_All_mix_right :
    'a1 list -> 'a2 list -> ('a2, 'a3) coq_All -> ('a1, 'a2, 'a4) coq_All2 ->
    ('a1, 'a2, ('a4, 'a3) prod) coq_All2 **)

let rec coq_All2_All_mix_right _ _ x = function
| All2_nil -> All2_nil
| All2_cons (x1, y, l, l', y0, a) ->
  All2_cons (x1, y, l, l',
    (match x with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x2, _) -> Coq_pair (y0, x2)),
    (coq_All2_All_mix_right l l'
      (match x with
       | All_nil -> assert false (* absurd case *)
       | All_cons (_, _, _, x2) -> x2) a))

(** val coq_All2i_All_mix_left :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a3) coq_All -> ('a1, 'a2, 'a4)
    coq_All2i -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2i **)

let rec coq_All2i_All_mix_left n _ _ x = function
| All2i_nil -> All2i_nil
| All2i_cons (x1, y, l, r, y0, a) ->
  All2i_cons (x1, y, l, r,
    (match x with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x2, _) -> Coq_pair (x2, y0)),
    (coq_All2i_All_mix_left (S n) l r
      (match x with
       | All_nil -> assert false (* absurd case *)
       | All_cons (_, _, _, x2) -> x2) a))

(** val coq_All2i_All_mix_right :
    nat -> 'a1 list -> 'a2 list -> ('a2, 'a3) coq_All -> ('a1, 'a2, 'a4)
    coq_All2i -> ('a1, 'a2, ('a4, 'a3) prod) coq_All2i **)

let rec coq_All2i_All_mix_right n _ _ x = function
| All2i_nil -> All2i_nil
| All2i_cons (x1, y, l, r, y0, a) ->
  All2i_cons (x1, y, l, r,
    (match x with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x2, _) -> Coq_pair (y0, x2)),
    (coq_All2i_All_mix_right (S n) l r
      (match x with
       | All_nil -> assert false (* absurd case *)
       | All_cons (_, _, _, x2) -> x2) a))

(** val coq_All2i_All2_mix_left :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2,
    'a4) coq_All2i -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2i **)

let rec coq_All2i_All2_mix_left n _ _ x = function
| All2i_nil -> All2i_nil
| All2i_cons (x1, y, l, r, y0, a) ->
  All2i_cons (x1, y, l, r,
    (match x with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, _, _, _, x2, _) -> Coq_pair (x2, y0)),
    (coq_All2i_All2_mix_left (S n) l r
      (match x with
       | All2_nil -> assert false (* absurd case *)
       | All2_cons (_, _, _, _, _, x2) -> x2) a))

(** val coq_Forall_All : 'a1 list -> ('a1, __) coq_All **)

let rec coq_Forall_All = function
| Coq_nil -> All_nil
| Coq_cons (y, l0) -> All_cons (y, l0, __, (coq_Forall_All l0))

(** val forallb_All : ('a1 -> bool) -> 'a1 list -> ('a1, __) coq_All **)

let forallb_All _ =
  coq_Forall_All

(** val coq_All_firstn :
    'a1 list -> nat -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All **)

let rec coq_All_firstn _ n = function
| All_nil -> All_nil
| All_cons (x, l, y, a) ->
  (match n with
   | O -> All_nil
   | S n0 ->
     All_cons (x,
       (let rec firstn n1 l0 =
          match n1 with
          | O -> Coq_nil
          | S n2 ->
            (match l0 with
             | Coq_nil -> Coq_nil
             | Coq_cons (a0, l1) -> Coq_cons (a0, (firstn n2 l1)))
        in firstn n0 l), y, (coq_All_firstn l n0 a)))

(** val coq_All_skipn :
    'a1 list -> nat -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All **)

let rec coq_All_skipn _ n = function
| All_nil -> All_nil
| All_cons (x, l, y, a) ->
  (match n with
   | O -> All_cons (x, l, y, a)
   | S n0 -> coq_All_skipn l n0 a)

(** val coq_All_app :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All -> (('a1, 'a2) coq_All, ('a1,
    'a2) coq_All) prod **)

let rec coq_All_app l l' =
  match l with
  | Coq_nil -> (fun x -> Coq_pair (All_nil, x))
  | Coq_cons (y, l0) ->
    let iHl = coq_All_app l0 l' in
    (fun h ->
    let h0 = (Coq_cons (y, (app l0 l'))),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, p, a) ->
       Coq_pair
         ((let x = iHl a in
           let Coq_pair (a0, _) = x in All_cons (y, l0, p, a0)),
         (let x = iHl a in let Coq_pair (_, b) = x in b))))

(** val coq_All_app_inv :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All -> ('a1,
    'a2) coq_All **)

let rec coq_All_app_inv _ l' hl hl' =
  match hl with
  | All_nil -> hl'
  | All_cons (x, l, y, a) ->
    All_cons (x,
      (let rec app0 l0 m =
         match l0 with
         | Coq_nil -> m
         | Coq_cons (a0, l1) -> Coq_cons (a0, (app0 l1 m))
       in app0 l l'), y, (coq_All_app_inv l l' a hl'))

(** val coq_All_True : 'a1 list -> ('a1, __) coq_All **)

let rec coq_All_True = function
| Coq_nil -> All_nil
| Coq_cons (y, l0) -> All_cons (y, l0, __, (coq_All_True l0))

(** val coq_All_tip : 'a1 -> ('a2, ('a1, 'a2) coq_All) iffT **)

let coq_All_tip a =
  Coq_pair ((fun x -> All_cons (a, Coq_nil, x, All_nil)), (fun x ->
    let x0 = (Coq_cons (a, Coq_nil)),x in
    let x2 = let _,pr2 = x0 in pr2 in
    (match x2 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, p, _) -> p)))

(** val coq_All_mix :
    'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a3) coq_All -> ('a1, ('a2, 'a3)
    prod) coq_All **)

let rec coq_All_mix _ a hq =
  match a with
  | All_nil ->
    (match hq with
     | All_nil -> All_nil
     | All_cons (_, _, _, _) -> assert false (* absurd case *))
  | All_cons (x, l, y, a0) ->
    (match hq with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x0, x1) ->
       All_cons (x, l, (Coq_pair (y, x0)), (coq_All_mix l a0 x1)))

(** val coq_All2_All_left :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 -> 'a2 -> 'a3 ->
    'a4) -> ('a1, 'a4) coq_All **)

let rec coq_All2_All_left _ _ hF h =
  match hF with
  | All2_nil -> All_nil
  | All2_cons (x, y, l, l', y0, a) ->
    All_cons (x, l, (h x y y0), (coq_All2_All_left l l' a h))

(** val coq_All2_All_right :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 -> 'a2 -> 'a3 ->
    'a4) -> ('a2, 'a4) coq_All **)

let rec coq_All2_All_right _ _ hF h =
  match hF with
  | All2_nil -> All_nil
  | All2_cons (x, y, l, l', y0, a) ->
    All_cons (y, l', (h x y y0), (coq_All2_All_right l l' a h))

(** val coq_All2_right :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a2, 'a3) coq_All **)

let rec coq_All2_right _ _ = function
| All2_nil -> All_nil
| All2_cons (_, y, l, l', y0, a0) ->
  All_cons (y, l', y0, (coq_All2_right l l' a0))

(** val coq_All2_impl_All2 :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3 ->
    'a4) coq_All2 -> ('a1, 'a2, 'a4) coq_All2 **)

let rec coq_All2_impl_All2 _ _ a x =
  match a with
  | All2_nil ->
    (match x with
     | All2_nil -> All2_nil
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2_cons (x0, y, l, l', y0, a0) ->
    (match x with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, _, _, _, x1, x2) ->
       All2_cons (x0, y, l, l', (x1 y0), (coq_All2_impl_All2 l l' a0 x2)))

(** val coq_All2_impl :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 -> 'a2 -> 'a3 ->
    'a4) -> ('a1, 'a2, 'a4) coq_All2 **)

let rec coq_All2_impl _ _ a x =
  match a with
  | All2_nil -> All2_nil
  | All2_cons (x0, y, l, l', y0, a0) ->
    All2_cons (x0, y, l, l', (x x0 y y0), (coq_All2_impl l l' a0 x))

(** val coq_All2_eq_eq : 'a1 list -> 'a1 list -> ('a1, 'a1, __) coq_All2 **)

let rec coq_All2_eq_eq l = function
| Coq_nil -> All2_nil
| Coq_cons (y, l0) -> All2_cons (y, y, l0, l0, __, (coq_All2_eq_eq l l0))

(** val coq_All2_reflexivity :
    ('a1, 'a2) coq_Reflexive -> ('a1 list, ('a1, 'a1, 'a2) coq_All2)
    coq_Reflexive **)

let coq_All2_reflexivity hp x =
  coq_All2_refl x (fun x0 -> reflexivity hp x0)

(** val coq_All2_symmetry :
    ('a1, 'a2) coq_Symmetric -> ('a1 list, ('a1, 'a1, 'a2) coq_All2)
    coq_Symmetric **)

let rec coq_All2_symmetry hR _ _ = function
| All2_nil -> All2_nil
| All2_cons (x, y, l0, l', y0, a) ->
  All2_cons (y, x, l', l0, (hR x y y0), (coq_All2_symmetry hR l0 l' a))

(** val coq_All2_transitivity :
    ('a1, 'a2) coq_Transitive -> ('a1 list, ('a1, 'a1, 'a2) coq_All2)
    coq_Transitive **)

let rec coq_All2_transitivity hR _ _ _ l x =
  match l with
  | All2_nil -> x
  | All2_cons (x0, y, l0, l', y0, a) ->
    (match x with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, y1, _, l'0, x1, x2) ->
       All2_cons (x0, y1, l0, l'0, (hR x0 y y1 y0 x1),
         (coq_All2_transitivity hR l0 l' l'0 a x2)))

(** val coq_All2_apply :
    'a2 list -> 'a3 list -> 'a1 -> ('a2, 'a3, 'a1 -> 'a4) coq_All2 -> ('a2,
    'a3, 'a4) coq_All2 **)

let coq_All2_apply l l' a all =
  coq_All2_impl l l' all (fun _ _ x -> x a)

(** val coq_All2_apply_arrow :
    'a2 list -> 'a3 list -> 'a1 -> ('a2, 'a3, 'a1 -> 'a4) coq_All2 -> ('a2,
    'a3, 'a4) coq_All2 **)

let coq_All2_apply_arrow l l' a all =
  coq_All2_impl l l' all (fun _ _ x -> x a)

(** val coq_All2_apply_dep_arrow :
    'a1 list -> 'a2 list -> ('a1, 'a3) coq_All -> ('a1, 'a2, 'a3 -> 'a4)
    coq_All2 -> ('a1, 'a2, 'a4) coq_All2 **)

let coq_All2_apply_dep_arrow l l' a all =
  let all0 = coq_All2_All_mix_left l l' a all in
  coq_All2_impl l l' all0 (fun _ _ x -> let Coq_pair (a0, b) = x in b a0)

(** val coq_All2_apply_dep_All :
    'a1 list -> 'a2 list -> ('a1, 'a3) coq_All -> ('a1, 'a2, 'a3 -> 'a4)
    coq_All2 -> ('a2, 'a4) coq_All **)

let coq_All2_apply_dep_All l l' a all =
  let all0 = coq_All2_All_mix_left l l' a all in
  let all1 =
    coq_All2_impl l l' all0 (fun _ _ x -> let Coq_pair (a0, d) = x in d a0)
  in
  coq_All2_All_right l l' all1 (fun _ _ x -> x)

(** val coq_All2i_All_left :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> (nat -> 'a1
    -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a4) coq_All **)

let rec coq_All2i_All_left n _ _ hF h =
  match hF with
  | All2i_nil -> All_nil
  | All2i_cons (x, y, l, r, y0, a) ->
    All_cons (x, l, (h n x y y0), (coq_All2i_All_left (S n) l r a h))

(** val coq_All2i_All_right :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> (nat -> 'a1
    -> 'a2 -> 'a3 -> 'a4) -> ('a2, 'a4) coq_All **)

let rec coq_All2i_All_right n _ _ hF h =
  match hF with
  | All2i_nil -> All_nil
  | All2i_cons (x, y, l, r, y0, a) ->
    All_cons (y, r, (h n x y y0), (coq_All2i_All_right (S n) l r a h))

(** val coq_All2_dep_impl :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3, 'a4)
    coq_All2_dep -> ('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> ('a1, 'a2, 'a3, 'a5)
    coq_All2_dep **)

let rec coq_All2_dep_impl _ _ _ a0 x =
  match a0 with
  | All2_dep_nil -> All2_dep_nil
  | All2_dep_cons (x0, y, l, l', r, rs, y0, a) ->
    All2_dep_cons (x0, y, l, l', r, rs, (x x0 y r y0),
      (coq_All2_dep_impl l l' rs a x))

(** val coq_All_refl : 'a1 list -> ('a1 -> 'a2) -> ('a1, 'a2) coq_All **)

let rec coq_All_refl l hp =
  match l with
  | Coq_nil -> All_nil
  | Coq_cons (y, l0) -> All_cons (y, l0, (hp y), (coq_All_refl l0 hp))

(** val coq_All_rev_map :
    ('a2 -> 'a1) -> 'a2 list -> ('a2, 'a3) coq_All -> ('a1, 'a3) coq_All **)

let rec coq_All_rev_map f _ = function
| All_nil -> All_nil
| All_cons (x0, l, y, a) ->
  coq_All_app_inv (rev_map f l) (Coq_cons ((f x0), Coq_nil))
    (coq_All_rev_map f l a) (All_cons ((f x0), Coq_nil, y, All_nil))

(** val coq_All_rev : 'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All **)

let coq_All_rev l =
  rev_ind (fun _ -> All_nil) (fun x l0 iHl x0 ->
    let x1 = coq_All_app l0 (Coq_cons (x, Coq_nil)) x0 in
    let Coq_pair (a, a0) = x1 in
    (match a0 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x2, _) ->
       let x3 = iHl a in All_cons (x, (List.rev l0), x2, x3))) l

(** val coq_All_rev_inv :
    'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All **)

let coq_All_rev_inv l =
  rev_ind (fun _ -> All_nil) (fun x l0 iHl x0 ->
    let x1 = coq_All_app (List.rev (Coq_cons (x, Coq_nil))) (List.rev l0) x0
    in
    let Coq_pair (a, a0) = x1 in
    (match a with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x2, x3) ->
       coq_All_app_inv l0 (Coq_cons (x, Coq_nil)) (iHl a0) (All_cons (x,
         Coq_nil, x2, x3)))) l

(** val coq_All_impl_All :
    'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a2 -> 'a3) coq_All -> ('a1, 'a3)
    coq_All **)

let rec coq_All_impl_All _ a x =
  match a with
  | All_nil ->
    (match x with
     | All_nil -> All_nil
     | All_cons (_, _, _, _) -> assert false (* absurd case *))
  | All_cons (x0, l, y, a0) ->
    (match x with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x1, x2) ->
       All_cons (x0, l, (x1 y), (coq_All_impl_All l a0 x2)))

(** val coq_Alli_impl_Alli :
    'a1 list -> nat -> ('a1, 'a2) coq_Alli -> ('a1, 'a2 -> 'a3) coq_Alli ->
    ('a1, 'a3) coq_Alli **)

let rec coq_Alli_impl_Alli _ n x x0 =
  match x with
  | Alli_nil ->
    (match x0 with
     | Alli_nil -> Alli_nil
     | Alli_cons (_, _, _, _) -> assert false (* absurd case *))
  | Alli_cons (hd, tl, y, a) ->
    (match x0 with
     | Alli_nil -> assert false (* absurd case *)
     | Alli_cons (_, _, x1, x2) ->
       Alli_cons (hd, tl, (x1 y), (coq_Alli_impl_Alli tl (S n) a x2)))

(** val coq_All_impl :
    'a1 list -> ('a1, 'a2) coq_All -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a3)
    coq_All **)

let rec coq_All_impl _ a x =
  match a with
  | All_nil -> All_nil
  | All_cons (x0, l, y, a0) ->
    All_cons (x0, l, (x x0 y), (coq_All_impl l a0 x))

(** val coq_Alli_impl :
    'a1 list -> nat -> ('a1, 'a2) coq_Alli -> (nat -> 'a1 -> 'a2 -> 'a3) ->
    ('a1, 'a3) coq_Alli **)

let rec coq_Alli_impl _ n x x0 =
  match x with
  | Alli_nil -> Alli_nil
  | Alli_cons (hd, tl, y, a) ->
    Alli_cons (hd, tl, (x0 n hd y), (coq_Alli_impl tl (S n) a x0))

(** val coq_All_map :
    ('a1 -> 'a2) -> 'a1 list -> ('a1, 'a3) coq_All -> ('a2, 'a3) coq_All **)

let rec coq_All_map f _ = function
| All_nil -> All_nil
| All_cons (x0, l, y, a) ->
  All_cons ((f x0),
    (let rec map0 = function
     | Coq_nil -> Coq_nil
     | Coq_cons (a0, t) -> Coq_cons ((f a0), (map0 t))
     in map0 l), y, (coq_All_map f l a))

(** val coq_All_map_inv :
    ('a1 -> 'a2) -> 'a1 list -> ('a2, 'a3) coq_All -> ('a1, 'a3) coq_All **)

let rec coq_All_map_inv f l hf =
  match l with
  | Coq_nil ->
    (match hf with
     | All_nil -> All_nil
     | All_cons (_, _, _, _) -> assert false (* absurd case *))
  | Coq_cons (y, l0) ->
    (match hf with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x, x0) ->
       All_cons (y, l0, x, (coq_All_map_inv f l0 x0)))

(** val coq_In_All : 'a1 list -> ('a1 -> __ -> 'a2) -> ('a1, 'a2) coq_All **)

let rec coq_In_All l x =
  match l with
  | Coq_nil -> All_nil
  | Coq_cons (y, l0) ->
    All_cons (y, l0, (x y __), (coq_In_All l0 (fun x0 _ -> x x0 __)))

(** val coq_All_nth_error :
    'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_All -> 'a2 **)

let rec coq_All_nth_error _ i x = function
| All_nil -> assert false (* absurd case *)
| All_cons (_, l, y, a) ->
  (match i with
   | O -> y
   | S n -> coq_All_nth_error l n x a)

(** val coq_Alli_mix :
    nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a3) coq_Alli -> ('a1,
    ('a2, 'a3) prod) coq_Alli **)

let rec coq_Alli_mix n _ a hq =
  match a with
  | Alli_nil ->
    (match hq with
     | Alli_nil -> Alli_nil
     | Alli_cons (_, _, _, _) -> assert false (* absurd case *))
  | Alli_cons (hd, tl, y, a0) ->
    (match hq with
     | Alli_nil -> assert false (* absurd case *)
     | Alli_cons (_, _, x, x0) ->
       Alli_cons (hd, tl, (Coq_pair (y, x)), (coq_Alli_mix (S n) tl a0 x0)))

(** val coq_Alli_All :
    'a1 list -> nat -> ('a1, 'a2) coq_Alli -> (nat -> 'a1 -> 'a2 -> 'a3) ->
    ('a1, 'a3) coq_All **)

let rec coq_Alli_All _ n x x0 =
  match x with
  | Alli_nil -> All_nil
  | Alli_cons (hd, tl, y, a) ->
    All_cons (hd, tl, (x0 n hd y), (coq_Alli_All tl (S n) a x0))

(** val coq_Alli_app :
    nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Alli -> (('a1, 'a2)
    coq_Alli, ('a1, 'a2) coq_Alli) prod **)

let rec coq_Alli_app n l l' =
  match l with
  | Coq_nil -> (fun h -> Coq_pair (Alli_nil, h))
  | Coq_cons (y, l0) ->
    let iHl = fun x x0 -> coq_Alli_app x l0 x0 in
    (fun h ->
    match h with
    | Alli_nil -> assert false (* absurd case *)
    | Alli_cons (_, _, x, x0) ->
      Coq_pair ((Alli_cons (y, l0, x,
        (let n0 = S n in let Coq_pair (x1, _) = iHl n0 l' x0 in x1))),
        (let n0 = S n in let Coq_pair (_, x1) = iHl n0 l' x0 in x1)))

(** val coq_Alli_nth_error :
    nat -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_Alli -> 'a2 **)

let rec coq_Alli_nth_error k _ i x = function
| Alli_nil -> assert false (* absurd case *)
| Alli_cons (_, tl, y, a) ->
  (match i with
   | O -> y
   | S n -> coq_Alli_nth_error (S k) tl n x a)

(** val forall_nth_error_All :
    'a1 list -> (nat -> 'a1 -> __ -> 'a2) -> ('a1, 'a2) coq_All **)

let rec forall_nth_error_All l h =
  match l with
  | Coq_nil -> All_nil
  | Coq_cons (y, l0) ->
    All_cons (y, l0, (h O y __),
      (forall_nth_error_All l0 (fun i x _ -> h (S i) x __)))

(** val forall_nth_error_Alli :
    nat -> 'a1 list -> (nat -> 'a1 -> __ -> 'a2) -> ('a1, 'a2) coq_Alli **)

let rec forall_nth_error_Alli k l h =
  match l with
  | Coq_nil -> Alli_nil
  | Coq_cons (y, l0) ->
    Alli_cons (y, l0, (h O y __),
      (forall_nth_error_Alli (S k) l0 (fun i x _ -> h (S i) x __)))

(** val coq_Alli_mapi :
    (nat -> 'a1 -> 'a2) -> nat -> 'a1 list -> (('a1, 'a3) coq_Alli, ('a2,
    'a3) coq_Alli) iffT **)

let coq_Alli_mapi f k l =
  Coq_pair ((fun x ->
    let rec f0 n _ = function
    | Alli_nil -> Alli_nil
    | Alli_cons (hd, tl, y, a0) ->
      Alli_cons ((f n hd), (mapi_rec f tl (S n)), y, (f0 (S n) tl a0))
    in f0 k l x),
    (let rec f0 l0 k0 x =
       match l0 with
       | Coq_nil -> Alli_nil
       | Coq_cons (y, l1) ->
         (match x with
          | Alli_nil -> assert false (* absurd case *)
          | Alli_cons (_, _, x0, x1) ->
            Alli_cons (y, l1, x0, (f0 l1 (S k0) x1)))
     in f0 l k))

(** val coq_Alli_shift :
    nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli **)

let rec coq_Alli_shift n _ = function
| Alli_nil -> Alli_nil
| Alli_cons (hd, tl, y, a0) ->
  Alli_cons (hd, tl, y, (coq_Alli_shift (S n) tl a0))

(** val coq_Alli_rev :
    nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli **)

let coq_Alli_rev k l =
  rev_ind (fun _ _ -> Alli_nil) (fun x l0 iHl k0 x0 ->
    let x1 = coq_Alli_app k0 l0 (Coq_cons (x, Coq_nil)) x0 in
    let Coq_pair (a, b) = x1 in
    Alli_cons (x, (List.rev l0),
    (match b with
     | Alli_nil -> assert false (* absurd case *)
     | Alli_cons (_, _, x2, _) -> x2),
    (let iHl0 = iHl k0 a in
     coq_Alli_shift O (List.rev l0)
       (coq_Alli_impl (List.rev l0) O iHl0 (fun _ _ x2 -> x2))))) l k

(** val coq_Alli_rev_inv :
    nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli **)

let coq_Alli_rev_inv k l alli0 =
  coq_Alli_rev k (List.rev l) alli0

(** val coq_Alli_app_inv :
    'a1 list -> 'a1 list -> nat -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli
    -> ('a1, 'a2) coq_Alli **)

let rec coq_Alli_app_inv _ l' n x x0 =
  match x with
  | Alli_nil -> x0
  | Alli_cons (hd, tl, y, a) ->
    let iHX = coq_Alli_app_inv tl l' (S n) a x0 in
    Alli_cons (hd, (app tl l'), y, iHX)

(** val coq_Alli_rev_nth_error :
    'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_Alli -> 'a2 **)

let coq_Alli_rev_nth_error l n x x0 =
  let rec f l0 n0 x1 x2 =
    match l0 with
    | Coq_nil -> (fun _ -> assert false (* absurd case *))
    | Coq_cons (y, l1) ->
      let __top_assumption_ =
        coq_Alli_app O (List.rev l1) (Coq_cons (y, Coq_nil)) x2
      in
      let _evar_0_ = fun alll alla ->
        match alla with
        | Alli_nil -> assert false (* absurd case *)
        | Alli_cons (_, _, x3, _) ->
          (match n0 with
           | O -> x3
           | S n1 -> f l1 n1 x1 alll __)
      in
      (fun _ -> let Coq_pair (a, b) = __top_assumption_ in _evar_0_ a b)
  in f l n x x0 __

(** val coq_Alli_shiftn :
    nat -> 'a1 list -> nat -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli **)

let rec coq_Alli_shiftn k _ n = function
| Alli_nil -> Alli_nil
| Alli_cons (hd, tl, y, a) ->
  Alli_cons (hd, tl, y, (coq_Alli_shiftn (S k) tl n a))

(** val coq_Alli_shiftn_inv :
    nat -> 'a1 list -> nat -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_Alli **)

let rec coq_Alli_shiftn_inv k l n x =
  match l with
  | Coq_nil -> Alli_nil
  | Coq_cons (y, l0) ->
    Alli_cons (y, l0,
      (match x with
       | Alli_nil -> assert false (* absurd case *)
       | Alli_cons (_, _, x0, _) -> x0),
      (match x with
       | Alli_nil -> assert false (* absurd case *)
       | Alli_cons (_, _, _, x0) -> coq_Alli_shiftn_inv (S k) l0 n x0))

(** val coq_Alli_All_mix :
    nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a3) coq_All -> ('a1,
    ('a2, 'a3) prod) coq_Alli **)

let rec coq_Alli_All_mix n _ a x =
  match a with
  | Alli_nil -> Alli_nil
  | Alli_cons (hd, tl, y, a0) ->
    Alli_cons (hd, tl,
      (match x with
       | All_nil -> assert false (* absurd case *)
       | All_cons (_, _, x0, _) -> Coq_pair (y, x0)),
      (match x with
       | All_nil -> assert false (* absurd case *)
       | All_cons (_, _, _, x0) -> coq_Alli_All_mix (S n) tl a0 x0))

type ('a, 'p) coq_OnOne2 =
| OnOne2_hd of 'a * 'a * 'a list * 'p
| OnOne2_tl of 'a * 'a list * 'a list * ('a, 'p) coq_OnOne2

(** val coq_OnOne2_rect :
    ('a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> ('a1 -> 'a1 list -> 'a1 list ->
    ('a1, 'a2) coq_OnOne2 -> 'a3 -> 'a3) -> 'a1 list -> 'a1 list -> ('a1,
    'a2) coq_OnOne2 -> 'a3 **)

let rec coq_OnOne2_rect f f0 _ _ = function
| OnOne2_hd (hd, hd', tl, y) -> f hd hd' tl y
| OnOne2_tl (hd, tl, tl', o0) ->
  f0 hd tl tl' o0 (coq_OnOne2_rect f f0 tl tl' o0)

(** val coq_OnOne2_rec :
    ('a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> ('a1 -> 'a1 list -> 'a1 list ->
    ('a1, 'a2) coq_OnOne2 -> 'a3 -> 'a3) -> 'a1 list -> 'a1 list -> ('a1,
    'a2) coq_OnOne2 -> 'a3 **)

let rec coq_OnOne2_rec f f0 _ _ = function
| OnOne2_hd (hd, hd', tl, y) -> f hd hd' tl y
| OnOne2_tl (hd, tl, tl', o0) ->
  f0 hd tl tl' o0 (coq_OnOne2_rec f f0 tl tl' o0)

type ('a, 'p) coq_OnOne2_sig = ('a, 'p) coq_OnOne2

(** val coq_OnOne2_sig_pack :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1 list * 'a1
    list) * ('a1, 'a2) coq_OnOne2 **)

let coq_OnOne2_sig_pack x x0 onOne2_var =
  (x,x0),onOne2_var

(** val coq_OnOne2_Signature :
    'a1 list -> 'a1 list -> (('a1, 'a2) coq_OnOne2, 'a1 list * 'a1 list,
    ('a1, 'a2) coq_OnOne2_sig) coq_Signature **)

let coq_OnOne2_Signature x x0 onOne2_var =
  (x,x0),onOne2_var

(** val coq_NoConfusionPackage_OnOne2 :
    (('a1 list * 'a1 list) * ('a1, 'a2) coq_OnOne2) coq_NoConfusionPackage **)

let coq_NoConfusionPackage_OnOne2 =
  Build_NoConfusionPackage

(** val coq_OnOne2_All_mix_left :
    'a1 list -> 'a1 list -> ('a1, 'a3) coq_All -> ('a1, 'a2) coq_OnOne2 ->
    ('a1, ('a2, 'a3) prod) coq_OnOne2 **)

let rec coq_OnOne2_All_mix_left _ _ h = function
| OnOne2_hd (hd, hd', tl, y) ->
  OnOne2_hd (hd, hd', tl,
    (match h with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x0, _) -> Coq_pair (y, x0)))
| OnOne2_tl (hd, tl, tl', o) ->
  OnOne2_tl (hd, tl, tl',
    (match h with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, _, x0) -> coq_OnOne2_All_mix_left tl tl' x0 o))

(** val coq_OnOne2_app :
    'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a2)
    coq_OnOne2 **)

let rec coq_OnOne2_app l tl tl' x =
  match l with
  | Coq_nil -> x
  | Coq_cons (y, l0) ->
    OnOne2_tl (y, (app l0 tl), (app l0 tl'), (coq_OnOne2_app l0 tl tl' x))

(** val coq_OnOne2_app_r :
    'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a2)
    coq_OnOne2 **)

let rec coq_OnOne2_app_r _ _ tl = function
| OnOne2_hd (hd, hd', tl0, y) ->
  OnOne2_hd (hd, hd',
    (let rec app0 l m =
       match l with
       | Coq_nil -> m
       | Coq_cons (a, l1) -> Coq_cons (a, (app0 l1 m))
     in app0 tl0 tl), y)
| OnOne2_tl (hd, tl0, tl', o) ->
  OnOne2_tl (hd,
    (let rec app0 l m =
       match l with
       | Coq_nil -> m
       | Coq_cons (a, l1) -> Coq_cons (a, (app0 l1 m))
     in app0 tl0 tl),
    (let rec app0 l m =
       match l with
       | Coq_nil -> m
       | Coq_cons (a, l1) -> Coq_cons (a, (app0 l1 m))
     in app0 tl' tl), (coq_OnOne2_app_r tl0 tl' tl o))

(** val coq_OnOne2_mapP :
    'a1 list -> 'a1 list -> ('a1 -> 'a2) -> ('a1, __) coq_OnOne2 -> ('a2, __)
    coq_OnOne2 **)

let rec coq_OnOne2_mapP _ _ f = function
| OnOne2_hd (hd, hd', tl, _) -> OnOne2_hd ((f hd), (f hd'), (map f tl), __)
| OnOne2_tl (hd, tl, tl', o) ->
  OnOne2_tl ((f hd), (map f tl), (map f tl'), (coq_OnOne2_mapP tl tl' f o))

(** val coq_OnOne2_map :
    'a1 list -> 'a1 list -> ('a1 -> 'a2) -> ('a1, ('a2, 'a1, 'a3) on_Trel)
    coq_OnOne2 -> ('a2, 'a3) coq_OnOne2 **)

let rec coq_OnOne2_map _ _ f = function
| OnOne2_hd (hd, hd', tl, y) -> OnOne2_hd ((f hd), (f hd'), (map f tl), y)
| OnOne2_tl (hd, tl, tl', o) ->
  OnOne2_tl ((f hd), (map f tl), (map f tl'), (coq_OnOne2_map tl tl' f o))

(** val coq_OnOne2_sym :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a2) coq_OnOne2 **)

let rec coq_OnOne2_sym _ _ = function
| OnOne2_hd (hd, hd', tl, y) -> OnOne2_hd (hd', hd, tl, y)
| OnOne2_tl (hd, tl, tl', o) ->
  OnOne2_tl (hd, tl', tl, (coq_OnOne2_sym tl' tl o))

(** val coq_OnOne2_exist :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1 -> 'a1 -> 'a2 ->
    ('a1, ('a3, 'a3) prod) sigT) -> ('a1 list, (('a1, 'a3) coq_OnOne2, ('a1,
    'a3) coq_OnOne2) prod) sigT **)

let rec coq_OnOne2_exist _ _ h hPQ =
  match h with
  | OnOne2_hd (hd, hd', tl, y) ->
    let s = hPQ hd hd' y in
    let Coq_existT (x, p) = s in
    let Coq_pair (q, q0) = p in
    Coq_existT ((Coq_cons (x, tl)), (Coq_pair ((OnOne2_hd (hd, x, tl, q)),
    (OnOne2_hd (hd', x, tl, q0)))))
  | OnOne2_tl (hd, tl, tl', o) ->
    let Coq_existT (x, p) = coq_OnOne2_exist tl tl' o hPQ in
    let Coq_pair (o0, o1) = p in
    Coq_existT ((Coq_cons (hd, x)), (Coq_pair ((OnOne2_tl (hd, tl, x, o0)),
    (OnOne2_tl (hd, tl', x, o1)))))

(** val coq_OnOne2_ind_l :
    ('a1 list -> 'a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> ('a1 list -> 'a1 ->
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> 'a3 -> 'a3) -> 'a1 list
    -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> 'a3 **)

let coq_OnOne2_ind_l hhd htl l l' h =
  let rec f _ _ = function
  | OnOne2_hd (hd, hd', tl, y) -> hhd l hd hd' tl y
  | OnOne2_tl (hd, tl, tl', o0) -> htl l hd tl tl' o0 (f tl tl' o0)
  in f l l' h

(** val coq_OnOne2_impl_exist_and_All :
    'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a1,
    'a3) coq_All2 -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> 'a3 -> ('a1, ('a4, 'a3)
    prod) sigT) -> ('a1 list, (('a1, 'a4) coq_OnOne2, ('a1, 'a1, 'a3)
    coq_All2) prod) sigT **)

let rec coq_OnOne2_impl_exist_and_All _ _ l3 h1 h2 h =
  match h1 with
  | OnOne2_hd (hd, hd', tl, y) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let hh = h hd a hd' y x in
          let Coq_existT (x1, p) = hh in
          let Coq_pair (r, r0) = p in
          Coq_existT ((Coq_cons (x1, tl)), (Coq_pair ((OnOne2_hd (hd, x1, tl,
          r)), (All2_cons (a, x1, l, tl, r0, x0)))))))
  | OnOne2_tl (hd, tl, tl', o) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let iHh1 = coq_OnOne2_impl_exist_and_All tl tl' l o x0 h in
          let Coq_existT (x1, p) = iHh1 in
          let Coq_pair (o0, a0) = p in
          Coq_existT ((Coq_cons (hd, x1)), (Coq_pair ((OnOne2_tl (hd, tl, x1,
          o0)), (All2_cons (a, hd, l, x1, x, a0)))))))

(** val coq_OnOne2_impl_exist_and_All_r :
    'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a1,
    'a3) coq_All2 -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> 'a3 -> ('a1, ('a4, 'a3)
    prod) sigT) -> ('a1 list, (('a1, 'a4) coq_OnOne2, ('a1, 'a1, 'a3)
    coq_All2) prod) sigT **)

let rec coq_OnOne2_impl_exist_and_All_r _ _ l3 h1 h2 h =
  match h1 with
  | OnOne2_hd (hd, hd', tl, y) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let hh = h hd a hd' y x in
          let Coq_existT (x1, p) = hh in
          let Coq_pair (r, r0) = p in
          Coq_existT ((Coq_cons (x1, tl)), (Coq_pair ((OnOne2_hd (hd, x1, tl,
          r)), (All2_cons (x1, a, tl, l, r0, x0)))))))
  | OnOne2_tl (hd, tl, tl', o) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let iHh1 = coq_OnOne2_impl_exist_and_All_r tl tl' l o x0 h in
          let Coq_existT (x1, p) = iHh1 in
          let Coq_pair (o0, a0) = p in
          Coq_existT ((Coq_cons (hd, x1)), (Coq_pair ((OnOne2_tl (hd, tl, x1,
          o0)), (All2_cons (hd, a, x1, l, x, a0)))))))

(** val coq_OnOne2_split :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, ('a1, ('a1 list,
    ('a1 list, ('a2, __) prod) sigT) sigT) sigT) sigT **)

let rec coq_OnOne2_split _ _ = function
| OnOne2_hd (hd, hd', tl, y) ->
  Coq_existT (hd, (Coq_existT (hd', (Coq_existT (Coq_nil, (Coq_existT (tl,
    (Coq_pair (y, __)))))))))
| OnOne2_tl (hd, tl, tl', o0) ->
  let Coq_existT (x, s) = coq_OnOne2_split tl tl' o0 in
  let Coq_existT (x0, s0) = s in
  let Coq_existT (x1, s1) = s0 in
  let Coq_existT (x2, p) = s1 in
  Coq_existT (x, (Coq_existT (x0, (Coq_existT ((Coq_cons (hd, x1)),
  (Coq_existT (x2, (let Coq_pair (a, _) = p in Coq_pair (a, __)))))))))

(** val coq_OnOne2_impl :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1 -> 'a1 -> 'a2 ->
    'a3) -> ('a1, 'a3) coq_OnOne2 **)

let rec coq_OnOne2_impl _ _ o x =
  match o with
  | OnOne2_hd (hd, hd', tl, y) -> OnOne2_hd (hd, hd', tl, (x hd hd' y))
  | OnOne2_tl (hd, tl, tl', o0) ->
    OnOne2_tl (hd, tl, tl', (coq_OnOne2_impl tl tl' o0 x))

(** val coq_OnOne2_nth_error :
    'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_OnOne2 -> ('a1, (__,
    (__, 'a2) sum) prod) sigT **)

let rec coq_OnOne2_nth_error _ _ n t = function
| OnOne2_hd (_, hd', _, y) ->
  (match n with
   | O -> Coq_existT (hd', (Coq_pair (__, (Coq_inr y))))
   | S _ -> Coq_existT (t, (Coq_pair (__, (Coq_inl __)))))
| OnOne2_tl (_, tl, tl', o) ->
  (match n with
   | O -> Coq_existT (t, (Coq_pair (__, (Coq_inl __))))
   | S n0 -> coq_OnOne2_nth_error tl tl' n0 t o)

(** val coq_OnOne2_nth_error_r :
    'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_OnOne2 -> ('a1, (__,
    (__, 'a2) sum) prod) sigT **)

let rec coq_OnOne2_nth_error_r _ _ n t' = function
| OnOne2_hd (hd, _, _, y) ->
  (match n with
   | O -> Coq_existT (hd, (Coq_pair (__, (Coq_inr y))))
   | S _ -> Coq_existT (t', (Coq_pair (__, (Coq_inl __)))))
| OnOne2_tl (_, tl, tl', o) ->
  (match n with
   | O -> Coq_existT (t', (Coq_pair (__, (Coq_inl __))))
   | S n0 -> coq_OnOne2_nth_error_r tl tl' n0 t' o)

(** val coq_OnOne2_impl_All_r :
    'a1 list -> 'a1 list -> ('a1 -> 'a1 -> 'a3 -> 'a2 -> 'a3) -> ('a1, 'a2)
    coq_OnOne2 -> ('a1, 'a3) coq_All -> ('a1, 'a3) coq_All **)

let rec coq_OnOne2_impl_All_r _ _ hPQ x h =
  match x with
  | OnOne2_hd (hd, hd', tl, y) ->
    let h0 = (Coq_cons (hd, tl)),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, q, a) -> All_cons (hd', tl, (hPQ hd hd' q y), a))
  | OnOne2_tl (hd, tl, tl', o) ->
    let h0 = (Coq_cons (hd, tl)),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, q, a) ->
       All_cons (hd, tl', q, (coq_OnOne2_impl_All_r tl tl' hPQ o a)))

(** val coq_OnOne2_All2_All2 :
    'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a1,
    'a3) coq_All2 -> ('a1 -> 'a1 -> 'a3 -> 'a4) -> ('a1 -> 'a1 -> 'a1 -> 'a2
    -> 'a3 -> 'a4) -> ('a1, 'a1, 'a4) coq_All2 **)

let rec coq_OnOne2_All2_All2 _ _ l3 o h =
  match o with
  | OnOne2_hd (hd, hd', tl, y) ->
    let h0 = ((Coq_cons (hd, tl)),l3),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (fun hf hf' ->
    match h2 with
    | All2_nil -> assert false (* absurd case *)
    | All2_cons (_, y0, _, l', r, a) ->
      let hf'0 = hf' hd hd' y0 y r in
      All2_cons (hd', y0, tl, l', hf'0, (coq_All2_impl tl l' a hf)))
  | OnOne2_tl (hd, tl, tl', o0) ->
    let h0 = ((Coq_cons (hd, tl)),l3),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (fun hf ->
    match h2 with
    | All2_nil -> assert false (* absurd case *)
    | All2_cons (_, y, _, l', r, a) ->
      let iHo = coq_OnOne2_All2_All2 tl tl' l' o0 a hf in
      (fun x -> All2_cons (hd, y, tl', l', (hf hd y r), (iHo x))))

(** val coq_OnOne2_All_All :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2 -> ('a1, 'a3) coq_All ->
    ('a1 -> 'a3 -> 'a4) -> ('a1 -> 'a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a4)
    coq_All **)

let rec coq_OnOne2_All_All _ _ o h =
  match o with
  | OnOne2_hd (hd, hd', tl, y) ->
    let h0 = (Coq_cons (hd, tl)),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (fun hf hf' ->
    match h2 with
    | All_nil -> assert false (* absurd case *)
    | All_cons (_, _, r, a) ->
      let hf'0 = hf' hd hd' y r in
      All_cons (hd', tl, hf'0, (coq_All_impl tl a hf)))
  | OnOne2_tl (hd, tl, tl', o0) ->
    let h0 = (Coq_cons (hd, tl)),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (fun hf ->
    match h2 with
    | All_nil -> assert false (* absurd case *)
    | All_cons (_, _, r, a) ->
      let iHo = coq_OnOne2_All_All tl tl' o0 a hf in
      (fun x -> All_cons (hd, tl', (hf hd r), (iHo x))))

type ('a, 'p) coq_OnOne2i =
| OnOne2i_hd of nat * 'a * 'a * 'a list * 'p
| OnOne2i_tl of nat * 'a * 'a list * 'a list * ('a, 'p) coq_OnOne2i

(** val coq_OnOne2i_rect :
    (nat -> 'a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> (nat -> 'a1 -> 'a1 list
    -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> 'a3 -> 'a3) -> nat -> 'a1 list
    -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> 'a3 **)

let rec coq_OnOne2i_rect f f0 _ _ _ = function
| OnOne2i_hd (i, hd, hd', tl, y) -> f i hd hd' tl y
| OnOne2i_tl (i, hd, tl, tl', o0) ->
  f0 i hd tl tl' o0 (coq_OnOne2i_rect f f0 (S i) tl tl' o0)

(** val coq_OnOne2i_rec :
    (nat -> 'a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> (nat -> 'a1 -> 'a1 list
    -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> 'a3 -> 'a3) -> nat -> 'a1 list
    -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> 'a3 **)

let rec coq_OnOne2i_rec f f0 _ _ _ = function
| OnOne2i_hd (i, hd, hd', tl, y) -> f i hd hd' tl y
| OnOne2i_tl (i, hd, tl, tl', o0) ->
  f0 i hd tl tl' o0 (coq_OnOne2i_rec f f0 (S i) tl tl' o0)

type ('a, 'p) coq_OnOne2i_sig = ('a, 'p) coq_OnOne2i

(** val coq_OnOne2i_sig_pack :
    nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> (nat * ('a1
    list * 'a1 list)) * ('a1, 'a2) coq_OnOne2i **)

let coq_OnOne2i_sig_pack x x0 x1 onOne2i_var =
  (x,(x0,x1)),onOne2i_var

(** val coq_OnOne2i_Signature :
    nat -> 'a1 list -> 'a1 list -> (('a1, 'a2) coq_OnOne2i, nat * ('a1
    list * 'a1 list), ('a1, 'a2) coq_OnOne2i_sig) coq_Signature **)

let coq_OnOne2i_Signature x x0 x1 onOne2i_var =
  (x,(x0,x1)),onOne2i_var

(** val coq_NoConfusionPackage_OnOne2i :
    ((nat * ('a1 list * 'a1 list)) * ('a1, 'a2) coq_OnOne2i)
    coq_NoConfusionPackage **)

let coq_NoConfusionPackage_OnOne2i =
  Build_NoConfusionPackage

(** val coq_OnOne2i_All_mix_left :
    nat -> 'a1 list -> 'a1 list -> ('a1, 'a3) coq_All -> ('a1, 'a2)
    coq_OnOne2i -> ('a1, ('a2, 'a3) prod) coq_OnOne2i **)

let rec coq_OnOne2i_All_mix_left _ _ _ h = function
| OnOne2i_hd (i, hd, hd', tl, y) ->
  OnOne2i_hd (i, hd, hd', tl,
    (match h with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x0, _) -> Coq_pair (y, x0)))
| OnOne2i_tl (i, hd, tl, tl', o) ->
  OnOne2i_tl (i, hd, tl, tl',
    (match h with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, _, x0) -> coq_OnOne2i_All_mix_left (S i) tl tl' x0 o))

(** val coq_OnOne2i_app :
    nat -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i ->
    ('a1, 'a2) coq_OnOne2i **)

let rec coq_OnOne2i_app i l tl tl' x =
  match l with
  | Coq_nil -> x
  | Coq_cons (y, l0) ->
    OnOne2i_tl (i, y, (app l0 tl), (app l0 tl'),
      (coq_OnOne2i_app (S i) l0 tl tl' x))

(** val coq_OnOne2i_app_r :
    nat -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i ->
    ('a1, 'a2) coq_OnOne2i **)

let rec coq_OnOne2i_app_r _ _ _ tl = function
| OnOne2i_hd (i, hd, hd', tl0, y) ->
  OnOne2i_hd (i, hd, hd',
    (let rec app0 l m =
       match l with
       | Coq_nil -> m
       | Coq_cons (a, l1) -> Coq_cons (a, (app0 l1 m))
     in app0 tl0 tl), y)
| OnOne2i_tl (i, hd, tl0, tl', o) ->
  OnOne2i_tl (i, hd,
    (let rec app0 l m =
       match l with
       | Coq_nil -> m
       | Coq_cons (a, l1) -> Coq_cons (a, (app0 l1 m))
     in app0 tl0 tl),
    (let rec app0 l m =
       match l with
       | Coq_nil -> m
       | Coq_cons (a, l1) -> Coq_cons (a, (app0 l1 m))
     in app0 tl' tl), (coq_OnOne2i_app_r (S i) tl0 tl' tl o))

(** val coq_OnOne2i_mapP :
    nat -> 'a1 list -> 'a1 list -> ('a1 -> 'a2) -> ('a1, __) coq_OnOne2i ->
    ('a2, __) coq_OnOne2i **)

let rec coq_OnOne2i_mapP _ _ _ f = function
| OnOne2i_hd (i, hd, hd', tl, _) ->
  OnOne2i_hd (i, (f hd), (f hd'), (map f tl), __)
| OnOne2i_tl (i, hd, tl, tl', o) ->
  OnOne2i_tl (i, (f hd), (map f tl), (map f tl'),
    (coq_OnOne2i_mapP (S i) tl tl' f o))

(** val coq_OnOne2i_map :
    nat -> 'a1 list -> 'a1 list -> ('a1 -> 'a2) -> ('a1, ('a2, 'a1, 'a3)
    on_Trel) coq_OnOne2i -> ('a2, 'a3) coq_OnOne2i **)

let rec coq_OnOne2i_map _ _ _ f = function
| OnOne2i_hd (i, hd, hd', tl, y) ->
  OnOne2i_hd (i, (f hd), (f hd'), (map f tl), y)
| OnOne2i_tl (i, hd, tl, tl', o) ->
  OnOne2i_tl (i, (f hd), (map f tl), (map f tl'),
    (coq_OnOne2i_map (S i) tl tl' f o))

(** val coq_OnOne2i_sym :
    nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> ('a1, 'a2)
    coq_OnOne2i **)

let rec coq_OnOne2i_sym _ _ _ = function
| OnOne2i_hd (i, hd, hd', tl, y) -> OnOne2i_hd (i, hd', hd, tl, y)
| OnOne2i_tl (i, hd, tl, tl', o) ->
  OnOne2i_tl (i, hd, tl', tl, (coq_OnOne2i_sym (S i) tl' tl o))

(** val coq_OnOne2i_exist :
    nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> (nat -> 'a1 ->
    'a1 -> 'a2 -> ('a1, ('a3, 'a3) prod) sigT) -> ('a1 list, (('a1, 'a3)
    coq_OnOne2i, ('a1, 'a3) coq_OnOne2i) prod) sigT **)

let rec coq_OnOne2i_exist _ _ _ h hPQ =
  match h with
  | OnOne2i_hd (i, hd, hd', tl, y) ->
    let s = hPQ i hd hd' y in
    let Coq_existT (x, p) = s in
    let Coq_pair (q, q0) = p in
    Coq_existT ((Coq_cons (x, tl)), (Coq_pair ((OnOne2i_hd (i, hd, x, tl,
    q)), (OnOne2i_hd (i, hd', x, tl, q0)))))
  | OnOne2i_tl (i, hd, tl, tl', o) ->
    let Coq_existT (x, p) = coq_OnOne2i_exist (S i) tl tl' o hPQ in
    let Coq_pair (o0, o1) = p in
    Coq_existT ((Coq_cons (hd, x)), (Coq_pair ((OnOne2i_tl (i, hd, tl, x,
    o0)), (OnOne2i_tl (i, hd, tl', x, o1)))))

(** val coq_OnOne2i_ind_l :
    ('a1 list -> nat -> 'a1 -> 'a1 -> 'a1 list -> 'a2 -> 'a3) -> ('a1 list ->
    nat -> 'a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> 'a3 ->
    'a3) -> nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> 'a3 **)

let coq_OnOne2i_ind_l hhd htl i l l' h =
  let rec f _ _ _ = function
  | OnOne2i_hd (i0, hd, hd', tl, y) -> hhd l i0 hd hd' tl y
  | OnOne2i_tl (i0, hd, tl, tl', o0) ->
    htl l i0 hd tl tl' o0 (f (S i0) tl tl' o0)
  in f i l l' h

(** val coq_OnOne2i_impl_exist_and_All :
    nat -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i ->
    ('a1, 'a1, 'a3) coq_All2 -> (nat -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a3 ->
    ('a1, ('a4, 'a3) prod) sigT) -> ('a1 list, (('a1, 'a4) coq_OnOne2i, ('a1,
    'a1, 'a3) coq_All2) prod) sigT **)

let rec coq_OnOne2i_impl_exist_and_All _ _ _ l3 h1 h2 h =
  match h1 with
  | OnOne2i_hd (i, hd, hd', tl, y) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let hh = h i hd a hd' y x in
          let Coq_existT (x1, p) = hh in
          let Coq_pair (r, r0) = p in
          Coq_existT ((Coq_cons (x1, tl)), (Coq_pair ((OnOne2i_hd (i, hd, x1,
          tl, r)), (All2_cons (a, x1, l, tl, r0, x0)))))))
  | OnOne2i_tl (i, hd, tl, tl', o) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let iHh1 = coq_OnOne2i_impl_exist_and_All (S i) tl tl' l o x0 h in
          let Coq_existT (x1, p) = iHh1 in
          let Coq_pair (o0, a0) = p in
          Coq_existT ((Coq_cons (hd, x1)), (Coq_pair ((OnOne2i_tl (i, hd, tl,
          x1, o0)), (All2_cons (a, hd, l, x1, x, a0)))))))

(** val coq_OnOne2i_impl_exist_and_All_r :
    nat -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i ->
    ('a1, 'a1, 'a3) coq_All2 -> (nat -> 'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a3 ->
    ('a1, ('a4, 'a3) prod) sigT) -> ('a1 list, (('a1, 'a4) coq_OnOne2i, ('a1,
    'a1, 'a3) coq_All2) prod) sigT **)

let rec coq_OnOne2i_impl_exist_and_All_r _ _ _ l3 h1 h2 h =
  match h1 with
  | OnOne2i_hd (i, hd, hd', tl, y) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let hh = h i hd a hd' y x in
          let Coq_existT (x1, p) = hh in
          let Coq_pair (r, r0) = p in
          Coq_existT ((Coq_cons (x1, tl)), (Coq_pair ((OnOne2i_hd (i, hd, x1,
          tl, r)), (All2_cons (x1, a, tl, l, r0, x0)))))))
  | OnOne2i_tl (i, hd, tl, tl', o) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let iHh1 = coq_OnOne2i_impl_exist_and_All_r (S i) tl tl' l o x0 h in
          let Coq_existT (x1, p) = iHh1 in
          let Coq_pair (o0, a0) = p in
          Coq_existT ((Coq_cons (hd, x1)), (Coq_pair ((OnOne2i_tl (i, hd, tl,
          x1, o0)), (All2_cons (hd, a, x1, l, x, a0)))))))

(** val coq_OnOne2i_split :
    nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> (nat, ('a1,
    ('a1, ('a1 list, ('a1 list, ('a2, __) prod) sigT) sigT) sigT) sigT) sigT **)

let rec coq_OnOne2i_split _ _ _ = function
| OnOne2i_hd (i, hd, hd', tl, y) ->
  Coq_existT (i, (Coq_existT (hd, (Coq_existT (hd', (Coq_existT (Coq_nil,
    (Coq_existT (tl, (Coq_pair (y, __)))))))))))
| OnOne2i_tl (i, hd, tl, tl', o0) ->
  let Coq_existT (x, s) = coq_OnOne2i_split (S i) tl tl' o0 in
  let Coq_existT (x0, s0) = s in
  let Coq_existT (x1, s1) = s0 in
  let Coq_existT (x2, s2) = s1 in
  let Coq_existT (x3, p) = s2 in
  Coq_existT (x, (Coq_existT (x0, (Coq_existT (x1, (Coq_existT ((Coq_cons
  (hd, x2)), (Coq_existT (x3,
  (let Coq_pair (a, _) = p in Coq_pair (a, __)))))))))))

(** val coq_OnOne2i_impl :
    nat -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_OnOne2i -> (nat -> 'a1 ->
    'a1 -> 'a2 -> 'a3) -> ('a1, 'a3) coq_OnOne2i **)

let rec coq_OnOne2i_impl _ _ _ o x =
  match o with
  | OnOne2i_hd (i, hd, hd', tl, y) ->
    OnOne2i_hd (i, hd, hd', tl, (x i hd hd' y))
  | OnOne2i_tl (i, hd, tl, tl', o0) ->
    OnOne2i_tl (i, hd, tl, tl', (coq_OnOne2i_impl (S i) tl tl' o0 x))

(** val coq_OnOne2i_nth_error :
    'a1 list -> 'a1 list -> nat -> nat -> 'a1 -> ('a1, 'a2) coq_OnOne2i ->
    ('a1, (__, (__, 'a2) sum) prod) sigT **)

let coq_OnOne2i_nth_error l l' i n t x =
  let rec f _ _ _ o n0 =
    match o with
    | OnOne2i_hd (_, _, hd', _, y) ->
      (fun _ ->
        match n0 with
        | O -> Coq_existT (hd', (Coq_pair (__, (Coq_inr y))))
        | S _ -> Coq_existT (t, (Coq_pair (__, (Coq_inl __)))))
    | OnOne2i_tl (i0, _, tl, tl', o0) ->
      (match n0 with
       | O -> (fun _ -> Coq_existT (t, (Coq_pair (__, (Coq_inl __)))))
       | S n1 -> f (S i0) tl tl' o0 n1)
  in f i l l' x n __

(** val coq_OnOne2i_nth_error_r :
    nat -> 'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_OnOne2i ->
    ('a1, (__, (__, 'a2) sum) prod) sigT **)

let coq_OnOne2i_nth_error_r i l l' n t' x =
  let rec f _ _ _ o n0 =
    match o with
    | OnOne2i_hd (_, hd, _, _, y) ->
      (fun _ ->
        match n0 with
        | O -> Coq_existT (hd, (Coq_pair (__, (Coq_inr y))))
        | S _ -> Coq_existT (t', (Coq_pair (__, (Coq_inl __)))))
    | OnOne2i_tl (i0, _, tl, tl', o0) ->
      (match n0 with
       | O -> (fun _ -> Coq_existT (t', (Coq_pair (__, (Coq_inl __)))))
       | S n1 -> f (S i0) tl tl' o0 n1)
  in f i l l' x n __

type ('a, 'b, 'p) coq_OnOne2All =
| OnOne2All_hd of 'b * 'b list * 'a * 'a * 'a list * 'p
| OnOne2All_tl of 'b * 'b list * 'a * 'a list * 'a list
   * ('a, 'b, 'p) coq_OnOne2All

(** val coq_OnOne2All_rect :
    ('a2 -> 'a2 list -> 'a1 -> 'a1 -> 'a1 list -> 'a3 -> __ -> 'a4) -> ('a2
    -> 'a2 list -> 'a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3)
    coq_OnOne2All -> 'a4 -> 'a4) -> 'a2 list -> 'a1 list -> 'a1 list -> ('a1,
    'a2, 'a3) coq_OnOne2All -> 'a4 **)

let rec coq_OnOne2All_rect f f0 _ _ _ = function
| OnOne2All_hd (b, bs, hd, hd', tl, y) -> f b bs hd hd' tl y __
| OnOne2All_tl (b, bs, hd, tl, tl', o0) ->
  f0 b bs hd tl tl' o0 (coq_OnOne2All_rect f f0 bs tl tl' o0)

(** val coq_OnOne2All_rec :
    ('a2 -> 'a2 list -> 'a1 -> 'a1 -> 'a1 list -> 'a3 -> __ -> 'a4) -> ('a2
    -> 'a2 list -> 'a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3)
    coq_OnOne2All -> 'a4 -> 'a4) -> 'a2 list -> 'a1 list -> 'a1 list -> ('a1,
    'a2, 'a3) coq_OnOne2All -> 'a4 **)

let rec coq_OnOne2All_rec f f0 _ _ _ = function
| OnOne2All_hd (b, bs, hd, hd', tl, y) -> f b bs hd hd' tl y __
| OnOne2All_tl (b, bs, hd, tl, tl', o0) ->
  f0 b bs hd tl tl' o0 (coq_OnOne2All_rec f f0 bs tl tl' o0)

type ('a, 'b, 'p) coq_OnOne2All_sig = ('a, 'b, 'p) coq_OnOne2All

(** val coq_OnOne2All_sig_pack :
    'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All -> ('a2
    list * ('a1 list * 'a1 list)) * ('a1, 'a2, 'a3) coq_OnOne2All **)

let coq_OnOne2All_sig_pack x x0 x1 onOne2All_var =
  (x,(x0,x1)),onOne2All_var

(** val coq_OnOne2All_Signature :
    'a2 list -> 'a1 list -> 'a1 list -> (('a1, 'a2, 'a3) coq_OnOne2All, 'a2
    list * ('a1 list * 'a1 list), ('a1, 'a2, 'a3) coq_OnOne2All_sig)
    coq_Signature **)

let coq_OnOne2All_Signature x x0 x1 onOne2All_var =
  (x,(x0,x1)),onOne2All_var

(** val coq_NoConfusionPackage_OnOne2All :
    (('a2 list * ('a1 list * 'a1 list)) * ('a1, 'a2, 'a3) coq_OnOne2All)
    coq_NoConfusionPackage **)

let coq_NoConfusionPackage_OnOne2All =
  Build_NoConfusionPackage

(** val coq_OnOne2All_All_mix_left :
    'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a4) coq_All -> ('a1, 'a2, 'a3)
    coq_OnOne2All -> ('a1, 'a2, ('a3, 'a4) prod) coq_OnOne2All **)

let rec coq_OnOne2All_All_mix_left _ _ _ h = function
| OnOne2All_hd (b, bs, hd, hd', tl, y) ->
  OnOne2All_hd (b, bs, hd, hd', tl,
    (match h with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x0, _) -> Coq_pair (y, x0)))
| OnOne2All_tl (b, bs, hd, tl, tl', o) ->
  OnOne2All_tl (b, bs, hd, tl, tl',
    (match h with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, _, x0) -> coq_OnOne2All_All_mix_left bs tl tl' x0 o))

(** val coq_OnOne2All_All2_mix_left :
    'a2 list -> 'a1 list -> 'a1 list -> ('a2, 'a1, 'a4) coq_All2 -> ('a1,
    'a2, 'a3) coq_OnOne2All -> ('a1, 'a2, ('a3, 'a4) prod) coq_OnOne2All **)

let rec coq_OnOne2All_All2_mix_left _ _ _ a = function
| OnOne2All_hd (b, bs, hd, hd', tl, y) ->
  OnOne2All_hd (b, bs, hd, hd', tl,
    (match a with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, _, _, _, x0, _) -> Coq_pair (y, x0)))
| OnOne2All_tl (b, bs, hd, tl, tl', o) ->
  OnOne2All_tl (b, bs, hd, tl, tl',
    (match a with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, _, _, _, _, x0) ->
       coq_OnOne2All_All2_mix_left bs tl tl' x0 o))

(** val coq_OnOne2All_app :
    'a2 list -> 'a2 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2,
    'a3) coq_OnOne2All -> ('a1, 'a2, 'a3) coq_OnOne2All **)

let rec coq_OnOne2All_app i i' l tl tl' x =
  match l with
  | Coq_nil ->
    (match i' with
     | Coq_nil -> x
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | Coq_cons (y, l0) ->
    (match i' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (b, l1) ->
       OnOne2All_tl (b, (app l1 i), y, (app l0 tl), (app l0 tl'),
         (coq_OnOne2All_app i l1 l0 tl tl' x)))

(** val coq_OnOne2All_mapP :
    'a3 list -> 'a1 list -> 'a1 list -> ('a1 -> 'a2) -> ('a1, 'a3, __)
    coq_OnOne2All -> ('a2, 'a3, __) coq_OnOne2All **)

let rec coq_OnOne2All_mapP _ _ _ f = function
| OnOne2All_hd (b, bs, hd, hd', tl, _) ->
  OnOne2All_hd (b, bs, (f hd), (f hd'), (map f tl), __)
| OnOne2All_tl (b, bs, hd, tl, tl', o) ->
  OnOne2All_tl (b, bs, (f hd), (map f tl), (map f tl'),
    (coq_OnOne2All_mapP bs tl tl' f o))

(** val coq_OnOne2All_map :
    'a2 list -> 'a1 list -> 'a1 list -> ('a1 -> 'a3) -> ('a1, 'a2, ('a3, 'a1,
    'a4) on_Trel) coq_OnOne2All -> ('a3, 'a2, 'a4) coq_OnOne2All **)

let rec coq_OnOne2All_map _ _ _ f = function
| OnOne2All_hd (b, bs, hd, hd', tl, y) ->
  OnOne2All_hd (b, bs, (f hd), (f hd'), (map f tl), y)
| OnOne2All_tl (b, bs, hd, tl, tl', o) ->
  OnOne2All_tl (b, bs, (f hd), (map f tl), (map f tl'),
    (coq_OnOne2All_map bs tl tl' f o))

(** val coq_OnOne2All_map_all :
    'a3 list -> 'a1 list -> 'a1 list -> ('a3 -> 'a4) -> ('a1 -> 'a2) -> ('a1,
    'a3, ('a2, 'a1, 'a5) on_Trel) coq_OnOne2All -> ('a2, 'a4, 'a5)
    coq_OnOne2All **)

let rec coq_OnOne2All_map_all _ _ _ g f = function
| OnOne2All_hd (b, bs, hd, hd', tl, y) ->
  OnOne2All_hd ((g b), (map g bs), (f hd), (f hd'), (map f tl), y)
| OnOne2All_tl (b, bs, hd, tl, tl', o) ->
  OnOne2All_tl ((g b), (map g bs), (f hd), (map f tl), (map f tl'),
    (coq_OnOne2All_map_all bs tl tl' g f o))

(** val coq_OnOne2All_sym :
    'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All ->
    ('a1, 'a2, 'a3) coq_OnOne2All **)

let rec coq_OnOne2All_sym _ _ _ = function
| OnOne2All_hd (b, bs, hd, hd', tl, y) -> OnOne2All_hd (b, bs, hd', hd, tl, y)
| OnOne2All_tl (b, bs, hd, tl, tl', o) ->
  OnOne2All_tl (b, bs, hd, tl', tl, (coq_OnOne2All_sym bs tl' tl o))

(** val coq_OnOne2All_exist :
    'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All -> ('a2
    -> 'a1 -> 'a1 -> 'a3 -> ('a1, ('a4, 'a4) prod) sigT) -> ('a1 list, (('a1,
    'a2, 'a4) coq_OnOne2All, ('a1, 'a2, 'a4) coq_OnOne2All) prod) sigT **)

let rec coq_OnOne2All_exist _ _ _ h hPQ =
  match h with
  | OnOne2All_hd (b, bs, hd, hd', tl, y) ->
    let s = hPQ b hd hd' y in
    let Coq_existT (x, p) = s in
    let Coq_pair (q, q0) = p in
    Coq_existT ((Coq_cons (x, tl)), (Coq_pair ((OnOne2All_hd (b, bs, hd, x,
    tl, q)), (OnOne2All_hd (b, bs, hd', x, tl, q0)))))
  | OnOne2All_tl (b, bs, hd, tl, tl', o) ->
    let Coq_existT (x, p) = coq_OnOne2All_exist bs tl tl' o hPQ in
    let Coq_pair (o0, o1) = p in
    Coq_existT ((Coq_cons (hd, x)), (Coq_pair ((OnOne2All_tl (b, bs, hd, tl,
    x, o0)), (OnOne2All_tl (b, bs, hd, tl', x, o1)))))

(** val coq_OnOne2All_ind_l :
    ('a1 list -> 'a2 -> 'a2 list -> 'a1 -> 'a1 -> 'a1 list -> 'a3 -> __ ->
    'a4) -> ('a1 list -> 'a2 -> 'a2 list -> 'a1 -> 'a1 list -> 'a1 list ->
    ('a1, 'a2, 'a3) coq_OnOne2All -> 'a4 -> 'a4) -> 'a2 list -> 'a1 list ->
    'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All -> 'a4 **)

let coq_OnOne2All_ind_l hhd htl i l l' h =
  let rec f _ _ _ = function
  | OnOne2All_hd (b, bs, hd, hd', tl, y) -> hhd l b bs hd hd' tl y __
  | OnOne2All_tl (b, bs, hd, tl, tl', o0) ->
    htl l b bs hd tl tl' o0 (f bs tl tl' o0)
  in f i l l' h

(** val coq_OnOne2All_impl_exist_and_All :
    'a2 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3)
    coq_OnOne2All -> ('a1, 'a1, 'a4) coq_All2 -> ('a2 -> 'a1 -> 'a1 -> 'a1 ->
    'a3 -> 'a4 -> ('a1, ('a5, 'a4) prod) sigT) -> ('a1 list, (('a1, 'a2, 'a5)
    coq_OnOne2All, ('a1, 'a1, 'a4) coq_All2) prod) sigT **)

let rec coq_OnOne2All_impl_exist_and_All _ _ _ l3 h1 h2 h =
  match h1 with
  | OnOne2All_hd (b, bs, hd, hd', tl, y) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let hh = h b hd a hd' y x in
          let Coq_existT (x1, p) = hh in
          let Coq_pair (r, r0) = p in
          Coq_existT ((Coq_cons (x1, tl)), (Coq_pair ((OnOne2All_hd (b, bs,
          hd, x1, tl, r)), (All2_cons (a, x1, l, tl, r0, x0)))))))
  | OnOne2All_tl (b, bs, hd, tl, tl', o) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let iHh1 = coq_OnOne2All_impl_exist_and_All bs tl tl' l o x0 h in
          let Coq_existT (x1, p) = iHh1 in
          let Coq_pair (o0, a0) = p in
          Coq_existT ((Coq_cons (hd, x1)), (Coq_pair ((OnOne2All_tl (b, bs,
          hd, tl, x1, o0)), (All2_cons (a, hd, l, x1, x, a0)))))))

(** val coq_OnOne2All_impl_exist_and_All_r :
    'a2 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3)
    coq_OnOne2All -> ('a1, 'a1, 'a4) coq_All2 -> ('a2 -> 'a1 -> 'a1 -> 'a1 ->
    'a3 -> 'a4 -> ('a1, ('a5, 'a4) prod) sigT) -> ('a1 list, (('a1, 'a2, 'a5)
    coq_OnOne2All, ('a1, 'a1, 'a4) coq_All2) prod) sigT **)

let rec coq_OnOne2All_impl_exist_and_All_r _ _ _ l3 h1 h2 h =
  match h1 with
  | OnOne2All_hd (b, bs, hd, hd', tl, y) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let hh = h b hd a hd' y x in
          let Coq_existT (x1, p) = hh in
          let Coq_pair (r, r0) = p in
          Coq_existT ((Coq_cons (x1, tl)), (Coq_pair ((OnOne2All_hd (b, bs,
          hd, x1, tl, r)), (All2_cons (x1, a, tl, l, r0, x0)))))))
  | OnOne2All_tl (b, bs, hd, tl, tl', o) ->
    (match l3 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       (match h2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x, x0) ->
          let iHh1 = coq_OnOne2All_impl_exist_and_All_r bs tl tl' l o x0 h in
          let Coq_existT (x1, p) = iHh1 in
          let Coq_pair (o0, a0) = p in
          Coq_existT ((Coq_cons (hd, x1)), (Coq_pair ((OnOne2All_tl (b, bs,
          hd, tl, x1, o0)), (All2_cons (hd, a, x1, l, x, a0)))))))

(** val coq_OnOne2All_split :
    'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All ->
    ('a2, ('a1, ('a1, ('a1 list, ('a1 list, ('a3, __) prod) sigT) sigT) sigT)
    sigT) sigT **)

let rec coq_OnOne2All_split _ _ _ = function
| OnOne2All_hd (b, _, hd, hd', tl, y) ->
  Coq_existT (b, (Coq_existT (hd, (Coq_existT (hd', (Coq_existT (Coq_nil,
    (Coq_existT (tl, (Coq_pair (y, __)))))))))))
| OnOne2All_tl (_, bs, hd, tl, tl', o0) ->
  let Coq_existT (x, s) = coq_OnOne2All_split bs tl tl' o0 in
  let Coq_existT (x0, s0) = s in
  let Coq_existT (x1, s1) = s0 in
  let Coq_existT (x2, s2) = s1 in
  let Coq_existT (x3, p) = s2 in
  Coq_existT (x, (Coq_existT (x0, (Coq_existT (x1, (Coq_existT ((Coq_cons
  (hd, x2)), (Coq_existT (x3,
  (let Coq_pair (a, _) = p in Coq_pair (a, __)))))))))))

(** val coq_OnOne2All_impl :
    'a2 list -> 'a1 list -> 'a1 list -> ('a1, 'a2, 'a3) coq_OnOne2All -> ('a2
    -> 'a1 -> 'a1 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a4) coq_OnOne2All **)

let rec coq_OnOne2All_impl _ _ _ o x =
  match o with
  | OnOne2All_hd (b, bs, hd, hd', tl, y) ->
    OnOne2All_hd (b, bs, hd, hd', tl, (x b hd hd' y))
  | OnOne2All_tl (b, bs, hd, tl, tl', o0) ->
    OnOne2All_tl (b, bs, hd, tl, tl', (coq_OnOne2All_impl bs tl tl' o0 x))

(** val coq_OnOne2All_nth_error :
    'a2 list -> 'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2, 'a3)
    coq_OnOne2All -> ('a1, (__, (__, ('a2, (__, 'a3) prod) sigT) sum) prod)
    sigT **)

let rec coq_OnOne2All_nth_error _ _ _ n t = function
| OnOne2All_hd (b, _, _, hd', _, y) ->
  (match n with
   | O ->
     Coq_existT (hd', (Coq_pair (__, (Coq_inr (Coq_existT (b, (Coq_pair (__,
       y))))))))
   | S _ -> Coq_existT (t, (Coq_pair (__, (Coq_inl __)))))
| OnOne2All_tl (_, bs, _, tl, tl', o) ->
  (match n with
   | O -> Coq_existT (t, (Coq_pair (__, (Coq_inl __))))
   | S n0 -> coq_OnOne2All_nth_error bs tl tl' n0 t o)

(** val coq_OnOne2All_nth_error_r :
    'a2 list -> 'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a2, 'a3)
    coq_OnOne2All -> ('a1, (__, (__, ('a2, (__, 'a3) prod) sigT) sum) prod)
    sigT **)

let rec coq_OnOne2All_nth_error_r _ _ _ n t' = function
| OnOne2All_hd (b, _, hd, _, _, y) ->
  (match n with
   | O ->
     Coq_existT (hd, (Coq_pair (__, (Coq_inr (Coq_existT (b, (Coq_pair (__,
       y))))))))
   | S _ -> Coq_existT (t', (Coq_pair (__, (Coq_inl __)))))
| OnOne2All_tl (_, bs, _, tl, tl', o) ->
  (match n with
   | O -> Coq_existT (t', (Coq_pair (__, (Coq_inl __))))
   | S n0 -> coq_OnOne2All_nth_error_r bs tl tl' n0 t' o)

(** val coq_OnOne2All_impl_All_r :
    'a2 list -> 'a1 list -> 'a1 list -> ('a2 -> 'a1 -> 'a1 -> 'a4 -> 'a3 ->
    'a4) -> ('a1, 'a2, 'a3) coq_OnOne2All -> ('a1, 'a4) coq_All -> ('a1, 'a4)
    coq_All **)

let rec coq_OnOne2All_impl_All_r _ _ _ hPQ x h =
  match x with
  | OnOne2All_hd (b, _, hd, hd', tl, y) ->
    let h0 = (Coq_cons (hd, tl)),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, q, a) -> All_cons (hd', tl, (hPQ b hd hd' q y), a))
  | OnOne2All_tl (_, bs, hd, tl, tl', o) ->
    let h0 = (Coq_cons (hd, tl)),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, q, a) ->
       All_cons (hd, tl', q, (coq_OnOne2All_impl_All_r bs tl tl' hPQ o a)))

(** val coq_OnOne2All_nth_error_impl :
    'a1 list -> 'a2 list -> 'a2 list -> ('a2, 'a1, 'a3) coq_OnOne2All ->
    ('a2, 'a1, ((nat, __) sigT, 'a3) prod) coq_OnOne2All **)

let rec coq_OnOne2All_nth_error_impl _ _ _ = function
| OnOne2All_hd (b, bs, hd, hd', tl, y) ->
  OnOne2All_hd (b, bs, hd, hd', tl, (Coq_pair ((Coq_existT (O, __)), y)))
| OnOne2All_tl (b, bs, hd, tl, tl', o0) ->
  OnOne2All_tl (b, bs, hd, tl, tl',
    (coq_OnOne2All_impl bs tl tl' (coq_OnOne2All_nth_error_impl bs tl tl' o0)
      (fun _ _ _ x0 ->
      let Coq_pair (s, p) = x0 in
      let Coq_existT (x, _) = s in Coq_pair ((Coq_existT ((S x), __)), p))))

(** val coq_Forall2_All2 : 'a1 list -> 'a2 list -> ('a1, 'a2, __) coq_All2 **)

let rec coq_Forall2_All2 l l' =
  match l with
  | Coq_nil ->
    (match l' with
     | Coq_nil -> All2_nil
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | Coq_cons (y, l0) ->
    (match l' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (b, l1) ->
       All2_cons (y, b, l0, l1, __, (coq_Forall2_All2 l0 l1)))

(** val coq_All2_map_left_equiv :
    'a2 list -> 'a3 list -> ('a2 -> 'a1) -> (('a2, 'a3, 'a4) coq_All2, ('a1,
    'a3, 'a4) coq_All2) iffT **)

let coq_All2_map_left_equiv l l' f =
  coq_All2_map_equiv f (fun y -> y) l l'

(** val coq_All2_map_right_equiv :
    'a1 list -> 'a2 list -> ('a2 -> 'a3) -> (('a1, 'a2, 'a4) coq_All2, ('a1,
    'a3, 'a4) coq_All2) iffT **)

let coq_All2_map_right_equiv l l' f =
  coq_All2_map_equiv (fun x -> x) f l l'

(** val coq_All2_map_left :
    'a2 list -> 'a3 list -> ('a2 -> 'a1) -> ('a2, 'a3, 'a4) coq_All2 -> ('a1,
    'a3, 'a4) coq_All2 **)

let coq_All2_map_left l l' f =
  let Coq_pair (x, _) = coq_All2_map_left_equiv l l' f in x

(** val coq_All2_map_right :
    'a1 list -> 'a2 list -> ('a2 -> 'a3) -> ('a1, 'a2, 'a4) coq_All2 -> ('a1,
    'a3, 'a4) coq_All2 **)

let coq_All2_map_right l l' f =
  let Coq_pair (x, _) = coq_All2_map_right_equiv l l' f in x

(** val coq_All2_map_left_inv :
    'a2 list -> 'a3 list -> ('a2 -> 'a1) -> ('a1, 'a3, 'a4) coq_All2 -> ('a2,
    'a3, 'a4) coq_All2 **)

let coq_All2_map_left_inv l l' f =
  snd (coq_All2_map_left_equiv l l' f)

(** val coq_All2_map_right_inv :
    'a1 list -> 'a2 list -> ('a2 -> 'a3) -> ('a1, 'a3, 'a4) coq_All2 -> ('a1,
    'a2, 'a4) coq_All2 **)

let coq_All2_map_right_inv l l' f =
  snd (coq_All2_map_right_equiv l l' f)

(** val coq_All2_undep :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> (('a1, 'a2, 'a4)
    coq_All2, ('a1, 'a2, 'a3, 'a4) coq_All2_dep) iffT **)

let coq_All2_undep l l' a =
  Coq_pair
    ((let rec f _ _ a0 x =
        match a0 with
        | All2_nil ->
          (match x with
           | All2_nil -> All2_dep_nil
           | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
        | All2_cons (x0, y, l0, l'0, y0, a1) ->
          (match x with
           | All2_nil -> assert false (* absurd case *)
           | All2_cons (_, _, _, _, x1, x2) ->
             All2_dep_cons (x0, y, l0, l'0, y0, a1, x1, (f l0 l'0 a1 x2)))
      in f l l' a), (fun x ->
    let rec f _ _ _ = function
    | All2_dep_nil -> All2_nil
    | All2_dep_cons (x0, y, l0, l'0, _, rs, y0, a1) ->
      All2_cons (x0, y, l0, l'0, y0, (f l0 l'0 rs a1))
    in f l l' a x))

(** val coq_All2_All2_mix :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a4)
    coq_All2 -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2 **)

let rec coq_All2_All2_mix _ _ a h =
  match a with
  | All2_nil ->
    let h0 = (Coq_nil,Coq_nil),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_nil -> All2_nil
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2_cons (x, y, l, l', y0, a0) ->
    let h0 = ((Coq_cons (x, l)),(Coq_cons (y, l'))),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, _, _, _, q, a1) ->
       All2_cons (x, y, l, l', (Coq_pair (y0, q)),
         (coq_All2_All2_mix l l' a0 a1)))

(** val coq_All2_mix :
    'a1 list -> 'a1 list -> ('a1, 'a1, 'a2) coq_All2 -> ('a1, 'a1, 'a3)
    coq_All2 -> ('a1, 'a1, ('a2, 'a3) prod) coq_All2 **)

let rec coq_All2_mix _ _ a hQ =
  match a with
  | All2_nil ->
    (match hQ with
     | All2_nil -> All2_nil
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2_cons (x, y, l, l', y0, a0) ->
    (match hQ with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, _, _, _, x0, x1) ->
       All2_cons (x, y, l, l', (Coq_pair (y0, x0)), (coq_All2_mix l l' a0 x1)))

(** val coq_All2_mix_inv :
    'a1 list -> 'a1 list -> ('a1, 'a1, ('a2, 'a3) prod) coq_All2 -> (('a1,
    'a1, 'a2) coq_All2, ('a1, 'a1, 'a3) coq_All2) prod **)

let rec coq_All2_mix_inv _ _ = function
| All2_nil -> Coq_pair (All2_nil, All2_nil)
| All2_cons (x, y, l, l', y0, a0) ->
  let iHX = coq_All2_mix_inv l l' a0 in
  Coq_pair ((All2_cons (x, y, l, l', (let Coq_pair (a1, _) = y0 in a1),
  (let Coq_pair (a1, _) = iHX in a1))), (All2_cons (x, y, l, l',
  (let Coq_pair (_, b) = y0 in b), (let Coq_pair (_, b) = iHX in b))))

(** val coq_All_safe_nth : 'a1 list -> nat -> ('a1, 'a2) coq_All -> 'a2 **)

let rec coq_All_safe_nth _ n = function
| All_nil -> assert false (* absurd case *)
| All_cons (_, l, y, a) ->
  (match n with
   | O -> y
   | S n0 -> coq_All_safe_nth l n0 a)

type size = nat

(** val all_size :
    ('a1 -> 'a2 -> size) -> 'a1 list -> ('a1, 'a2) coq_All -> size **)

let rec all_size fn _ = function
| All_nil -> O
| All_cons (x, l, px, pl) -> add (fn x px) (all_size fn l pl)

(** val alli_size :
    (nat -> 'a1 -> 'a2 -> size) -> 'a1 list -> nat -> ('a1, 'a2) coq_Alli ->
    size **)

let rec alli_size fn _ n = function
| Alli_nil -> O
| Alli_cons (hd, tl, px, pl) -> add (fn n hd px) (alli_size fn tl (S n) pl)

(** val all2_size :
    ('a1 -> 'a2 -> 'a3 -> size) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
    coq_All2 -> size **)

let rec all2_size fn _ _ = function
| All2_nil -> O
| All2_cons (x, y, l, l', rxy, rll') ->
  add (fn x y rxy) (all2_size fn l l' rll')

(** val all2i_size :
    (nat -> 'a1 -> 'a2 -> 'a3 -> size) -> nat -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) coq_All2i -> size **)

let rec all2i_size fn n _ _ = function
| All2i_nil -> O
| All2i_cons (x, y, l, r, rxy, rll') ->
  add (fn n x y rxy) (all2i_size fn (S n) l r rll')

(** val coq_All2i_impl :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> (nat -> 'a1
    -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a4) coq_All2i **)

let rec coq_All2i_impl n _ _ ha h =
  match ha with
  | All2i_nil -> All2i_nil
  | All2i_cons (x, y, l, r, y0, a) ->
    All2i_cons (x, y, l, r, (h n x y y0), (coq_All2i_impl (S n) l r a h))

(** val nth_error_all :
    'a1 list -> nat -> 'a1 -> ('a1, 'a2) coq_All -> 'a2 **)

let rec nth_error_all l n x hPl =
  match l with
  | Coq_nil -> assert false (* absurd case *)
  | Coq_cons (_, l0) ->
    (match n with
     | O ->
       (match hPl with
        | All_nil -> assert false (* absurd case *)
        | All_cons (_, _, x0, _) -> x0)
     | S n0 ->
       nth_error_all l0 n0 x
         (match hPl with
          | All_nil -> assert false (* absurd case *)
          | All_cons (_, _, _, x0) -> x0))

(** val nth_error_alli :
    'a1 list -> nat -> 'a1 -> nat -> ('a1, 'a2) coq_Alli -> 'a2 **)

let rec nth_error_alli _ n x k = function
| Alli_nil -> assert false (* absurd case *)
| Alli_cons (_, tl, y, a) ->
  (match n with
   | O -> y
   | S n0 -> nth_error_alli tl n0 x (S k) a)

(** val map_option_Some :
    'a1 option list -> 'a1 list -> ('a1 option, 'a1, __) coq_All2 **)

let rec map_option_Some l _ =
  match l with
  | Coq_nil -> All2_nil
  | Coq_cons (y, l0) ->
    (match y with
     | Some x ->
       let o = map_option_out l0 in
       (match o with
        | Some l1 ->
          All2_cons ((Some x), x, l0, l1, __, (map_option_Some l0 l1))
        | None -> assert false (* absurd case *))
     | None -> assert false (* absurd case *))

(** val coq_All_mapi :
    (nat -> 'a1 -> 'a2) -> 'a1 list -> nat -> ('a1, 'a3) coq_Alli -> ('a2,
    'a3) coq_All **)

let rec coq_All_mapi f _ k = function
| Alli_nil -> All_nil
| Alli_cons (hd, tl, y, a) ->
  All_cons ((f k hd), (mapi_rec f tl (S k)), y, (coq_All_mapi f tl (S k) a))

(** val coq_All_Alli :
    'a1 list -> nat -> ('a1, 'a2) coq_All -> (nat -> 'a1 -> 'a2 -> 'a3) ->
    ('a1, 'a3) coq_Alli **)

let rec coq_All_Alli _ n h x =
  match h with
  | All_nil -> Alli_nil
  | All_cons (x0, l, y, a) ->
    Alli_cons (x0, l, (x n x0 y), (coq_All_Alli l (S n) a x))

(** val coq_All2_All_left_pack :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, ('a2, (__, 'a3)
    prod) sigT) coq_Alli **)

let rec coq_All2_All_left_pack _ _ = function
| All2_nil -> Alli_nil
| All2_cons (x, y, l, l', y0, a0) ->
  Alli_cons (x, l, (Coq_existT (y, (Coq_pair (__, y0)))),
    (coq_Alli_shift O l (coq_All2_All_left_pack l l' a0)))

(** val map_option_out_All :
    'a1 option list -> 'a1 list -> ('a1 option, __) coq_All -> ('a1, __)
    coq_All **)

let rec map_option_out_All _ _ = function
| All_nil -> All_nil
| All_cons (x0, l, _, a) ->
  (match x0 with
   | Some a0 ->
     (match map_option_out l with
      | Some l0 -> All_cons (a0, l0, __, (map_option_out_All l l0 a))
      | None -> assert false (* absurd case *))
   | None -> assert false (* absurd case *))

(** val coq_All2_app_inv_l :
    'a1 list -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a2
    list, ('a2 list, (__, (('a1, 'a2, 'a3) coq_All2, ('a1, 'a2, 'a3)
    coq_All2) prod) prod) sigT) sigT **)

let rec coq_All2_app_inv_l l l2 r x =
  match l with
  | Coq_nil ->
    Coq_existT (Coq_nil, (Coq_existT (r, (Coq_pair (__, (Coq_pair (All2_nil,
      x)))))))
  | Coq_cons (y, l0) ->
    let x0 = ((Coq_cons (y, (app l0 l2))),r),x in
    let x2 = let _,pr2 = x0 in pr2 in
    (match x2 with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, y0, _, l', r0, a) ->
       let x1 = coq_All2_app_inv_l l0 l2 l' a in
       let Coq_existT (x3, s) = x1 in
       let Coq_existT (x4, p) = s in
       let Coq_pair (_, p0) = p in
       let Coq_pair (a0, a1) = p0 in
       Coq_existT ((Coq_cons (y0, x3)), (Coq_existT (x4, (Coq_pair (__,
       (Coq_pair ((All2_cons (y, y0, l0, x3, r0, a0)), a1))))))))

(** val coq_All2_app_inv_r :
    'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1
    list, ('a1 list, (__, (('a1, 'a2, 'a3) coq_All2, ('a1, 'a2, 'a3)
    coq_All2) prod) prod) sigT) sigT **)

let rec coq_All2_app_inv_r l r1 r2 h =
  match r1 with
  | Coq_nil ->
    Coq_existT (Coq_nil, (Coq_existT (l, (Coq_pair (__, (Coq_pair (All2_nil,
      h)))))))
  | Coq_cons (y, l0) ->
    let h0 = (l,(Coq_cons (y, (app l0 r2)))),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (x, _, l1, _, r, a) ->
       let h1 = coq_All2_app_inv_r l1 l0 r2 a in
       let Coq_existT (x0, s) = h1 in
       let Coq_existT (x1, p) = s in
       let Coq_pair (_, p0) = p in
       let Coq_pair (a0, a1) = p0 in
       Coq_existT ((Coq_cons (x, x0)), (Coq_existT (x1, (Coq_pair (__,
       (Coq_pair ((All2_cons (x, y, x0, l0, r, a0)), a1))))))))

(** val coq_All2_app_inv :
    'a1 list -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2
    -> (('a1, 'a2, 'a3) coq_All2, ('a1, 'a2, 'a3) coq_All2) prod **)

let coq_All2_app_inv l1 l2 r1 r2 h =
  let h0 = coq_All2_app_inv_l l1 l2 (app r1 r2) h in
  let Coq_existT (_, s) = h0 in
  let Coq_existT (_, p) = s in let Coq_pair (_, p0) = p in p0

(** val coq_All2_rect_rev :
    'a4 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
    coq_All2 -> 'a4 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
    coq_All2 -> 'a4 **)

let coq_All2_rect_rev x x0 l l0 a =
  rev_ind (fun _ a0 ->
    match a0 with
    | All2_nil -> x
    | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
    (fun x1 l1 iHl l2 a0 ->
    let a1 = coq_All2_app_inv_l l1 (Coq_cons (x1, Coq_nil)) l2 a0 in
    let Coq_existT (x2, s) = a1 in
    let Coq_existT (_, p) = s in
    let Coq_pair (_, p0) = p in
    let Coq_pair (a2, a3) = p0 in
    (match a3 with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, y, _, _, x3, x4) ->
       (match x4 with
        | All2_nil -> x0 x1 y l1 x2 x3 a2 (iHl x2 a2)
        | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *)))) l
    l0 a

(** val coq_All2_app :
    'a1 list -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2
    -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3) coq_All2 **)

let rec coq_All2_app _ l2 _ l2' x x0 =
  match x with
  | All2_nil -> x0
  | All2_cons (x1, y, l, l', y0, a) ->
    All2_cons (x1, y, (app l l2), (app l' l2'), y0,
      (coq_All2_app l l2 l' l2' a x0))

(** val coq_All2_rev :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a3)
    coq_All2 **)

let rec coq_All2_rev _ _ = function
| All2_nil -> All2_nil
| All2_cons (x, y, l, l', y0, a0) ->
  coq_All2_app (List.rev l) (Coq_cons (x, Coq_nil)) (List.rev l') (Coq_cons
    (y, Coq_nil)) (coq_All2_rev l l' a0) (All2_cons (x, y, Coq_nil, Coq_nil,
    y0, All2_nil))

(** val coq_All_All2_flex :
    'a1 list -> 'a2 list -> ('a1, 'a3) coq_All -> ('a1 -> 'a2 -> __ -> 'a3 ->
    'a4) -> ('a1, 'a2, 'a4) coq_All2 **)

let rec coq_All_All2_flex _ l' h1 h2 =
  match h1 with
  | All_nil ->
    (match l' with
     | Coq_nil -> All2_nil
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | All_cons (x, l, y, a) ->
    (match l' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (b, l0) ->
       All2_cons (x, b, l, l0, (h2 x b __ y),
         (coq_All_All2_flex l l0 a (fun x0 y0 _ x1 -> h2 x0 y0 __ x1))))

(** val coq_All_All_All2 :
    'a1 list -> 'a1 list -> ('a1, __) coq_All -> ('a1, __) coq_All -> ('a1,
    'a1, __) coq_All2 **)

let coq_All_All_All2 l l' x x0 =
  let rec f l0 l'0 x1 x2 =
    match l0 with
    | Coq_nil ->
      (fun _ ->
        match l'0 with
        | Coq_nil -> All2_nil
        | Coq_cons (_, _) -> assert false (* absurd case *))
    | Coq_cons (y, l1) ->
      (match l'0 with
       | Coq_nil -> (fun _ -> assert false (* absurd case *))
       | Coq_cons (a, l2) ->
         let iHl = f l1 l2 in
         let ha0 = (Coq_cons (y, l1)),x1 in
         let ha2 = let _,pr2 = ha0 in pr2 in
         (match ha2 with
          | All_nil -> assert false (* absurd case *)
          | All_cons (_, _, _, a0) ->
            let hb0 = (Coq_cons (a, l2)),x2 in
            let hb2 = let _,pr2 = hb0 in pr2 in
            (fun _ ->
            match hb2 with
            | All_nil -> assert false (* absurd case *)
            | All_cons (_, _, _, a1) ->
              All2_cons (y, a, l1, l2, __, (iHl a0 a1 __)))))
  in f l l' x x0 __

(** val coq_All2_impl_In :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1 -> 'a2 -> __ ->
    __ -> 'a3 -> 'a4) -> ('a1, 'a2, 'a4) coq_All2 **)

let rec coq_All2_impl_In l _ x x0 =
  match l with
  | Coq_nil ->
    (match x with
     | All2_nil -> All2_nil
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | Coq_cons (y, l0) ->
    (match x with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, y0, _, l', x1, x2) ->
       All2_cons (y, y0, l0, l', (x0 y y0 __ __ x1),
         (coq_All2_impl_In l0 l' x2 (fun x3 y1 _ _ x4 -> x0 x3 y1 __ __ x4))))

(** val coq_All2_All :
    'a1 list -> ('a1, 'a1, 'a2) coq_All2 -> ('a1, 'a2) coq_All **)

let rec coq_All2_All l x =
  match l with
  | Coq_nil -> All_nil
  | Coq_cons (y, l0) ->
    (match x with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, _, _, _, x0, x1) ->
       All_cons (y, l0, x0, (coq_All2_All l0 x1)))

(** val coq_All2_trans :
    ('a1, 'a2) coq_Transitive -> ('a1 list, ('a1, 'a1, 'a2) coq_All2)
    coq_Transitive **)

let rec coq_All2_trans hP _ _ _ h hyz =
  match h with
  | All2_nil ->
    (match hyz with
     | All2_nil -> All2_nil
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2_cons (x, y, l, l', y0, a) ->
    (match hyz with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, y1, _, l'0, x0, x1) ->
       All2_cons (x, y1, l, l'0, (transitivity hP x y y1 y0 x0),
         (coq_All2_trans hP l l' l'0 a x1)))

(** val coq_All2_trans' :
    ('a1 -> 'a2 -> 'a3 -> ('a4, 'a5) prod -> 'a6) -> 'a1 list -> 'a2 list ->
    'a3 list -> ('a1, 'a2, 'a4) coq_All2 -> ('a2, 'a3, 'a5) coq_All2 -> ('a1,
    'a3, 'a6) coq_All2 **)

let rec coq_All2_trans' h _ _ _ x x0 =
  match x with
  | All2_nil ->
    (match x0 with
     | All2_nil -> All2_nil
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2_cons (x1, y, l, l', y0, a) ->
    (match x0 with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, y1, _, l'0, x2, x3) ->
       All2_cons (x1, y1, l, l'0, (h x1 y y1 (Coq_pair (y0, x2))),
         (coq_All2_trans' h l l' l'0 a x3)))

(** val coq_All2_nth :
    'a1 list -> 'a2 list -> nat -> 'a1 -> 'a2 -> ('a1, 'a2, 'a3) coq_All2 ->
    'a3 -> 'a3 **)

let rec coq_All2_nth _ _ n d d' h hd =
  match n with
  | O -> (match h with
          | All2_nil -> hd
          | All2_cons (_, _, _, _, p, _) -> p)
  | S n0 ->
    (match h with
     | All2_nil -> hd
     | All2_cons (_, _, l, l', _, a) -> coq_All2_nth l l' n0 d d' a hd)

(** val coq_All2_mapi :
    (nat -> 'a1 -> 'a3) -> (nat -> 'a2 -> 'a4) -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, nat -> 'a5) coq_All2 -> ('a3, 'a4, 'a5) coq_All2 **)

let coq_All2_mapi f g l l' h =
  let i = O in
  let rec f0 _ _ a i0 =
    match a with
    | All2_nil -> All2_nil
    | All2_cons (x, y, l0, l'0, y0, a0) ->
      All2_cons ((f i0 x), (g i0 y), (mapi_rec f l0 (S i0)),
        (mapi_rec g l'0 (S i0)), (y0 i0), (f0 l0 l'0 a0 (S i0)))
  in f0 l l' h i

(** val coq_All2_skipn :
    'a1 list -> 'a2 list -> nat -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2,
    'a3) coq_All2 **)

let rec coq_All2_skipn _ _ n = function
| All2_nil -> All2_nil
| All2_cons (x, y, l, l', y0, a) ->
  (match n with
   | O -> All2_cons (x, y, l, l', y0, a)
   | S n0 -> coq_All2_skipn l l' n0 a)

(** val coq_All2_right_triv :
    'a1 list -> 'a2 list -> ('a2, 'a3) coq_All -> ('a1, 'a2, 'a3) coq_All2 **)

let rec coq_All2_right_triv l _ = function
| All_nil ->
  (match l with
   | Coq_nil -> All2_nil
   | Coq_cons (_, _) -> assert false (* absurd case *))
| All_cons (x0, l0, y, a) ->
  (match l with
   | Coq_nil -> assert false (* absurd case *)
   | Coq_cons (a0, l1) ->
     All2_cons (a0, x0, l1, l0, y, (coq_All2_right_triv l1 l0 a)))

(** val coq_All_repeat : nat -> 'a1 -> 'a2 -> ('a1, 'a2) coq_All **)

let rec coq_All_repeat n x x0 =
  match n with
  | O -> All_nil
  | S n0 -> All_cons (x, (repeat x n0), x0, (coq_All_repeat n0 x x0))

(** val coq_All2_from_nth_error :
    'a1 list -> 'a2 list -> (nat -> 'a1 -> 'a2 -> __ -> __ -> __ -> 'a3) ->
    ('a1, 'a2, 'a3) coq_All2 **)

let rec coq_All2_from_nth_error l l2 x =
  match l with
  | Coq_nil ->
    (match l2 with
     | Coq_nil -> All2_nil
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | Coq_cons (y, l0) ->
    (match l2 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (b, l1) ->
       All2_cons (y, b, l0, l1, (x O y b __ __ __),
         (coq_All2_from_nth_error l0 l1 (fun n x1 x2 _ _ _ ->
           x (S n) x1 x2 __ __ __))))

(** val coq_All2_nth_error :
    'a1 list -> 'a2 list -> nat -> 'a1 -> 'a2 -> ('a1, 'a2, 'a3) coq_All2 ->
    'a3 **)

let rec coq_All2_nth_error _ _ n t t' = function
| All2_nil -> assert false (* absurd case *)
| All2_cons (_, _, l, l', y, a) ->
  (match n with
   | O -> y
   | S n0 -> coq_All2_nth_error l l' n0 t t' a)

(** val coq_All2_dep_from_nth_error :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> (nat -> 'a1 -> 'a2 ->
    __ -> __ -> __ -> 'a4) -> ('a1, 'a2, 'a3, 'a4) coq_All2_dep **)

let rec coq_All2_dep_from_nth_error _ _ a h' =
  match a with
  | All2_nil -> All2_dep_nil
  | All2_cons (x, y, l, l', y0, a0) ->
    All2_dep_cons (x, y, l, l', y0, a0, (h' O x y __ __ __),
      (coq_All2_dep_from_nth_error l l' a0 (fun n x1 x2 _ _ _ ->
        h' (S n) x1 x2 __ __ __)))

(** val coq_All2_dep_nth_error :
    'a1 list -> 'a2 list -> nat -> 'a1 -> 'a2 -> ('a1, 'a2, 'a3) coq_All2 ->
    ('a1, 'a2, 'a3, 'a4) coq_All2_dep -> 'a4 **)

let coq_All2_dep_nth_error l l' n t t' h h' =
  let rec f _ _ _ a0 n0 =
    match a0 with
    | All2_dep_nil -> (fun _ _ -> assert false (* absurd case *))
    | All2_dep_cons (x, y, l0, l'0, r, rs, y0, a) ->
      (match n0 with
       | O ->
         (fun _ _ ->
           internal_eq_rew_r_dep x t (fun r0 r1 ->
             internal_eq_rew_r_dep y t' (fun _ r2 -> r2) r0 r1) r y0)
       | S n1 -> f l0 l'0 rs a n1)
  in f l l' h h' n __ __

(** val coq_All2_swap :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a2, 'a1, 'a3)
    coq_All2 **)

let rec coq_All2_swap _ _ = function
| All2_nil -> All2_nil
| All2_cons (x, y, l, l', y0, a0) ->
  All2_cons (y, x, l', l, y0, (coq_All2_swap l l' a0))

(** val coq_All2_firstn :
    'a1 list -> 'a2 list -> nat -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2,
    'a3) coq_All2 **)

let rec coq_All2_firstn _ _ n = function
| All2_nil -> All2_nil
| All2_cons (x, y, l, l', y0, a) ->
  (match n with
   | O -> All2_nil
   | S n0 ->
     All2_cons (x, y,
       (let rec firstn n1 l0 =
          match n1 with
          | O -> Coq_nil
          | S n2 ->
            (match l0 with
             | Coq_nil -> Coq_nil
             | Coq_cons (a0, l1) -> Coq_cons (a0, (firstn n2 l1)))
        in firstn n0 l),
       (let rec firstn n1 l0 =
          match n1 with
          | O -> Coq_nil
          | S n2 ->
            (match l0 with
             | Coq_nil -> Coq_nil
             | Coq_cons (a0, l1) -> Coq_cons (a0, (firstn n2 l1)))
        in firstn n0 l'), y0, (coq_All2_firstn l l' n0 a)))

(** val coq_All2_impl' :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2 -> 'a3 ->
    'a4) coq_All -> ('a1, 'a2, 'a4) coq_All2 **)

let rec coq_All2_impl' _ _ a x =
  match a with
  | All2_nil -> All2_nil
  | All2_cons (x0, y, l, l', y0, a0) ->
    (match x with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x1, x2) ->
       All2_cons (x0, y, l, l', (x1 y y0), (coq_All2_impl' l l' a0 x2)))

(** val coq_All_All2 :
    'a1 list -> ('a1, 'a3) coq_All -> ('a1 -> 'a3 -> 'a2) -> ('a1, 'a1, 'a2)
    coq_All2 **)

let rec coq_All_All2 _ a x =
  match a with
  | All_nil -> All2_nil
  | All_cons (x0, l, y, a0) ->
    All2_cons (x0, x0, l, l, (x x0 y), (coq_All_All2 l a0 x))

(** val coq_All2_nth_error_Some :
    'a1 list -> 'a2 list -> nat -> 'a1 -> ('a1, 'a2, 'a3) coq_All2 -> ('a2,
    (__, 'a3) prod) sigT **)

let rec coq_All2_nth_error_Some _ _ n t = function
| All2_nil -> assert false (* absurd case *)
| All2_cons (_, y, l, l', y0, a) ->
  (match n with
   | O -> Coq_existT (y, (Coq_pair (__, y0)))
   | S n0 -> coq_All2_nth_error_Some l l' n0 t a)

(** val coq_All2_nth_error_Some_r :
    'a1 list -> 'a2 list -> nat -> 'a2 -> ('a1, 'a2, 'a3) coq_All2 -> ('a1,
    (__, 'a3) prod) sigT **)

let rec coq_All2_nth_error_Some_r _ _ n t' = function
| All2_nil -> assert false (* absurd case *)
| All2_cons (x, _, l, l', y, a) ->
  (match n with
   | O -> Coq_existT (x, (Coq_pair (__, y)))
   | S n0 -> coq_All2_nth_error_Some_r l l' n0 t' a)

(** val coq_All2_same :
    'a1 list -> ('a1 -> 'a2) -> ('a1, 'a1, 'a2) coq_All2 **)

let rec coq_All2_same l x =
  match l with
  | Coq_nil -> All2_nil
  | Coq_cons (y, l0) -> All2_cons (y, y, l0, l0, (x y), (coq_All2_same l0 x))

(** val coq_All2_prod :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2 -> ('a1, 'a2, 'a4)
    coq_All2 -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2 **)

let rec coq_All2_prod _ _ a x =
  match a with
  | All2_nil ->
    (match x with
     | All2_nil -> All2_nil
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2_cons (x0, y, l, l', y0, a0) ->
    (match x with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, _, _, _, x1, x2) ->
       All2_cons (x0, y, l, l', (Coq_pair (y0, x1)),
         (coq_All2_prod l l' a0 x2)))

(** val coq_All2_prod_inv :
    'a1 list -> 'a2 list -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2 -> (('a1,
    'a2, 'a3) coq_All2, ('a1, 'a2, 'a4) coq_All2) prod **)

let rec coq_All2_prod_inv _ _ = function
| All2_nil -> Coq_pair (All2_nil, All2_nil)
| All2_cons (x, y, l, l', y0, a0) ->
  let Coq_pair (a1, a2) = coq_All2_prod_inv l l' a0 in
  let Coq_pair (p, q) = y0 in
  Coq_pair ((All2_cons (x, y, l, l', p, a1)), (All2_cons (x, y, l, l', q,
  a2)))

(** val coq_All2_sym :
    'a1 list -> 'a1 list -> ('a1, 'a1, 'a2) coq_All2 -> ('a1, 'a1, 'a2)
    coq_All2 **)

let rec coq_All2_sym _ _ = function
| All2_nil -> All2_nil
| All2_cons (x, y, l, l', y0, a0) ->
  All2_cons (y, x, l', l, y0, (coq_All2_sym l l' a0))

(** val coq_All2_symP :
    ('a1, 'a2) coq_Symmetric -> ('a1 list, ('a1, 'a1, 'a2) coq_All2)
    coq_Symmetric **)

let rec coq_All2_symP hP _ _ = function
| All2_nil -> All2_nil
| All2_cons (x, y, l, l', y0, a) ->
  All2_cons (y, x, l', l, (hP x y y0), (coq_All2_symP hP l l' a))

(** val coq_All_All2_All2_mix :
    'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2 -> 'a2 -> 'a4 -> 'a5 ->
    ('a2, ('a3, 'a3) prod) sigT) coq_All -> ('a1, 'a2, 'a4) coq_All2 -> ('a1,
    'a2, 'a5) coq_All2 -> ('a2 list, (('a2, 'a2, 'a3) coq_All2, ('a2, 'a2,
    'a3) coq_All2) prod) sigT **)

let rec coq_All_All2_All2_mix _ _ _ h h' h'' =
  match h with
  | All_nil ->
    (match h' with
     | All2_nil ->
       (match h'' with
        | All2_nil -> Coq_existT (Coq_nil, (Coq_pair (All2_nil, All2_nil)))
        | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All_cons (_, l, y, a) ->
    (match h' with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, y0, _, l', x, x0) ->
       (match h'' with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, y1, _, l'0, x1, x2) ->
          let s = coq_All_All2_All2_mix l l' l'0 a x0 x2 in
          let Coq_existT (x3, p) = s in
          let Coq_pair (a0, a1) = p in
          let s0 = y y0 y1 x x1 in
          let Coq_existT (x4, p0) = s0 in
          let Coq_pair (p1, p2) = p0 in
          Coq_existT ((Coq_cons (x4, x3)), (Coq_pair ((All2_cons (y0, x4, l',
          x3, p1, a0)), (All2_cons (y1, x4, l'0, x3, p2, a1)))))))

(** val coq_All2_nth_error_Some_right :
    'a1 list -> 'a1 list -> nat -> 'a1 -> ('a1, 'a1, 'a2) coq_All2 -> ('a1,
    (__, 'a2) prod) sigT **)

let rec coq_All2_nth_error_Some_right _ _ n t = function
| All2_nil -> assert false (* absurd case *)
| All2_cons (x, _, l, l', y, a) ->
  (match n with
   | O -> Coq_existT (x, (Coq_pair (__, y)))
   | S n0 -> coq_All2_nth_error_Some_right l l' n0 t a)

(** val forallb_nth' : 'a1 list -> ('a1 -> bool) -> nat -> 'a1 -> sumbool **)

let forallb_nth' l _ n _ =
  let s = le_lt_dec (length l) n in
  (match s with
   | Coq_left -> Coq_right
   | Coq_right -> Coq_left)

(** val coq_All_prod_inv :
    'a1 list -> ('a1, ('a2, 'a3) prod) coq_All -> (('a1, 'a2) coq_All, ('a1,
    'a3) coq_All) prod **)

let rec coq_All_prod_inv _ = function
| All_nil -> Coq_pair (All_nil, All_nil)
| All_cons (x, l, y, a0) ->
  let Coq_pair (a1, a2) = coq_All_prod_inv l a0 in
  let Coq_pair (p, q) = y in
  Coq_pair ((All_cons (x, l, p, a1)), (All_cons (x, l, q, a2)))

(** val coq_All_pair :
    'a1 list -> (('a1, ('a2, 'a3) prod) coq_All, (('a1, 'a2) coq_All, ('a1,
    'a3) coq_All) prod) iffT **)

let coq_All_pair l =
  Coq_pair ((fun x ->
    let rec f _ = function
    | All_nil -> Coq_pair (All_nil, All_nil)
    | All_cons (x0, l0, y, a0) ->
      let Coq_pair (a1, b) = y in
      let Coq_pair (a2, b0) = f l0 a0 in
      Coq_pair ((All_cons (x0, l0, a1, a2)), (All_cons (x0, l0, b, b0)))
    in f l x), (fun __top_assumption_ ->
    let _evar_0_ = fun hl hl' ->
      let rec f _ a hl'0 =
        match a with
        | All_nil ->
          let hl'1 = Coq_nil,hl'0 in
          let hl'2 = let _,pr2 = hl'1 in pr2 in
          (match hl'2 with
           | All_nil -> All_nil
           | All_cons (_, _, _, _) -> assert false (* absurd case *))
        | All_cons (x, l0, y, a0) ->
          let hl'1 = (Coq_cons (x, l0)),hl'0 in
          let hl'2 = let _,pr2 = hl'1 in pr2 in
          (match hl'2 with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, q, a1) ->
             let x0 = f l0 a0 a1 in All_cons (x, l0, (Coq_pair (y, q)), x0))
      in f l hl hl'
    in
    let Coq_pair (a, b) = __top_assumption_ in _evar_0_ a b))

(** val coq_All_prod :
    'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a3) coq_All -> ('a1, ('a2, 'a3)
    prod) coq_All **)

let rec coq_All_prod _ a h2 =
  match a with
  | All_nil -> All_nil
  | All_cons (x, l, y, a0) ->
    (match h2 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, x0, x1) ->
       let iHh1 = coq_All_prod l a0 x1 in
       All_cons (x, l, (Coq_pair (y, x0)), iHh1))

(** val coq_All2i_mapi :
    (nat -> 'a1 -> 'a3) -> (nat -> 'a2 -> 'a4) -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a5) coq_All2i -> ('a3, 'a4, 'a5) coq_All2i **)

let coq_All2i_mapi f g l l' h =
  let n = O in
  let rec f0 n0 _ _ = function
  | All2i_nil -> All2i_nil
  | All2i_cons (x, y, l0, r, y0, a0) ->
    All2i_cons ((f n0 x), (g n0 y), (mapi_rec f l0 (S n0)),
      (mapi_rec g r (S n0)), y0, (f0 (S n0) l0 r a0))
  in f0 n l l' h

(** val coq_All2i_app :
    nat -> 'a1 list -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3)
    coq_All2i -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2, 'a3) coq_All2i **)

let rec coq_All2i_app n _ l2 _ r2 h1 h2 =
  match h1 with
  | All2i_nil -> h2
  | All2i_cons (x, y, l, r, y0, a) ->
    All2i_cons (x, y, (app l l2), (app r r2), y0,
      (coq_All2i_app (S n) l l2 r r2 a h2))

(** val coq_All2i_mapi_rec :
    'a3 list -> 'a4 list -> (nat -> 'a3 -> 'a1) -> (nat -> 'a4 -> 'a2) -> nat
    -> ('a3, 'a4, 'a5) coq_All2i -> ('a1, 'a2, 'a5) coq_All2i **)

let rec coq_All2i_mapi_rec _ _ f g n = function
| All2i_nil -> All2i_nil
| All2i_cons (x0, y, l, r, y0, a) ->
  All2i_cons ((f n x0), (g n y),
    (let rec mapi_rec0 f0 l0 n0 =
       match l0 with
       | Coq_nil -> Coq_nil
       | Coq_cons (hd, tl) -> Coq_cons ((f0 n0 hd), (mapi_rec0 f0 tl (S n0)))
     in mapi_rec0 f l (S n)),
    (let rec mapi_rec0 f0 l0 n0 =
       match l0 with
       | Coq_nil -> Coq_nil
       | Coq_cons (hd, tl) -> Coq_cons ((f0 n0 hd), (mapi_rec0 f0 tl (S n0)))
     in mapi_rec0 g r (S n)), y0, (coq_All2i_mapi_rec l r f g (S n) a))

(** val coq_All2i_trivial :
    (nat -> 'a1 -> 'a2 -> 'a3) -> nat -> 'a1 list -> 'a2 list -> ('a1, 'a2,
    'a3) coq_All2i **)

let rec coq_All2i_trivial h n l l' =
  match l with
  | Coq_nil ->
    (match l' with
     | Coq_nil -> All2i_nil
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | Coq_cons (y, l0) ->
    (match l' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (b, l1) ->
       All2i_cons (y, b, l0, l1, (h n y b), (coq_All2i_trivial h (S n) l0 l1)))

(** val coq_All2i_rev :
    'a1 list -> 'a2 list -> nat -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2,
    'a3) coq_All2i **)

let rec coq_All2i_rev _ _ n = function
| All2i_nil -> All2i_nil
| All2i_cons (x, y, l, r, y0, a) ->
  coq_All2i_app O (List.rev l) (Coq_cons (x, Coq_nil)) (List.rev r) (Coq_cons
    (y, Coq_nil))
    (coq_All2i_impl O (List.rev l) (List.rev r) (coq_All2i_rev l r (S n) a)
      (fun _ _ _ x0 -> x0)) (All2i_cons (x, y, Coq_nil, Coq_nil, y0,
    All2i_nil))

type ('a, 'b, 'r) coq_All2i_len =
| All2i_len_nil
| All2i_len_cons of 'a * 'b * 'a list * 'b list * 'r
   * ('a, 'b, 'r) coq_All2i_len

(** val coq_All2i_len_rect :
    'a4 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
    coq_All2i_len -> 'a4 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
    coq_All2i_len -> 'a4 **)

let rec coq_All2i_len_rect f f0 _ _ = function
| All2i_len_nil -> f
| All2i_len_cons (x, y, l, l', y0, a0) ->
  f0 x y l l' y0 a0 (coq_All2i_len_rect f f0 l l' a0)

(** val coq_All2i_len_rec :
    'a4 -> ('a1 -> 'a2 -> 'a1 list -> 'a2 list -> 'a3 -> ('a1, 'a2, 'a3)
    coq_All2i_len -> 'a4 -> 'a4) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3)
    coq_All2i_len -> 'a4 **)

let rec coq_All2i_len_rec f f0 _ _ = function
| All2i_len_nil -> f
| All2i_len_cons (x, y, l, l', y0, a0) ->
  f0 x y l l' y0 a0 (coq_All2i_len_rec f f0 l l' a0)

(** val coq_All2i_len_app :
    'a1 list -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3)
    coq_All2i_len -> ('a1, 'a2, 'a3) coq_All2i_len -> ('a1, 'a2, 'a3)
    coq_All2i_len **)

let rec coq_All2i_len_app _ l0' _ l1' h = function
| All2i_len_nil -> h
| All2i_len_cons (x0, y, l, l', y0, a) ->
  All2i_len_cons (x0, y, (app l l0'), (app l' l1'), y0,
    (coq_All2i_len_app l l0' l' l1' h a))

(** val coq_All2i_len_impl :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i_len -> (nat -> 'a1 ->
    'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a4) coq_All2i_len **)

let rec coq_All2i_len_impl _ _ a x =
  match a with
  | All2i_len_nil -> All2i_len_nil
  | All2i_len_cons (x0, y, l, l', y0, a0) ->
    All2i_len_cons (x0, y, l, l', (x (length l) x0 y y0),
      (coq_All2i_len_impl l l' a0 x))

(** val coq_All2i_len_rev :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i_len -> ('a1, 'a2, 'a3)
    coq_All2i_len **)

let rec coq_All2i_len_rev _ _ = function
| All2i_len_nil -> All2i_len_nil
| All2i_len_cons (x, y, l, l', y0, a0) ->
  coq_All2i_len_app (List.rev l) (Coq_cons (x, Coq_nil)) (List.rev l')
    (Coq_cons (y, Coq_nil)) (All2i_len_cons (x, y, Coq_nil, Coq_nil, y0,
    All2i_len_nil))
    (coq_All2i_len_impl (List.rev l) (List.rev l')
      (coq_All2i_len_rev l l' a0) (fun _ _ _ x0 -> x0))

(** val coq_All2i_rev_ctx :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i_len -> ('a1,
    'a2, 'a3) coq_All2i **)

let rec coq_All2i_rev_ctx n _ _ = function
| All2i_len_nil -> All2i_nil
| All2i_len_cons (x0, y, l, l', y0, a) ->
  coq_All2i_app O (List.rev l) (Coq_cons (x0, Coq_nil)) (List.rev l')
    (Coq_cons (y, Coq_nil)) (coq_All2i_rev_ctx n l l' a) (All2i_cons (x0, y,
    Coq_nil, Coq_nil, y0, All2i_nil))

(** val coq_All2i_rev_ctx_gen :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2,
    'a3) coq_All2i_len **)

let rec coq_All2i_rev_ctx_gen n _ _ = function
| All2i_nil -> All2i_len_nil
| All2i_cons (x, y, l, r, y0, a0) ->
  coq_All2i_len_app (List.rev l) (Coq_cons (x, Coq_nil)) (List.rev r)
    (Coq_cons (y, Coq_nil)) (All2i_len_cons (x, y, Coq_nil, Coq_nil, y0,
    All2i_len_nil))
    (coq_All2i_len_impl (List.rev l) (List.rev r)
      (coq_All2i_rev_ctx_gen (S n) l r a0) (fun _ _ _ x0 -> x0))

(** val coq_All2i_rev_ctx_inv :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2, 'a3)
    coq_All2i_len **)

let coq_All2i_rev_ctx_inv l l' x =
  coq_All2i_rev_ctx_gen O l l' x

(** val coq_All_All2_refl :
    'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a1, 'a2) coq_All2 **)

let rec coq_All_All2_refl _ = function
| All_nil -> All2_nil
| All_cons (x, l, y, a0) ->
  All2_cons (x, x, l, l, y, (coq_All_All2_refl l a0))

(** val coq_All2_app_r :
    'a1 list -> 'a1 list -> 'a1 -> 'a1 -> ('a1, 'a1, 'a2) coq_All2 -> (('a1,
    'a1, 'a2) coq_All2, 'a2) prod **)

let rec coq_All2_app_r l l' r r' x =
  match l with
  | Coq_nil ->
    (match l' with
     | Coq_nil ->
       (match x with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x0, x1) -> Coq_pair (x1, x0))
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | Coq_cons (y, l0) ->
    (match l' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l1) ->
       (match x with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, x0, x1) ->
          let x2 = coq_All2_app_r l0 l1 r r' x1 in
          Coq_pair ((All2_cons (y, a, l0, l1, x0,
          (let Coq_pair (a0, _) = x2 in a0))),
          (let Coq_pair (_, b) = x2 in b))))

(** val forallb2P :
    ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> ('a1 -> 'a2 -> reflect)
    -> reflect **)

let forallb2P p l l' _ =
  iff_reflect (forallb2 p l l')

(** val coq_All_forall :
    'a1 list -> ('a1, __) coq_All -> 'a2 -> ('a1, __) coq_All **)

let rec coq_All_forall _ x b =
  match x with
  | All_nil -> All_nil
  | All_cons (x0, l, _, a) -> All_cons (x0, l, __, (coq_All_forall l a b))

(** val coq_All2i_map :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> nat -> 'a1 list -> 'a2 list -> ('a1, 'a2,
    'a5) coq_All2i -> ('a3, 'a4, 'a5) coq_All2i **)

let rec coq_All2i_map f g n _ _ = function
| All2i_nil -> All2i_nil
| All2i_cons (x0, y, l, r, y0, a) ->
  All2i_cons ((f x0), (g y), (map f l), (map g r), y0,
    (coq_All2i_map f g (S n) l r a))

(** val coq_All2i_map_right :
    ('a1 -> 'a3) -> nat -> 'a2 list -> 'a1 list -> ('a2, 'a1, 'a4) coq_All2i
    -> ('a2, 'a3, 'a4) coq_All2i **)

let rec coq_All2i_map_right g n _ _ = function
| All2i_nil -> All2i_nil
| All2i_cons (x0, y, l, r, y0, a) ->
  All2i_cons (x0, (g y), l, (map g r), y0,
    (coq_All2i_map_right g (S n) l r a))

(** val coq_All2i_nth_impl_gen :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2,
    (__, 'a3) prod) coq_All2i **)

let rec coq_All2i_nth_impl_gen n _ _ = function
| All2i_nil -> All2i_nil
| All2i_cons (x, y, l, r, y0, a0) ->
  All2i_cons (x, y, l, r,
    (let b = PeanoNat.Nat.ltb n n in
     match b with
     | Coq_true -> assert false (* absurd case *)
     | Coq_false -> Coq_pair (__, y0)),
    (coq_All2i_impl (S n) l r (coq_All2i_nth_impl_gen (S n) l r a0)
      (fun i _ _ x0 ->
      let b = PeanoNat.Nat.ltb i (S n) in
      (match b with
       | Coq_true -> assert false (* absurd case *)
       | Coq_false ->
         let Coq_pair (_, r0) = x0 in
         let b0 = PeanoNat.Nat.ltb i n in
         (match b0 with
          | Coq_true -> assert false (* absurd case *)
          | Coq_false -> Coq_pair (__, r0))))))

(** val coq_All2i_nth_hyp :
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i -> ('a1, 'a2, (__, 'a3)
    prod) coq_All2i **)

let coq_All2i_nth_hyp l l' a =
  let a0 = coq_All2i_nth_impl_gen O l l' a in
  coq_All2i_impl O l l' a0 (fun _ _ _ x -> x)

(** val coq_All2i_nth_error_l :
    'a1 list -> 'a2 list -> nat -> 'a1 -> nat -> ('a1, 'a2, 'a3) coq_All2i ->
    ('a2, (__, 'a3) prod) sigT **)

let rec coq_All2i_nth_error_l _ _ n x k = function
| All2i_nil -> assert false (* absurd case *)
| All2i_cons (_, y, l, r, y0, a) ->
  (match n with
   | O -> Coq_existT (y, (Coq_pair (__, y0)))
   | S n0 -> coq_All2i_nth_error_l l r n0 x (S k) a)

(** val coq_All2i_nth_error_r :
    'a1 list -> 'a2 list -> nat -> 'a2 -> nat -> ('a1, 'a2, 'a3) coq_All2i ->
    ('a1, (__, 'a3) prod) sigT **)

let rec coq_All2i_nth_error_r _ _ n x k = function
| All2i_nil -> assert false (* absurd case *)
| All2i_cons (x1, _, l, r, y, a) ->
  (match n with
   | O -> Coq_existT (x1, (Coq_pair (__, y)))
   | S n0 -> coq_All2i_nth_error_r l r n0 x (S k) a)

(** val coq_All2i_app_inv_l :
    nat -> 'a1 list -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i ->
    ('a2 list, ('a2 list, (__, (('a1, 'a2, 'a3) coq_All2i, ('a1, 'a2, 'a3)
    coq_All2i) prod) prod) sigT) sigT **)

let rec coq_All2i_app_inv_l n xs xs' l a =
  match xs with
  | Coq_nil ->
    Coq_existT (Coq_nil, (Coq_existT (l, (Coq_pair (__, (Coq_pair (All2i_nil,
      a)))))))
  | Coq_cons (y, l0) ->
    let a1 = (n,((Coq_cons (y, (app l0 xs'))),l)),a in
    let a3 = let _,pr2 = a1 in pr2 in
    (match a3 with
     | All2i_nil -> assert false (* absurd case *)
     | All2i_cons (_, y0, _, r, r0, a0) ->
       let a2 = coq_All2i_app_inv_l (S n) l0 xs' r a0 in
       let Coq_existT (x, s) = a2 in
       let Coq_existT (x0, p) = s in
       let Coq_pair (_, p0) = p in
       let Coq_pair (a4, a5) = p0 in
       Coq_existT ((Coq_cons (y0, x)), (Coq_existT (x0, (Coq_pair (__,
       (Coq_pair ((All2i_cons (y, y0, l0, x, r0, a4)), a5))))))))

(** val coq_All2i_app_inv_r :
    nat -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3) coq_All2i ->
    ('a1 list, ('a1 list, (__, (('a1, 'a2, 'a3) coq_All2i, ('a1, 'a2, 'a3)
    coq_All2i) prod) prod) sigT) sigT **)

let rec coq_All2i_app_inv_r n l ys ys' a =
  match ys with
  | Coq_nil ->
    Coq_existT (Coq_nil, (Coq_existT (l, (Coq_pair (__, (Coq_pair (All2i_nil,
      a)))))))
  | Coq_cons (y, l0) ->
    let a1 = (n,(l,(Coq_cons (y, (app l0 ys'))))),a in
    let a3 = let _,pr2 = a1 in pr2 in
    (match a3 with
     | All2i_nil -> assert false (* absurd case *)
     | All2i_cons (x, _, l1, _, r, a0) ->
       let a2 = coq_All2i_app_inv_r (S n) l1 l0 ys' a0 in
       let Coq_existT (x0, s) = a2 in
       let Coq_existT (x1, p) = s in
       let Coq_pair (_, p0) = p in
       let Coq_pair (a4, a5) = p0 in
       Coq_existT ((Coq_cons (x, x0)), (Coq_existT (x1, (Coq_pair (__,
       (Coq_pair ((All2i_cons (x, y, x0, l0, r, a4)), a5))))))))

(** val coq_All2i_app_inv :
    nat -> 'a1 list -> 'a1 list -> 'a2 list -> 'a2 list -> ('a1, 'a2, 'a3)
    coq_All2i -> (('a1, 'a2, 'a3) coq_All2i, ('a1, 'a2, 'a3) coq_All2i) prod **)

let coq_All2i_app_inv n xs xs' ys ys' a =
  let a0 = coq_All2i_app_inv_l n xs xs' (app ys ys') a in
  let Coq_existT (_, s) = a0 in
  let Coq_existT (_, p) = s in let Coq_pair (_, p0) = p in p0

(** val coq_All2i_All2_All2i_All2i :
    nat -> 'a1 list -> 'a2 list -> 'a3 list -> ('a1, 'a2, 'a4) coq_All2i ->
    ('a2, 'a3, 'a5) coq_All2 -> ('a1, 'a3, 'a6) coq_All2i -> (nat -> 'a1 ->
    'a2 -> 'a3 -> 'a4 -> 'a5 -> 'a6 -> 'a7) -> ('a1, 'a3, 'a7) coq_All2i **)

let rec coq_All2i_All2_All2i_All2i n _ _ l'' a b c h =
  match a with
  | All2i_nil ->
    let b0 = (Coq_nil,l''),b in
    let b2 = let _,pr2 = b0 in pr2 in
    (match b2 with
     | All2_nil ->
       let c0 = (n,(Coq_nil,Coq_nil)),c in
       let c2 = let _,pr2 = c0 in pr2 in
       (match c2 with
        | All2i_nil -> All2i_nil
        | All2i_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
     | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2i_cons (x, y, l, r, y0, a0) ->
    let b0 = ((Coq_cons (y, r)),l''),b in
    let b2 = let _,pr2 = b0 in pr2 in
    (match b2 with
     | All2_nil -> assert false (* absurd case *)
     | All2_cons (_, y1, _, l', q, a1) ->
       let c0 = (n,((Coq_cons (x, l)),(Coq_cons (y1, l')))),c in
       let c2 = let _,pr2 = c0 in pr2 in
       (match c2 with
        | All2i_nil -> assert false (* absurd case *)
        | All2i_cons (_, _, _, _, r0, a2) ->
          All2i_cons (x, y1, l, l', (h n x y y1 y0 q r0),
            (coq_All2i_All2_All2i_All2i (S n) l r l' a0 a1 a2 h))))

(** val coq_All2i_All2_All2 :
    nat -> 'a1 list -> 'a2 list -> 'a3 list -> ('a1, 'a2, 'a4) coq_All2i ->
    ('a2, 'a3, 'a5) coq_All2 -> (nat -> 'a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 ->
    'a6) -> ('a2, 'a3, 'a6) coq_All2 **)

let rec coq_All2i_All2_All2 n _ _ l'' x h =
  match x with
  | All2i_nil ->
    let h0 = (Coq_nil,l''),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (fun _ ->
    match h2 with
    | All2_nil -> All2_nil
    | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2i_cons (x0, y, l, r, y0, a) ->
    let h0 = ((Coq_cons (y, r)),l''),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (fun x1 ->
    match h2 with
    | All2_nil -> assert false (* absurd case *)
    | All2_cons (_, y1, _, l', q, a0) ->
      All2_cons (y, y1, r, l', (x1 n x0 y y1 y0 q),
        (coq_All2i_All2_All2 (S n) l r l' a a0 x1)))

type ('a, 'p) coq_All_fold =
| All_fold_nil
| All_fold_cons of 'a * 'a list * ('a, 'p) coq_All_fold * 'p

(** val coq_All_fold_rect :
    'a3 -> ('a1 -> 'a1 list -> ('a1, 'a2) coq_All_fold -> 'a3 -> 'a2 -> 'a3)
    -> 'a1 list -> ('a1, 'a2) coq_All_fold -> 'a3 **)

let rec coq_All_fold_rect f f0 _ = function
| All_fold_nil -> f
| All_fold_cons (d, _UU0393_, a0, y) ->
  f0 d _UU0393_ a0 (coq_All_fold_rect f f0 _UU0393_ a0) y

(** val coq_All_fold_rec :
    'a3 -> ('a1 -> 'a1 list -> ('a1, 'a2) coq_All_fold -> 'a3 -> 'a2 -> 'a3)
    -> 'a1 list -> ('a1, 'a2) coq_All_fold -> 'a3 **)

let rec coq_All_fold_rec f f0 _ = function
| All_fold_nil -> f
| All_fold_cons (d, _UU0393_, a0, y) ->
  f0 d _UU0393_ a0 (coq_All_fold_rec f f0 _UU0393_ a0) y

type ('a, 'p) coq_All_fold_sig = ('a, 'p) coq_All_fold

(** val coq_All_fold_sig_pack :
    'a1 list -> ('a1, 'a2) coq_All_fold -> 'a1 list * ('a1, 'a2) coq_All_fold **)

let coq_All_fold_sig_pack x all_fold_var =
  x,all_fold_var

(** val coq_All_fold_Signature :
    'a1 list -> (('a1, 'a2) coq_All_fold, 'a1 list, ('a1, 'a2)
    coq_All_fold_sig) coq_Signature **)

let coq_All_fold_Signature x all_fold_var =
  x,all_fold_var

(** val coq_NoConfusionHomPackage_All_fold :
    'a1 list -> ('a1, 'a2) coq_All_fold coq_NoConfusionPackage **)

let coq_NoConfusionHomPackage_All_fold _ =
  Build_NoConfusionPackage

type ('a, 'p) coq_All2_fold =
| All2_fold_nil
| All2_fold_cons of 'a * 'a * 'a list * 'a list * ('a, 'p) coq_All2_fold * 'p

(** val coq_All2_fold_rect :
    'a3 -> ('a1 -> 'a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
    'a3 -> 'a2 -> 'a3) -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
    'a3 **)

let rec coq_All2_fold_rect f f0 _ _ = function
| All2_fold_nil -> f
| All2_fold_cons (d, d', _UU0393_, _UU0393_', a0, y) ->
  f0 d d' _UU0393_ _UU0393_' a0
    (coq_All2_fold_rect f f0 _UU0393_ _UU0393_' a0) y

(** val coq_All2_fold_rec :
    'a3 -> ('a1 -> 'a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
    'a3 -> 'a2 -> 'a3) -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold ->
    'a3 **)

let rec coq_All2_fold_rec f f0 _ _ = function
| All2_fold_nil -> f
| All2_fold_cons (d, d', _UU0393_, _UU0393_', a0, y) ->
  f0 d d' _UU0393_ _UU0393_' a0
    (coq_All2_fold_rec f f0 _UU0393_ _UU0393_' a0) y

type ('a, 'p) coq_All2_fold_sig = ('a, 'p) coq_All2_fold

(** val coq_All2_fold_sig_pack :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1 list * 'a1
    list) * ('a1, 'a2) coq_All2_fold **)

let coq_All2_fold_sig_pack x x0 all2_fold_var =
  (x,x0),all2_fold_var

(** val coq_All2_fold_Signature :
    'a1 list -> 'a1 list -> (('a1, 'a2) coq_All2_fold, 'a1 list * 'a1 list,
    ('a1, 'a2) coq_All2_fold_sig) coq_Signature **)

let coq_All2_fold_Signature x x0 all2_fold_var =
  (x,x0),all2_fold_var

(** val coq_NoConfusionPackage_All2_fold :
    (('a1 list * 'a1 list) * ('a1, 'a2) coq_All2_fold) coq_NoConfusionPackage **)

let coq_NoConfusionPackage_All2_fold =
  Build_NoConfusionPackage

type ('a, 'b, 'p) coq_All_over = 'p

(** val coq_All2_fold_from_nth_error :
    'a1 list -> 'a1 list -> (nat -> 'a1 -> 'a1 -> __ -> __ -> __ -> 'a2) ->
    ('a1, 'a2) coq_All2_fold **)

let rec coq_All2_fold_from_nth_error l l2 x =
  match l with
  | Coq_nil ->
    (match l2 with
     | Coq_nil -> All2_fold_nil
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | Coq_cons (y, l0) ->
    (match l2 with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l1) ->
       All2_fold_cons (y, a, l0, l1,
         (coq_All2_fold_from_nth_error l0 l1 (fun n x1 x2 _ ->
           x (S n) x1 x2 __)), (x O y a __ __ __)))

(** val coq_All2_fold_app :
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold
    -> ('a1, ('a1, 'a1, 'a2) coq_All_over) coq_All2_fold -> ('a1, 'a2)
    coq_All2_fold **)

let rec coq_All2_fold_app _UU0393_ _ _UU0393_l _ x = function
| All2_fold_nil -> x
| All2_fold_cons (d, d', _UU0393_0, _UU0393_', a, y) ->
  All2_fold_cons (d, d', (app _UU0393_0 _UU0393_), (app _UU0393_' _UU0393_l),
    (coq_All2_fold_app _UU0393_ _UU0393_0 _UU0393_l _UU0393_' x a), y)

(** val coq_All2_fold_impl :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1 list -> 'a1 list
    -> 'a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1, 'a3) coq_All2_fold **)

let rec coq_All2_fold_impl _ _ a x =
  match a with
  | All2_fold_nil -> All2_fold_nil
  | All2_fold_cons (d, d', _UU0393_, _UU0393_', a0, y) ->
    All2_fold_cons (d, d', _UU0393_, _UU0393_',
      (coq_All2_fold_impl _UU0393_ _UU0393_' a0 x),
      (x _UU0393_ _UU0393_' d d' y))

(** val coq_All_fold_app_inv :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All_fold -> (('a1, 'a2)
    coq_All_fold, ('a1, 'a2) coq_All_fold) prod **)

let rec coq_All_fold_app_inv = function
| Coq_nil -> (fun _ x -> Coq_pair (x, All_fold_nil))
| Coq_cons (y, l0) ->
  let iH_UU0393_ = coq_All_fold_app_inv l0 in
  (fun _UU0394_ x -> Coq_pair
  ((let x0 = (Coq_cons (y, (app l0 _UU0394_))),x in
    let x2 = let _,pr2 = x0 in pr2 in
    (match x2 with
     | All_fold_nil -> assert false (* absurd case *)
     | All_fold_cons (_, _, a, _) ->
       let iH_UU0393_0 = iH_UU0393_ _UU0394_ in
       let x1 = iH_UU0393_0 a in let Coq_pair (a0, _) = x1 in a0)),
  (let x0 = (Coq_cons (y, (app l0 _UU0394_))),x in
   let x2 = let _,pr2 = x0 in pr2 in
   (match x2 with
    | All_fold_nil -> assert false (* absurd case *)
    | All_fold_cons (_, _, a, p) ->
      All_fold_cons (y, l0,
        (let iH_UU0393_0 = iH_UU0393_ _UU0394_ in
         let x1 = iH_UU0393_0 a in let Coq_pair (_, b) = x1 in b), p)))))

(** val coq_All2_fold_All_fold_mix_left :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1, 'a3)
    coq_All2_fold -> ('a1, ('a2, 'a3) prod) coq_All2_fold **)

let rec coq_All2_fold_All_fold_mix_left _ _UU0393_' x h =
  match x with
  | All_fold_nil ->
    let h0 = (Coq_nil,_UU0393_'),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_fold_nil -> All2_fold_nil
     | All2_fold_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All_fold_cons (d, _UU0393_, a, y) ->
    let h0 = ((Coq_cons (d, _UU0393_)),_UU0393_'),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_fold_nil -> assert false (* absurd case *)
     | All2_fold_cons (_, d', _, _UU0393_'0, a0, q) ->
       All2_fold_cons (d, d', _UU0393_, _UU0393_'0,
         (coq_All2_fold_All_fold_mix_left _UU0393_ _UU0393_'0 a a0),
         (Coq_pair (y, q))))

(** val coq_All2_fold_All_fold_mix_right :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1, 'a3)
    coq_All2_fold -> ('a1, ('a2, 'a3) prod) coq_All2_fold **)

let rec coq_All2_fold_All_fold_mix_right _UU0393_ _ x h =
  match x with
  | All_fold_nil ->
    let h0 = (_UU0393_,Coq_nil),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_fold_nil -> All2_fold_nil
     | All2_fold_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All_fold_cons (d, _UU0393_0, a, y) ->
    let h0 = (_UU0393_,(Coq_cons (d, _UU0393_0))),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_fold_nil -> assert false (* absurd case *)
     | All2_fold_cons (d0, _, _UU0393_1, _, a0, q) ->
       All2_fold_cons (d0, d, _UU0393_1, _UU0393_0,
         (coq_All2_fold_All_fold_mix_right _UU0393_1 _UU0393_0 a a0),
         (Coq_pair (y, q))))

(** val coq_All2_fold_All_fold_mix_left_inv :
    'a1 list -> 'a1 list -> ('a1, ('a2, 'a3) prod) coq_All2_fold -> (('a1,
    'a2) coq_All_fold, ('a1, 'a3) coq_All2_fold) prod **)

let rec coq_All2_fold_All_fold_mix_left_inv _ _ = function
| All2_fold_nil -> Coq_pair (All_fold_nil, All2_fold_nil)
| All2_fold_cons (d, d', _UU0393_, _UU0393_', a0, y) ->
  let iHX = coq_All2_fold_All_fold_mix_left_inv _UU0393_ _UU0393_' a0 in
  Coq_pair ((All_fold_cons (d, _UU0393_, (let Coq_pair (a1, _) = iHX in a1),
  (let Coq_pair (a1, _) = y in a1))), (All2_fold_cons (d, d', _UU0393_,
  _UU0393_', (let Coq_pair (_, b) = iHX in b),
  (let Coq_pair (_, b) = y in b))))

(** val coq_All2_fold_All_right :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a2)
    coq_All_fold **)

let rec coq_All2_fold_All_right _ _ = function
| All2_fold_nil -> All_fold_nil
| All2_fold_cons (_, d', _UU0393_, _UU0393_', a0, y) ->
  All_fold_cons (d', _UU0393_',
    (coq_All2_fold_All_right _UU0393_ _UU0393_' a0), y)

(** val coq_All2_fold_All_left :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a2)
    coq_All_fold **)

let rec coq_All2_fold_All_left _ _ = function
| All2_fold_nil -> All_fold_nil
| All2_fold_cons (d, _, _UU0393_, _UU0393_', a0, y) ->
  All_fold_cons (d, _UU0393_, (coq_All2_fold_All_left _UU0393_ _UU0393_' a0),
    y)

(** val coq_All_fold_impl :
    'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1 list -> 'a1 -> 'a2 -> 'a3) ->
    ('a1, 'a3) coq_All_fold **)

let rec coq_All_fold_impl _ a x =
  match a with
  | All_fold_nil -> All_fold_nil
  | All_fold_cons (d, _UU0393_, a0, y) ->
    All_fold_cons (d, _UU0393_, (coq_All_fold_impl _UU0393_ a0 x),
      (x _UU0393_ d y))

(** val coq_All_fold_app :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1, 'a2)
    coq_All_fold -> ('a1, 'a2) coq_All_fold **)

let rec coq_All_fold_app _ _UU0394_ x x0 =
  match x with
  | All_fold_nil -> x0
  | All_fold_cons (d, _UU0393_, a, y) ->
    All_fold_cons (d, (app _UU0393_ _UU0394_),
      (coq_All_fold_app _UU0393_ _UU0394_ a x0), y)

(** val coq_Alli_All_fold :
    nat -> 'a1 list -> (('a1, 'a2) coq_Alli, ('a1, 'a2) coq_All_fold) iffT **)

let coq_Alli_All_fold n _UU0393_ =
  Coq_pair ((fun x ->
    let rec f n0 _ = function
    | Alli_nil -> All_fold_nil
    | Alli_cons (hd, tl, y, a0) ->
      coq_All_fold_app (List.rev tl) (Coq_cons (hd, Coq_nil))
        (coq_All_fold_impl (List.rev tl) (f (S n0) tl a0) (fun _ _ x0 -> x0))
        (All_fold_cons (hd, Coq_nil, All_fold_nil, y))
    in f n _UU0393_ x),
    (rev_ind (fun _ -> Alli_nil) (fun x _UU0393_0 iH_UU0393_ a ->
      let a0 = (Coq_cons (x, (List.rev _UU0393_0))),a in
      let a2 = let _,pr2 = a0 in pr2 in
      (match a2 with
       | All_fold_nil -> assert false (* absurd case *)
       | All_fold_cons (_, _, a1, p) ->
         coq_Alli_app_inv _UU0393_0 (Coq_cons (x, Coq_nil)) n (iH_UU0393_ a1)
           (Alli_cons (x, Coq_nil, p, Alli_nil)))) _UU0393_))

(** val coq_Alli_rev_All_fold :
    nat -> 'a1 list -> ('a1, 'a2) coq_Alli -> ('a1, 'a2) coq_All_fold **)

let coq_Alli_rev_All_fold n _UU0393_ _view_subject_ =
  fst (coq_Alli_All_fold n (List.rev _UU0393_)) _view_subject_

(** val coq_All_fold_Alli_rev :
    nat -> 'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1, 'a2) coq_Alli **)

let coq_All_fold_Alli_rev n _UU0393_ _view_subject_ =
  snd (coq_Alli_All_fold n (List.rev _UU0393_)) _view_subject_

(** val coq_All2_fold_All2 :
    'a1 list -> 'a1 list -> (('a1, 'a2) coq_All2_fold, ('a1, 'a1, 'a2)
    coq_All2) iffT **)

let coq_All2_fold_All2 _UU0393_ _UU0394_ =
  Coq_pair ((fun x ->
    let rec f _ _ = function
    | All2_fold_nil -> All2_nil
    | All2_fold_cons (d, d', _UU0393_0, _UU0393_', a0, y) ->
      All2_cons (d, d', _UU0393_0, _UU0393_', y, (f _UU0393_0 _UU0393_' a0))
    in f _UU0393_ _UU0394_ x), (fun x ->
    let rec f _ _ = function
    | All2_nil -> All2_fold_nil
    | All2_cons (x0, y, l, l', y0, a0) ->
      All2_fold_cons (x0, y, l, l', (f l l' a0), y0)
    in f _UU0393_ _UU0394_ x))

(** val coq_All2_fold_refl :
    ('a1 list -> 'a1 -> 'a2) -> 'a1 list -> ('a1, 'a2) coq_All2_fold **)

let rec coq_All2_fold_refl hP = function
| Coq_nil -> All2_fold_nil
| Coq_cons (y, l) ->
  All2_fold_cons (y, y, l, l, (coq_All2_fold_refl hP l), (hP l y))

(** val coq_All2_fold_trans :
    ('a1 list -> 'a1 list -> 'a1 list -> 'a1 -> 'a1 -> 'a1 -> ('a1, 'a2)
    coq_All2_fold -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a2) coq_All2_fold ->
    'a2 -> 'a2 -> 'a2) -> ('a1 list, ('a1, 'a2) coq_All2_fold) coq_Transitive **)

let rec coq_All2_fold_trans hP _ _ z = function
| All2_fold_nil -> (fun x -> x)
| All2_fold_cons (d, d', _UU0393_, _UU0393_', a, y) ->
  let iHAll2_fold = fun x -> coq_All2_fold_trans hP _UU0393_ _UU0393_' x a in
  (fun h' ->
  let h'0 = ((Coq_cons (d', _UU0393_')),z),h' in
  let h'2 = let _,pr2 = h'0 in pr2 in
  (match h'2 with
   | All2_fold_nil -> assert false (* absurd case *)
   | All2_fold_cons (_, d'0, _, _UU0393_'0, a0, p) ->
     All2_fold_cons (d, d'0, _UU0393_, _UU0393_'0,
       (iHAll2_fold _UU0393_'0 a0),
       (hP _UU0393_ _UU0393_' _UU0393_'0 d d' d'0 a a0
         (iHAll2_fold _UU0393_'0 a0) y p))))

(** val coq_All2_fold_sym :
    ('a1 list -> 'a1 list -> 'a1 -> 'a1 -> ('a1, 'a2) coq_All2_fold -> ('a1,
    'a2) coq_All2_fold -> 'a2 -> 'a2) -> ('a1 list, ('a1, 'a2) coq_All2_fold)
    coq_Symmetric **)

let rec coq_All2_fold_sym hP _ _ = function
| All2_fold_nil -> All2_fold_nil
| All2_fold_cons (d, d', _UU0393_, _UU0393_', a, y) ->
  let iHAll2_fold = coq_All2_fold_sym hP _UU0393_ _UU0393_' a in
  All2_fold_cons (d', d, _UU0393_', _UU0393_, iHAll2_fold,
  (hP _UU0393_ _UU0393_' d d' a iHAll2_fold y))

(** val coq_All2_fold_app_inv :
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold
    -> (('a1, 'a2) coq_All2_fold, ('a1, 'a2) coq_All2_fold) prod **)

let rec coq_All2_fold_app_inv _UU0393_ _UU0393_' _UU0394_ _UU0394_' x =
  match _UU0394_ with
  | Coq_nil ->
    (match _UU0394_' with
     | Coq_nil -> Coq_pair (x, All2_fold_nil)
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | Coq_cons (y, l) ->
    (match _UU0394_' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l0) ->
       let iH_UU0394_ = fun x0 ->
         coq_All2_fold_app_inv _UU0393_ _UU0393_' l l0 x0
       in
       let h'0 = ((Coq_cons (y, (app l _UU0393_))),(Coq_cons (a,
         (app l0 _UU0393_')))),x
       in
       let h'2 = let _,pr2 = h'0 in pr2 in
       (match h'2 with
        | All2_fold_nil -> assert false (* absurd case *)
        | All2_fold_cons (_, _, _, _, a0, p) ->
          let iH_UU0394_0 = iH_UU0394_ a0 in
          let Coq_pair (a1, b) = iH_UU0394_0 in
          Coq_pair (a1, (All2_fold_cons (y, a, l, l0, b, p)))))

(** val coq_All2_fold_app_inv_l :
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold
    -> (('a1, 'a2) coq_All2_fold, ('a1, 'a2) coq_All2_fold) prod **)

let rec coq_All2_fold_app_inv_l _UU0393_ _UU0393_' _UU0394_ _UU0394_' x =
  match _UU0394_ with
  | Coq_nil ->
    (match _UU0394_' with
     | Coq_nil -> Coq_pair (x, All2_fold_nil)
     | Coq_cons (_, _) -> assert false (* absurd case *))
  | Coq_cons (y, l) ->
    (match _UU0394_' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l0) ->
       let iH_UU0394_ = fun x0 ->
         coq_All2_fold_app_inv_l _UU0393_ _UU0393_' l l0 x0
       in
       let h'0 = ((Coq_cons (y, (app l _UU0393_))),(Coq_cons (a,
         (app l0 _UU0393_')))),x
       in
       let h'2 = let _,pr2 = h'0 in pr2 in
       (match h'2 with
        | All2_fold_nil -> assert false (* absurd case *)
        | All2_fold_cons (_, _, _, _, a0, p) ->
          let iH_UU0394_0 = iH_UU0394_ a0 in
          let Coq_pair (a1, b) = iH_UU0394_0 in
          Coq_pair (a1, (All2_fold_cons (y, a, l, l0, b, p)))))

(** val coq_All2_fold_impl_ind :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1 list -> 'a1 list
    -> 'a1 -> 'a1 -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a3) coq_All2_fold ->
    'a2 -> 'a3) -> ('a1, 'a3) coq_All2_fold **)

let rec coq_All2_fold_impl_ind _ _ cr hcr =
  match cr with
  | All2_fold_nil -> All2_fold_nil
  | All2_fold_cons (d, d', _UU0393_, _UU0393_', a, y) ->
    let iHcr = coq_All2_fold_impl_ind _UU0393_ _UU0393_' a hcr in
    All2_fold_cons (d, d', _UU0393_, _UU0393_', iHcr,
    (hcr _UU0393_ _UU0393_' d d' a iHcr y))

(** val coq_All2_fold_impl_len :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1 list -> 'a1 list
    -> 'a1 -> 'a1 -> __ -> 'a2 -> 'a3) -> ('a1, 'a3) coq_All2_fold **)

let rec coq_All2_fold_impl_len _ _ h hP =
  match h with
  | All2_fold_nil -> All2_fold_nil
  | All2_fold_cons (d, d', _UU0393_, _UU0393_', a, y) ->
    All2_fold_cons (d, d', _UU0393_, _UU0393_',
      (coq_All2_fold_impl_len _UU0393_ _UU0393_' a hP),
      (hP _UU0393_ _UU0393_' d d' __ y))

(** val coq_All2_fold_nth :
    nat -> 'a1 list -> 'a1 list -> 'a1 -> ('a1, 'a2) coq_All2_fold -> ('a1,
    (__, (('a1, 'a2) coq_All2_fold, 'a2) prod) prod) sigT **)

let rec coq_All2_fold_nth n _UU0393_ _UU0393_' d hrel =
  match n with
  | O ->
    (match _UU0393_ with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       let hrel0 = ((Coq_cons (a, l)),_UU0393_'),hrel in
       let hrel2 = let _,pr2 = hrel0 in pr2 in
       (match hrel2 with
        | All2_fold_nil -> assert false (* absurd case *)
        | All2_fold_cons (_, d', _, _, a0, p) ->
          Coq_existT (d', (Coq_pair (__, (Coq_pair (a0, p)))))))
  | S n0 ->
    (match _UU0393_ with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       let hrel0 = ((Coq_cons (a, l)),_UU0393_'),hrel in
       let hrel2 = let _,pr2 = hrel0 in pr2 in
       (match hrel2 with
        | All2_fold_nil -> assert false (* absurd case *)
        | All2_fold_cons (_, _, _, _UU0393_'0, a0, _) ->
          let s = coq_All2_fold_nth n0 l _UU0393_'0 d a0 in
          let Coq_existT (x, p) = s in
          Coq_existT (x,
          (let Coq_pair (_, b) = p in
           let Coq_pair (a1, b0) = b in Coq_pair (__, (Coq_pair (a1, b0)))))))

(** val coq_All2_fold_nth_r :
    nat -> 'a1 list -> 'a1 list -> 'a1 -> ('a1, 'a2) coq_All2_fold -> ('a1,
    (__, (('a1, 'a2) coq_All2_fold, 'a2) prod) prod) sigT **)

let rec coq_All2_fold_nth_r n _UU0393_ _UU0393_' d' hrel =
  match n with
  | O ->
    (match _UU0393_' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       let hrel0 = (_UU0393_,(Coq_cons (a, l))),hrel in
       let hrel2 = let _,pr2 = hrel0 in pr2 in
       (match hrel2 with
        | All2_fold_nil -> assert false (* absurd case *)
        | All2_fold_cons (d, _, _, _, a0, p) ->
          Coq_existT (d, (Coq_pair (__, (Coq_pair (a0, p)))))))
  | S n0 ->
    (match _UU0393_' with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (a, l) ->
       let hrel0 = (_UU0393_,(Coq_cons (a, l))),hrel in
       let hrel2 = let _,pr2 = hrel0 in pr2 in
       (match hrel2 with
        | All2_fold_nil -> assert false (* absurd case *)
        | All2_fold_cons (_, _, _UU0393_0, _, a0, _) ->
          let s = coq_All2_fold_nth_r n0 _UU0393_0 l d' a0 in
          let Coq_existT (x, p) = s in
          Coq_existT (x,
          (let Coq_pair (_, b) = p in
           let Coq_pair (a1, b0) = b in Coq_pair (__, (Coq_pair (a1, b0)))))))

(** val coq_All2_fold_prod :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a3)
    coq_All2_fold -> ('a1, ('a2, 'a3) prod) coq_All2_fold **)

let rec coq_All2_fold_prod _ _ a h =
  match a with
  | All2_fold_nil ->
    let h0 = (Coq_nil,Coq_nil),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_fold_nil -> All2_fold_nil
     | All2_fold_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
  | All2_fold_cons (d, d', _UU0393_, _UU0393_', a0, y) ->
    let h0 = ((Coq_cons (d, _UU0393_)),(Coq_cons (d', _UU0393_'))),h in
    let h2 = let _,pr2 = h0 in pr2 in
    (match h2 with
     | All2_fold_nil -> assert false (* absurd case *)
     | All2_fold_cons (_, _, _, _, a1, q) ->
       All2_fold_cons (d, d', _UU0393_, _UU0393_',
         (coq_All2_fold_prod _UU0393_ _UU0393_' a0 a1), (Coq_pair (y, q))))

(** val coq_All2_fold_prod_inv :
    'a1 list -> 'a1 list -> ('a1, ('a2, 'a3) prod) coq_All2_fold -> (('a1,
    'a2) coq_All2_fold, ('a1, 'a3) coq_All2_fold) prod **)

let rec coq_All2_fold_prod_inv _ _ = function
| All2_fold_nil -> Coq_pair (All2_fold_nil, All2_fold_nil)
| All2_fold_cons (d, d', _UU0393_, _UU0393_', a0, y) ->
  let iHX = coq_All2_fold_prod_inv _UU0393_ _UU0393_' a0 in
  Coq_pair ((All2_fold_cons (d, d', _UU0393_, _UU0393_',
  (let Coq_pair (a1, _) = iHX in a1), (let Coq_pair (a1, _) = y in a1))),
  (All2_fold_cons (d, d', _UU0393_, _UU0393_',
  (let Coq_pair (_, b) = iHX in b), (let Coq_pair (_, b) = y in b))))

(** val coq_All_fold_prod :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1, 'a2)
    coq_All_fold -> ('a1 list -> 'a1 list -> 'a1 -> 'a1 -> ('a1, 'a2)
    coq_All_fold -> ('a1, 'a2) coq_All_fold -> ('a1, 'a3) coq_All2_fold ->
    'a2 -> 'a2 -> 'a3) -> ('a1, 'a3) coq_All2_fold **)

let coq_All_fold_prod _UU0393_ _UU0394_ ha hb h =
  let rec f _ = function
  | All_fold_nil ->
    (fun _ _ hb0 ->
      match hb0 with
      | All_fold_nil -> All2_fold_nil
      | All_fold_cons (_, _, _, _) -> assert false (* absurd case *))
  | All_fold_cons (d, _UU0393_0, a0, y) ->
    let iHha = f _UU0393_0 a0 in
    (fun _ _ hb0 ->
    match hb0 with
    | All_fold_nil -> assert false (* absurd case *)
    | All_fold_cons (d0, _UU0393_1, a1, p) ->
      All2_fold_cons (d, d0, _UU0393_0, _UU0393_1, (iHha _UU0393_1 __ a1),
        (h _UU0393_0 _UU0393_1 d d0 a0 a1 (iHha _UU0393_1 __ a1) y p)))
  in f _UU0393_ ha _UU0394_ __ hb

(** val coq_All2_fold_All_fold_mix :
    'a1 list -> 'a1 list -> ('a1, 'a2) coq_All2_fold -> ('a1, 'a3)
    coq_All_fold -> ('a1, 'a3) coq_All_fold -> ('a1, ('a3, ('a3, 'a2) prod)
    prod) coq_All2_fold **)

let rec coq_All2_fold_All_fold_mix _ _ a x x0 =
  match a with
  | All2_fold_nil -> All2_fold_nil
  | All2_fold_cons (d, d', _UU0393_, _UU0393_', a0, y) ->
    let l0 = (Coq_cons (d, _UU0393_)),x in
    let l2 = let _,pr2 = l0 in pr2 in
    (match l2 with
     | All_fold_nil -> assert false (* absurd case *)
     | All_fold_cons (_, _, a1, q) ->
       let r0 = (Coq_cons (d', _UU0393_')),x0 in
       let r2 = let _,pr2 = r0 in pr2 in
       (match r2 with
        | All_fold_nil -> assert false (* absurd case *)
        | All_fold_cons (_, _, a2, q0) ->
          All2_fold_cons (d, d', _UU0393_, _UU0393_',
            (coq_All2_fold_All_fold_mix _UU0393_ _UU0393_' a0 a1 a2),
            (Coq_pair (q, (Coq_pair (q0, y)))))))

(** val coq_All2_fold_All_fold_mix_inv :
    'a1 list -> 'a1 list -> ('a1, ('a3, ('a3, 'a2) prod) prod) coq_All2_fold
    -> (('a1, 'a2) coq_All2_fold, (('a1, 'a3) coq_All_fold, ('a1, 'a3)
    coq_All_fold) prod) prod **)

let rec coq_All2_fold_All_fold_mix_inv _ _ = function
| All2_fold_nil ->
  Coq_pair (All2_fold_nil, (Coq_pair (All_fold_nil, All_fold_nil)))
| All2_fold_cons (d, d', _UU0393_, _UU0393_', a0, y) ->
  let Coq_pair (a1, b) = y in
  let Coq_pair (a2, b0) = coq_All2_fold_All_fold_mix_inv _UU0393_ _UU0393_' a0
  in
  let Coq_pair (a3, b1) = b in
  let Coq_pair (a4, b2) = b0 in
  Coq_pair ((All2_fold_cons (d, d', _UU0393_, _UU0393_', a2, b1)), (Coq_pair
  ((All_fold_cons (d, _UU0393_, a4, a1)), (All_fold_cons (d', _UU0393_', b2,
  a3)))))

(** val coq_All_fold_All2_fold_impl :
    'a1 list -> ('a1, 'a2) coq_All_fold -> ('a1 list -> 'a1 -> ('a1, 'a2)
    coq_All_fold -> ('a1, 'a3) coq_All2_fold -> 'a2 -> 'a3) -> ('a1, 'a3)
    coq_All2_fold **)

let rec coq_All_fold_All2_fold_impl _ a h =
  match a with
  | All_fold_nil -> All2_fold_nil
  | All_fold_cons (d, _UU0393_, a0, y) ->
    let iHa = coq_All_fold_All2_fold_impl _UU0393_ a0 h in
    All2_fold_cons (d, d, _UU0393_, _UU0393_, iHa, (h _UU0393_ d a0 iHa y))

(** val coq_All_fold_All2_fold :
    'a1 list -> (('a1, 'a2) coq_All_fold, ('a1, 'a2) coq_All2_fold) iffT **)

let coq_All_fold_All2_fold _UU0393_ =
  Coq_pair ((fun x ->
    let rec f _ = function
    | All_fold_nil -> All2_fold_nil
    | All_fold_cons (d, _UU0393_0, a0, y) ->
      All2_fold_cons (d, d, _UU0393_0, _UU0393_0, (f _UU0393_0 a0), y)
    in f _UU0393_ x), (fun h ->
    let h0 = (_UU0393_,_UU0393_),h in
    let h2 = let _,pr2 = h0 in pr2 in
    let h1 = let pr1,_ = h0 in pr1 in
    let h1' = let pr1,_ = h1 in pr1 in
    let h3 = let _,pr2 = h1 in pr2 in
    let rec f _ _ a _ =
      match a with
      | All2_fold_nil -> All_fold_nil
      | All2_fold_cons (d, _, _UU0393_0, _UU0393_', a0, y) ->
        let iHAll2_fold = f _UU0393_0 _UU0393_' a0 _UU0393_0 in
        All_fold_cons (d, _UU0393_0, iHAll2_fold, y)
    in f h1' h3 h2 _UU0393_))

(** val coq_All_remove_last :
    'a1 list -> ('a1, 'a2) coq_All -> ('a1, 'a2) coq_All **)

let coq_All_remove_last l x =
  coq_All_firstn l (sub (length l) (S O)) x

(** val coq_All3_map_all :
    'a4 list -> 'a5 list -> 'a6 list -> ('a4 -> 'a1) -> ('a5 -> 'a2) -> ('a6
    -> 'a3) -> ('a4, 'a5, 'a6, 'a7) coq_All3 -> ('a1, 'a2, 'a3, 'a7) coq_All3 **)

let rec coq_All3_map_all _ _ _ f g h = function
| All3_nil -> All3_nil
| All3_cons (x0, y, z, l, l', l'', y0, a) ->
  All3_cons ((f x0), (g y), (h z), (map f l), (map g l'), (map h l''), y0,
    (coq_All3_map_all l l' l'' f g h a))

(** val coq_OnOne2All_All3 :
    'a1 list -> 'a2 list -> 'a2 list -> ('a1 -> 'a2 -> 'a2 -> 'a3 -> 'a4) ->
    ('a1 -> 'a2 -> 'a4) -> ('a2, 'a1, 'a3) coq_OnOne2All -> ('a1, 'a2, 'a2,
    'a4) coq_All3 **)

let rec coq_OnOne2All_All3 _ _ _ h1 h2 = function
| OnOne2All_hd (b, bs, hd, hd', tl, y) ->
  All3_cons (b, hd, hd', bs, tl, tl, (h1 b hd hd' y),
    (let rec f l bs0 =
       match l with
       | Coq_nil ->
         (match bs0 with
          | Coq_nil -> All3_nil
          | Coq_cons (_, _) -> assert false (* absurd case *))
       | Coq_cons (y0, l0) ->
         (match bs0 with
          | Coq_nil -> assert false (* absurd case *)
          | Coq_cons (a, l1) ->
            All3_cons (a, y0, y0, l1, l0, l0, (h2 a y0), (f l0 l1)))
     in f tl bs))
| OnOne2All_tl (b, bs, hd, tl, tl', o) ->
  All3_cons (b, hd, hd, bs, tl, tl', (h2 b hd),
    (coq_OnOne2All_All3 bs tl tl' h1 h2 o))

(** val map_All : ('a1 -> __ -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map_All fn = function
| Coq_nil -> Coq_nil
| Coq_cons (a, l0) -> Coq_cons ((fn a __), (map_All fn l0))

type ('a, 'b, 'c, 'q) map_All_graph =
| Coq_map_All_graph_equation_1
| Coq_map_All_graph_equation_2 of 'a * 'a list
   * ('a, 'b, 'c, 'q) map_All_graph

(** val map_All_graph_rect :
    ('a1 -> __ -> 'a2) -> (__ -> 'a5) -> ('a1 -> 'a1 list -> __ -> ('a1, 'a2,
    'a3, 'a4) map_All_graph -> 'a5 -> 'a5) -> 'a1 list -> 'a2 list -> ('a1,
    'a2, 'a3, 'a4) map_All_graph -> 'a5 **)

let rec map_All_graph_rect fn f f0 _ _ = function
| Coq_map_All_graph_equation_1 -> f __
| Coq_map_All_graph_equation_2 (x, xs, hind) ->
  f0 x xs __ hind (map_All_graph_rect fn f f0 xs (map_All fn xs) hind)

(** val map_All_graph_correct :
    ('a1 -> __ -> 'a2) -> 'a1 list -> ('a1, 'a2, 'a3, 'a4) map_All_graph **)

let rec map_All_graph_correct fn = function
| Coq_nil -> Coq_map_All_graph_equation_1
| Coq_cons (a, l0) ->
  Coq_map_All_graph_equation_2 (a, l0, (map_All_graph_correct fn l0))

(** val map_All_elim :
    ('a1 -> __ -> 'a2) -> (__ -> 'a5) -> ('a1 -> 'a1 list -> __ -> 'a5 ->
    'a5) -> 'a1 list -> 'a5 **)

let map_All_elim fn f f0 l =
  let rec f1 _ _ = function
  | Coq_map_All_graph_equation_1 -> f __
  | Coq_map_All_graph_equation_2 (x, xs, hind) ->
    f0 x xs __ (f1 xs (map_All fn xs) hind)
  in f1 l (map_All fn l) (map_All_graph_correct fn l)

(** val coq_FunctionalElimination_map_All :
    ('a1 -> __ -> 'a2) -> (__ -> __) -> ('a1 -> 'a1 list -> __ -> __ -> __)
    -> 'a1 list -> __ **)

let coq_FunctionalElimination_map_All =
  map_All_elim

(** val coq_FunctionalInduction_map_All :
    ('a1 -> __ -> 'a2) -> ('a1 list -> __ -> 'a2 list) coq_FunctionalInduction **)

let coq_FunctionalInduction_map_All fn =
  Obj.magic (fun x _ -> map_All_graph_correct fn x)

(** val coq_All_map_All :
    ('a1 -> __ -> 'a2) -> 'a1 list -> ('a3 -> 'a4 -> ('a1, __) coq_All) ->
    ('a1 -> 'a3 -> __ -> __ -> 'a5) -> 'a3 -> 'a4 -> ('a2, 'a5) coq_All **)

let coq_All_map_All f args =
  let packcall = args,__ in
  fun_elim (fun x _ -> map_All f x) (S (S (S O)))
    (Obj.magic (fun _ x x0 x1 _ ->
      coq_FunctionalElimination_map_All f x x0 x1)) __
    (fun _ _ _ _ _ _ _ _ _ _ _ -> All_nil) (fun x xs _ x0 _ _ _ _ _ _ ->
    let x1 = fun _ _ -> x0 __ __ xs __ __ __ in
    (fun ha hf y hy ->
    let x2 = ha y hy in
    let x3 = (Coq_cons (x, xs)),x2 in
    let x4 = let _,pr2 = x3 in pr2 in
    (match x4 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, _, _) ->
       All_cons ((f x __),
         (let rec map_All0 = function
          | Coq_nil -> Coq_nil
          | Coq_cons (a, l0) -> Coq_cons ((f a __), (map_All0 l0))
          in map_All0 xs), (hf x y __ __),
         (x1 __ __ (fun y0 x5 ->
           let x6 = ha y0 x5 in
           let x7 = (Coq_cons (x, xs)),x6 in
           let x8 = let _,pr2 = x7 in pr2 in
           (match x8 with
            | All_nil -> assert false (* absurd case *)
            | All_cons (_, _, _, a) -> a)) hf y hy)))))
    (let pr1,_ = packcall in pr1) __ __ __ args __ __ __

(** val coq_All2_map2_left :
    ('a2 -> 'a3 -> 'a5) -> 'a2 list -> 'a3 list -> 'a1 list -> 'a4 list ->
    ('a2, 'a4, 'a8) coq_All2 -> ('a3, 'a1, 'a7) coq_All2 -> ('a2 -> 'a3 ->
    'a1 -> 'a4 -> 'a8 -> 'a7 -> 'a6) -> ('a5, 'a1, 'a6) coq_All2 **)

let rec coq_All2_map2_left f l _ _ l''' hb ha hPQ =
  match ha with
  | All2_nil -> All2_nil
  | All2_cons (x, y, l0, l', y0, a) ->
    (match l with
     | Coq_nil -> assert false (* absurd case *)
     | Coq_cons (b, l1) ->
       let hb0 = ((Coq_cons (b, l1)),l'''),hb in
       let hb2 = let _,pr2 = hb0 in pr2 in
       (match hb2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, y1, _, l'0, r, a0) ->
          let iHha = coq_All2_map2_left f l1 l0 l' l'0 a0 a hPQ in
          All2_cons ((f b x), y, (map2 f l1 l0), l', (hPQ b x y y1 r y0),
          iHha)))

(** val coq_All2_map2_left_All3 :
    ('a2 -> 'a3 -> 'a1) -> 'a2 list -> 'a3 list -> 'a1 list -> ('a2, 'a3,
    'a1, 'a4) coq_All3 -> ('a1, 'a1, 'a4) coq_All2 **)

let rec coq_All2_map2_left_All3 f _ _ _ = function
| All3_nil -> All2_nil
| All3_cons (x0, y, z, l, l', l'', y0, a) ->
  All2_cons ((f x0 y), z,
    (let rec map3 l0 l'0 =
       match l0 with
       | Coq_nil -> Coq_nil
       | Coq_cons (hd, tl) ->
         (match l'0 with
          | Coq_nil -> Coq_nil
          | Coq_cons (hd', tl') -> Coq_cons ((f hd hd'), (map3 tl tl')))
     in map3 l l'), l'', y0, (coq_All2_map2_left_All3 f l l' l'' a))

(** val coq_All3_impl :
    'a1 list -> 'a2 list -> 'a3 list -> ('a1, 'a2, 'a3, 'a4) coq_All3 -> ('a1
    -> 'a2 -> 'a3 -> 'a4 -> 'a5) -> ('a1, 'a2, 'a3, 'a5) coq_All3 **)

let rec coq_All3_impl _ _ _ a x =
  match a with
  | All3_nil -> All3_nil
  | All3_cons (x0, y, z, l, l', l'', y0, a0) ->
    All3_cons (x0, y, z, l, l', l'', (x x0 y z y0),
      (coq_All3_impl l l' l'' a0 x))

(** val coq_All1_map2_right_inv :
    ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> ('a1, 'a3, 'a4) coq_All2
    -> ('a1, 'a2, 'a4) coq_All2 **)

let coq_All1_map2_right_inv g l l' x =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = fun _ -> All2_nil in
    let _evar_0_0 = fun _ _ _ -> assert false (* absurd case *) in
    (fun _ ->
    match __top_assumption_ with
    | Coq_nil -> _evar_0_
    | Coq_cons (a, l0) -> (fun x0 -> _evar_0_0 a l0 x0))
  in
  let _evar_0_0 = fun x0 xs ih __top_assumption_ ->
    let _evar_0_0 = fun _ -> assert false (* absurd case *) in
    let _evar_0_1 = fun y ys z ->
      let z0 = ((Coq_cons (x0, xs)),(Coq_cons ((g x0 y), (map2 g xs ys)))),z
      in
      let z2 = let _,pr2 = z0 in pr2 in
      (match z2 with
       | All2_nil -> assert false (* absurd case *)
       | All2_cons (_, _, _, _, r, a) ->
         All2_cons (x0, y, xs, ys, r, (ih ys __ a)))
    in
    (fun _ ->
    match __top_assumption_ with
    | Coq_nil -> _evar_0_0
    | Coq_cons (a, l0) -> (fun z -> _evar_0_1 a l0 z))
  in
  let rec f = function
  | Coq_nil -> _evar_0_
  | Coq_cons (y, l1) -> _evar_0_0 y l1 (f l1)
  in f l l' __ x

(** val coq_All1_map2_right :
    ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a4) coq_All2
    -> ('a1, 'a3, 'a4) coq_All2 **)

let coq_All1_map2_right g l l' =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = fun _ -> All2_nil in
    let _evar_0_0 = fun _ _ _ -> All2_nil in
    (match __top_assumption_ with
     | Coq_nil -> _evar_0_
     | Coq_cons (a, l0) -> _evar_0_0 a l0)
  in
  let _evar_0_0 = fun x xs ih __top_assumption_ ->
    let _evar_0_0 = fun _ -> assert false (* absurd case *) in
    let _evar_0_1 = fun y ys z -> All2_cons (x, (g x y), xs, (map2 g xs ys),
      (let z0 = ((Coq_cons (x, xs)),(Coq_cons (y, ys))),z in
       let z2 = let _,pr2 = z0 in pr2 in
       (match z2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, r, _) -> r)),
      (let z0 = ((Coq_cons (x, xs)),(Coq_cons (y, ys))),z in
       let z2 = let _,pr2 = z0 in pr2 in
       (match z2 with
        | All2_nil -> assert false (* absurd case *)
        | All2_cons (_, _, _, _, _, a) -> ih ys a)))
    in
    (match __top_assumption_ with
     | Coq_nil -> _evar_0_0
     | Coq_cons (a, l0) -> _evar_0_1 a l0)
  in
  let rec f = function
  | Coq_nil -> _evar_0_
  | Coq_cons (y, l1) -> _evar_0_0 y l1 (f l1)
  in f l l'

(** val coq_All1i_map2_right :
    nat -> ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a4)
    coq_All2i -> ('a1, 'a3, 'a4) coq_All2i **)

let coq_All1i_map2_right k g l l' =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = fun _ _ -> All2i_nil in
    let _evar_0_0 = fun _ _ _ _ -> All2i_nil in
    (match __top_assumption_ with
     | Coq_nil -> _evar_0_
     | Coq_cons (a, l0) -> _evar_0_0 a l0)
  in
  let _evar_0_0 = fun x xs ih __top_assumption_ ->
    let _evar_0_0 = fun _ _ -> assert false (* absurd case *) in
    let _evar_0_1 = fun y ys k0 z -> All2i_cons (x, (g x y), xs,
      (map2 g xs ys),
      (let z0 = (k0,((Coq_cons (x, xs)),(Coq_cons (y, ys)))),z in
       let z2 = let _,pr2 = z0 in pr2 in
       (match z2 with
        | All2i_nil -> assert false (* absurd case *)
        | All2i_cons (_, _, _, _, r, _) -> r)),
      (let z0 = (k0,((Coq_cons (x, xs)),(Coq_cons (y, ys)))),z in
       let z2 = let _,pr2 = z0 in pr2 in
       (match z2 with
        | All2i_nil -> assert false (* absurd case *)
        | All2i_cons (_, _, _, _, _, a) -> ih ys (S k0) a)))
    in
    (match __top_assumption_ with
     | Coq_nil -> _evar_0_0
     | Coq_cons (a, l0) -> _evar_0_1 a l0)
  in
  let rec f = function
  | Coq_nil -> _evar_0_
  | Coq_cons (y, l1) -> _evar_0_0 y l1 (f l1)
  in f l l' k

(** val coq_All1i_Alli_mix_left :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a3) coq_Alli -> ('a1, 'a2, 'a4)
    coq_All2i -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2i **)

let coq_All1i_Alli_mix_left k l l' _Hyp_ h =
  let _evar_0_ = fun n q ->
    let q0 = (n,Coq_nil),q in
    let q2 = let _,pr2 = q0 in pr2 in
    (match q2 with
     | Alli_nil -> All2i_nil
     | Alli_cons (_, _, _, _) -> assert false (* absurd case *))
  in
  let _evar_0_0 = fun n x y xs ys r _ ih q ->
    let q0 = (n,(Coq_cons (x, xs))),q in
    let q2 = let _,pr2 = q0 in pr2 in
    (match q2 with
     | Alli_nil -> assert false (* absurd case *)
     | Alli_cons (_, _, q1, a) ->
       All2i_cons (x, y, xs, ys, (Coq_pair (q1, r)), (ih a)))
  in
  let rec f n _ _ = function
  | All2i_nil -> _evar_0_ n
  | All2i_cons (x, y, l0, r, y0, a0) ->
    _evar_0_0 n x y l0 r y0 a0 (f (S n) l0 r a0)
  in f k l l' h _Hyp_

(** val coq_All_Alli_swap_iff :
    'a2 list -> 'a1 list -> nat -> (('a1, ('a2, 'a3) coq_Alli) coq_All, ('a2,
    ('a1, 'a3) coq_All) coq_Alli) iffT **)

let rec coq_All_Alli_swap_iff = function
| Coq_nil ->
  (fun ls2 _ ->
    match ls2 with
    | Coq_nil ->
      Coq_pair ((fun x ->
        match x with
        | All_nil -> Alli_nil
        | All_cons (_, _, _, _) -> assert false (* absurd case *)), (fun x ->
        match x with
        | Alli_nil -> All_nil
        | Alli_cons (_, _, _, _) -> assert false (* absurd case *)))
    | Coq_cons (a, l0) ->
      Coq_pair ((fun x ->
        match x with
        | All_nil -> assert false (* absurd case *)
        | All_cons (_, _, _, _) -> Alli_nil), (fun x ->
        match x with
        | Alli_nil ->
          All_cons (a, l0, Alli_nil, (coq_In_All l0 (fun _ _ -> Alli_nil)))
        | Alli_cons (_, _, _, _) -> assert false (* absurd case *))))
| Coq_cons (y, l0) ->
  let iH = coq_All_Alli_swap_iff l0 in
  (fun ls2 n ->
  match ls2 with
  | Coq_nil ->
    Coq_pair ((fun x ->
      match x with
      | All_nil ->
        Alli_cons (y, l0, All_nil,
          (let ls3 = Coq_nil in
           let n0 = S n in let Coq_pair (x0, _) = iH ls3 n0 in x0 All_nil))
      | All_cons (_, _, _, _) -> assert false (* absurd case *)), (fun x ->
      match x with
      | Alli_nil -> assert false (* absurd case *)
      | Alli_cons (_, _, _, _) -> All_nil))
  | Coq_cons (a, l1) ->
    Coq_pair ((fun x ->
      match x with
      | All_nil -> assert false (* absurd case *)
      | All_cons (_, _, x0, _) ->
        Alli_cons (y, l0, (All_cons (a, l1,
          (match x with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, x1, _) ->
             (match x1 with
              | Alli_nil -> assert false (* absurd case *)
              | Alli_cons (_, _, _, _) ->
                (match x0 with
                 | Alli_nil -> assert false (* absurd case *)
                 | Alli_cons (_, _, x2, _) -> x2))),
          (match x with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, x1, x2) ->
             (match x1 with
              | Alli_nil -> assert false (* absurd case *)
              | Alli_cons (_, _, _, _) ->
                (match x0 with
                 | Alli_nil -> assert false (* absurd case *)
                 | Alli_cons (_, _, _, _) ->
                   coq_All_impl l1 x2 (fun _ x3 ->
                     match x3 with
                     | Alli_nil -> assert false (* absurd case *)
                     | Alli_cons (_, _, x4, _) -> x4)))))),
          (let ls3 = Coq_cons (a, l1) in
           let n0 = S n in
           let Coq_pair (x1, _) = iH ls3 n0 in
           x1
             (match x with
              | All_nil -> assert false (* absurd case *)
              | All_cons (_, _, x2, x3) ->
                (match x2 with
                 | Alli_nil -> assert false (* absurd case *)
                 | Alli_cons (_, _, _, _) ->
                   (match x0 with
                    | Alli_nil -> assert false (* absurd case *)
                    | Alli_cons (_, _, _, x4) ->
                      All_cons (a, l1, x4,
                        (coq_All_impl l1 x3 (fun _ x5 ->
                          match x5 with
                          | Alli_nil -> assert false (* absurd case *)
                          | Alli_cons (_, _, _, x6) -> x6))))))))), (fun x ->
      match x with
      | Alli_nil -> assert false (* absurd case *)
      | Alli_cons (_, _, x0, x1) ->
        All_cons (a, l1, (Alli_cons (y, l0,
          (let x2 = fun ls3 n0 -> let Coq_pair (_, x2) = iH ls3 n0 in x2 in
           let x3 = x2 (Coq_cons (a, l1)) (S n) x1 in
           (match x3 with
            | All_nil -> assert false (* absurd case *)
            | All_cons (_, _, _, _) ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x4, _) ->
                 (match x with
                  | Alli_nil -> assert false (* absurd case *)
                  | Alli_cons (_, _, _, _) -> x4)))),
          (let x2 = fun ls3 n0 -> let Coq_pair (_, x2) = iH ls3 n0 in x2 in
           let x3 = x2 (Coq_cons (a, l1)) (S n) x1 in
           (match x3 with
            | All_nil -> assert false (* absurd case *)
            | All_cons (_, _, x4, _) ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, _, _) ->
                 (match x with
                  | Alli_nil -> assert false (* absurd case *)
                  | Alli_cons (_, _, _, _) -> x4)))))),
          (let x2 = fun ls3 n0 -> let Coq_pair (_, x2) = iH ls3 n0 in x2 in
           let x3 = x2 (Coq_cons (a, l1)) (S n) x1 in
           (match x3 with
            | All_nil -> assert false (* absurd case *)
            | All_cons (_, _, _, x4) ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, _, x5) ->
                 (match x with
                  | Alli_nil -> assert false (* absurd case *)
                  | Alli_cons (_, _, _, _) ->
                    coq_All_impl_All l1 x5
                      (coq_All_impl_All l1 x4
                        (coq_In_All l1 (fun _ _ x6 x7 -> Alli_cons (y, l0,
                          x7, x6))))))))))))

(** val coq_All_eta3 :
    (('a1, 'a2) prod, 'a3) prod list -> (((('a1, 'a2) prod, 'a3) prod, __)
    coq_All, ((('a1, 'a2) prod, 'a3) prod, 'a4) coq_All) iffT **)

let coq_All_eta3 ls =
  Coq_pair ((fun x ->
    let rec f _ = function
    | All_nil -> All_nil
    | All_cons (x0, l, y, a0) -> All_cons (x0, l, (Obj.magic y), (f l a0))
    in f ls x), (fun x ->
    let rec f _ = function
    | All_nil -> All_nil
    | All_cons (x0, l, y, a0) -> All_cons (x0, l, (Obj.magic y), (f l a0))
    in f ls x))

(** val coq_All2_All_swap :
    'a3 list -> 'a1 list -> 'a2 list -> ('a1, 'a2, ('a3, 'a4) coq_All)
    coq_All2 -> ('a3, ('a1, 'a2, 'a4) coq_All2) coq_All **)

let rec coq_All2_All_swap l ls2 ls3 x =
  match l with
  | Coq_nil ->
    (match ls2 with
     | Coq_nil ->
       (match ls3 with
        | Coq_nil ->
          (match x with
           | All2_nil -> All_nil
           | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
        | Coq_cons (_, _) -> assert false (* absurd case *))
     | Coq_cons (_, _) ->
       (match ls3 with
        | Coq_nil -> assert false (* absurd case *)
        | Coq_cons (_, _) ->
          (match x with
           | All2_nil -> assert false (* absurd case *)
           | All2_cons (_, _, _, _, x0, _) ->
             (match x0 with
              | All_nil -> All_nil
              | All_cons (_, _, _, _) -> assert false (* absurd case *)))))
  | Coq_cons (y, l0) ->
    (match ls2 with
     | Coq_nil ->
       (match ls3 with
        | Coq_nil ->
          (match x with
           | All2_nil ->
             All_cons (y, l0, All2_nil,
               (coq_All2_All_swap l0 Coq_nil Coq_nil All2_nil))
           | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *))
        | Coq_cons (_, _) -> assert false (* absurd case *))
     | Coq_cons (a, l1) ->
       (match ls3 with
        | Coq_nil -> assert false (* absurd case *)
        | Coq_cons (b, l2) ->
          (match x with
           | All2_nil -> assert false (* absurd case *)
           | All2_cons (_, _, _, _, x0, x1) ->
             (match x0 with
              | All_nil -> assert false (* absurd case *)
              | All_cons (_, _, x2, x3) ->
                All_cons (y, l0, (All2_cons (a, b, l1, l2, x2,
                  (coq_All2_impl l1 l2 x1 (fun _ _ x4 ->
                    match x4 with
                    | All_nil -> assert false (* absurd case *)
                    | All_cons (_, _, x5, _) -> x5)))),
                  (coq_All_impl l0
                    (coq_All_prod l0 x3
                      (coq_All2_All_swap l0 l1 l2
                        (coq_All2_impl l1 l2 x1 (fun _ _ x4 ->
                          match x4 with
                          | All_nil -> assert false (* absurd case *)
                          | All_cons (_, _, _, x5) -> x5)))) (fun _ x4 ->
                    let Coq_pair (y0, y1) = x4 in
                    All2_cons (a, b, l1, l2, y0, y1))))))))

(** val coq_All_All2_swap_sum :
    'a3 list -> 'a1 list -> 'a2 list -> ('a3, ('a1, 'a2, 'a4) coq_All2)
    coq_All -> (__, ('a1, 'a2, ('a3, 'a4) coq_All) coq_All2) sum **)

let rec coq_All_All2_swap_sum l ls2 ls3 x =
  match l with
  | Coq_nil ->
    (match ls2 with
     | Coq_nil ->
       (match ls3 with
        | Coq_nil ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))
        | Coq_cons (_, _) ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *)))
     | Coq_cons (_, _) ->
       (match ls3 with
        | Coq_nil ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))
        | Coq_cons (_, _) ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))))
  | Coq_cons (y, l0) ->
    (match ls2 with
     | Coq_nil ->
       (match ls3 with
        | Coq_nil ->
          (match x with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, x0, _) ->
             (match x0 with
              | All2_nil -> Coq_inr All2_nil
              | All2_cons (_, _, _, _, _, _) -> assert false (* absurd case *)))
        | Coq_cons (_, _) -> assert false (* absurd case *))
     | Coq_cons (a, l1) ->
       (match ls3 with
        | Coq_nil -> assert false (* absurd case *)
        | Coq_cons (b, l2) ->
          (match x with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, x0, x1) ->
             (match x0 with
              | All2_nil -> assert false (* absurd case *)
              | All2_cons (_, _, _, _, x2, x3) ->
                Coq_inr (All2_cons (a, b, l1, l2, (All_cons (y, l0, x2,
                  (coq_All_impl l0 x1 (fun _ x4 ->
                    match x4 with
                    | All2_nil -> assert false (* absurd case *)
                    | All2_cons (_, _, _, _, x5, _) -> x5)))),
                  (coq_All2_impl l1 l2
                    (coq_All2_prod l1 l2 x3
                      (let s =
                         coq_All_All2_swap_sum l0 l1 l2
                           (coq_All_impl l0 x1 (fun _ x4 ->
                             match x4 with
                             | All2_nil -> assert false (* absurd case *)
                             | All2_cons (_, _, _, _, _, x5) -> x5))
                       in
                       match s with
                       | Coq_inl _ ->
                         (match x1 with
                          | All_nil ->
                            coq_All2_impl l1 l2 x3 (fun _ _ _ -> All_nil)
                          | All_cons (_, _, _, _) ->
                            assert false (* absurd case *))
                       | Coq_inr a0 -> a0)) (fun _ _ x4 ->
                    let Coq_pair (y0, y1) = x4 in All_cons (y, l0, y0, y1)))))))))

(** val coq_All_All2_swap :
    'a3 list -> 'a1 list -> 'a2 list -> ('a3, ('a1, 'a2, 'a4) coq_All2)
    coq_All -> ('a1, 'a2, ('a3, 'a4) coq_All) coq_All2 **)

let coq_All_All2_swap ls1 ls2 ls3 x =
  match ls1 with
  | Coq_nil -> coq_All2_from_nth_error ls2 ls3 (fun _ _ _ _ _ _ -> All_nil)
  | Coq_cons (c, l) ->
    let rec f l0 ls4 ls5 x0 =
      match l0 with
      | Coq_nil ->
        (match ls4 with
         | Coq_nil ->
           (match ls5 with
            | Coq_nil ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_nil ->
                    (match x2 with
                     | All_nil -> All2_nil
                     | All_cons (_, _, _, _) -> assert false (* absurd case *))
                  | All2_cons (_, _, _, _, _, _) ->
                    assert false (* absurd case *)))
            | Coq_cons (_, _) -> assert false (* absurd case *))
         | Coq_cons (a, l1) ->
           (match ls5 with
            | Coq_nil -> assert false (* absurd case *)
            | Coq_cons (b, l2) ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_nil -> assert false (* absurd case *)
                  | All2_cons (_, _, _, _, x3, x4) ->
                    (match x2 with
                     | All_nil ->
                       All2_cons (a, b, l1, l2, (All_cons (c, Coq_nil, x3,
                         All_nil)),
                         (coq_All2_impl l1 l2 x4 (fun _ _ x5 -> All_cons (c,
                           Coq_nil, x5, All_nil))))
                     | All_cons (_, _, _, _) -> assert false (* absurd case *))))))
      | Coq_cons (y, l1) ->
        (match ls4 with
         | Coq_nil ->
           (match ls5 with
            | Coq_nil ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_nil ->
                    (match x2 with
                     | All_nil -> assert false (* absurd case *)
                     | All_cons (_, _, x3, _) ->
                       (match x3 with
                        | All2_nil -> All2_nil
                        | All2_cons (_, _, _, _, _, _) ->
                          assert false (* absurd case *)))
                  | All2_cons (_, _, _, _, _, _) ->
                    assert false (* absurd case *)))
            | Coq_cons (_, _) -> assert false (* absurd case *))
         | Coq_cons (a, l2) ->
           (match ls5 with
            | Coq_nil -> assert false (* absurd case *)
            | Coq_cons (b, l3) ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_nil -> assert false (* absurd case *)
                  | All2_cons (_, _, _, _, x3, x4) ->
                    (match x2 with
                     | All_nil -> assert false (* absurd case *)
                     | All_cons (_, _, x5, x6) ->
                       (match x5 with
                        | All2_nil -> assert false (* absurd case *)
                        | All2_cons (_, _, _, _, x7, x8) ->
                          All2_cons (a, b, l2, l3, (All_cons (c, (Coq_cons
                            (y, l1)), x3, (All_cons (y, l1, x7,
                            (coq_All_impl l1 x6 (fun _ x9 ->
                              match x9 with
                              | All2_nil -> assert false (* absurd case *)
                              | All2_cons (_, _, _, _, x10, _) -> x10)))))),
                            (coq_All2_impl l2 l3
                              (coq_All2_prod l2 l3 x4
                                (coq_All2_impl l2 l3
                                  (coq_All2_prod l2 l3 x8
                                    (coq_All2_impl l2 l3
                                      (f l1 l2 l3 (All_cons (c, l1, x4,
                                        (coq_All_impl l1 x6 (fun _ x9 ->
                                          match x9 with
                                          | All2_nil ->
                                            assert false (* absurd case *)
                                          | All2_cons (_, _, _, _, _, x10) ->
                                            x10))))) (fun _ _ x9 ->
                                      match x9 with
                                      | All_nil ->
                                        assert false (* absurd case *)
                                      | All_cons (_, _, _, x10) -> x10)))
                                  (fun _ _ x9 ->
                                  let Coq_pair (y0, y1) = x9 in
                                  All_cons (y, l1, y0, y1)))) (fun _ _ x9 ->
                              let Coq_pair (y0, y1) = x9 in
                              All_cons (c, (Coq_cons (y, l1)), y0, y1))))))))))
    in f l ls2 ls3 x

(** val coq_All2_fold_All_swap :
    'a2 list -> 'a1 list -> 'a1 list -> ('a1, ('a2, 'a3) coq_All)
    coq_All2_fold -> ('a2, ('a1, 'a3) coq_All2_fold) coq_All **)

let rec coq_All2_fold_All_swap l ls2 ls3 x =
  match l with
  | Coq_nil ->
    (match ls2 with
     | Coq_nil ->
       (match ls3 with
        | Coq_nil ->
          (match x with
           | All2_fold_nil -> All_nil
           | All2_fold_cons (_, _, _, _, _, _) ->
             assert false (* absurd case *))
        | Coq_cons (_, _) -> assert false (* absurd case *))
     | Coq_cons (_, _) ->
       (match ls3 with
        | Coq_nil -> assert false (* absurd case *)
        | Coq_cons (_, _) ->
          (match x with
           | All2_fold_nil -> assert false (* absurd case *)
           | All2_fold_cons (_, _, _, _, _, x0) ->
             (match x0 with
              | All_nil -> All_nil
              | All_cons (_, _, _, _) -> assert false (* absurd case *)))))
  | Coq_cons (y, l0) ->
    (match ls2 with
     | Coq_nil ->
       (match ls3 with
        | Coq_nil ->
          (match x with
           | All2_fold_nil ->
             All_cons (y, l0, All2_fold_nil,
               (coq_All_refl l0 (fun _ -> All2_fold_nil)))
           | All2_fold_cons (_, _, _, _, _, _) ->
             assert false (* absurd case *))
        | Coq_cons (_, _) -> assert false (* absurd case *))
     | Coq_cons (a, l1) ->
       (match ls3 with
        | Coq_nil -> assert false (* absurd case *)
        | Coq_cons (a0, l2) ->
          (match x with
           | All2_fold_nil -> assert false (* absurd case *)
           | All2_fold_cons (_, _, _, _, x0, x1) ->
             (match x1 with
              | All_nil -> assert false (* absurd case *)
              | All_cons (_, _, x2, x3) ->
                All_cons (y, l0, (All2_fold_cons (a, a0, l1, l2,
                  (coq_All2_fold_impl l1 l2 x0 (fun _ _ _ _ x4 ->
                    match x4 with
                    | All_nil -> assert false (* absurd case *)
                    | All_cons (_, _, x5, _) -> x5)), x2)),
                  (coq_All_impl l0
                    (coq_All_prod l0
                      (coq_All2_fold_All_swap l0 l1 l2
                        (coq_All2_fold_impl l1 l2 x0 (fun _ _ _ _ x4 ->
                          match x4 with
                          | All_nil -> assert false (* absurd case *)
                          | All_cons (_, _, _, x5) -> x5))) x3) (fun _ x4 ->
                    let Coq_pair (y0, y1) = x4 in
                    All2_fold_cons (a, a0, l1, l2, y0, y1))))))))

(** val coq_All_All2_fold_swap_sum :
    'a2 list -> 'a1 list -> 'a1 list -> ('a2, ('a1, 'a3) coq_All2_fold)
    coq_All -> (__, ('a1, ('a2, 'a3) coq_All) coq_All2_fold) sum **)

let rec coq_All_All2_fold_swap_sum l ls2 ls3 x =
  match l with
  | Coq_nil ->
    (match ls2 with
     | Coq_nil ->
       (match ls3 with
        | Coq_nil ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))
        | Coq_cons (_, _) ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *)))
     | Coq_cons (_, _) ->
       (match ls3 with
        | Coq_nil ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))
        | Coq_cons (_, _) ->
          (match x with
           | All_nil -> Coq_inl __
           | All_cons (_, _, _, _) -> assert false (* absurd case *))))
  | Coq_cons (y, l0) ->
    (match ls2 with
     | Coq_nil ->
       (match ls3 with
        | Coq_nil ->
          (match x with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, x0, _) ->
             (match x0 with
              | All2_fold_nil -> Coq_inr All2_fold_nil
              | All2_fold_cons (_, _, _, _, _, _) ->
                assert false (* absurd case *)))
        | Coq_cons (_, _) -> assert false (* absurd case *))
     | Coq_cons (a, l1) ->
       (match ls3 with
        | Coq_nil -> assert false (* absurd case *)
        | Coq_cons (a0, l2) ->
          (match x with
           | All_nil -> assert false (* absurd case *)
           | All_cons (_, _, x0, x1) ->
             (match x0 with
              | All2_fold_nil -> assert false (* absurd case *)
              | All2_fold_cons (_, _, _, _, x2, x3) ->
                Coq_inr (All2_fold_cons (a, a0, l1, l2,
                  (coq_All2_fold_impl l1 l2
                    (coq_All2_fold_prod l1 l2 x2
                      (let s =
                         coq_All_All2_fold_swap_sum l0 l1 l2
                           (coq_All_impl l0 x1 (fun _ x4 ->
                             match x4 with
                             | All2_fold_nil -> assert false (* absurd case *)
                             | All2_fold_cons (_, _, _, _, x5, _) -> x5))
                       in
                       match s with
                       | Coq_inl _ ->
                         (match x1 with
                          | All_nil ->
                            coq_All2_fold_impl l1 l2 x2 (fun _ _ _ _ _ ->
                              All_nil)
                          | All_cons (_, _, _, _) ->
                            assert false (* absurd case *))
                       | Coq_inr a1 -> a1)) (fun _ _ _ _ x4 ->
                    let Coq_pair (y0, y1) = x4 in All_cons (y, l0, y0, y1))),
                  (All_cons (y, l0, x3,
                  (coq_All_impl l0 x1 (fun _ x4 ->
                    match x4 with
                    | All2_fold_nil -> assert false (* absurd case *)
                    | All2_fold_cons (_, _, _, _, _, x5) -> x5))))))))))

(** val coq_All_All2_fold_swap :
    'a2 list -> 'a1 list -> 'a1 list -> ('a2, ('a1, 'a3) coq_All2_fold)
    coq_All -> ('a1, ('a2, 'a3) coq_All) coq_All2_fold **)

let coq_All_All2_fold_swap ls1 ls2 ls3 x =
  match ls1 with
  | Coq_nil ->
    coq_All2_fold_from_nth_error ls2 ls3 (fun _ _ _ _ _ _ -> All_nil)
  | Coq_cons (b, l) ->
    let rec f l0 ls4 ls5 x0 =
      match l0 with
      | Coq_nil ->
        (match ls4 with
         | Coq_nil ->
           (match ls5 with
            | Coq_nil ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_fold_nil ->
                    (match x2 with
                     | All_nil -> All2_fold_nil
                     | All_cons (_, _, _, _) -> assert false (* absurd case *))
                  | All2_fold_cons (_, _, _, _, _, _) ->
                    assert false (* absurd case *)))
            | Coq_cons (_, _) -> assert false (* absurd case *))
         | Coq_cons (a, l1) ->
           (match ls5 with
            | Coq_nil -> assert false (* absurd case *)
            | Coq_cons (a0, l2) ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_fold_nil -> assert false (* absurd case *)
                  | All2_fold_cons (_, _, _, _, x3, x4) ->
                    (match x2 with
                     | All_nil ->
                       All2_fold_cons (a, a0, l1, l2,
                         (coq_All2_fold_impl l1 l2 x3 (fun _ _ _ _ x5 ->
                           All_cons (b, Coq_nil, x5, All_nil))), (All_cons
                         (b, Coq_nil, x4, All_nil)))
                     | All_cons (_, _, _, _) -> assert false (* absurd case *))))))
      | Coq_cons (y, l1) ->
        (match ls4 with
         | Coq_nil ->
           (match ls5 with
            | Coq_nil ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_fold_nil ->
                    (match x2 with
                     | All_nil -> assert false (* absurd case *)
                     | All_cons (_, _, x3, _) ->
                       (match x3 with
                        | All2_fold_nil -> All2_fold_nil
                        | All2_fold_cons (_, _, _, _, _, _) ->
                          assert false (* absurd case *)))
                  | All2_fold_cons (_, _, _, _, _, _) ->
                    assert false (* absurd case *)))
            | Coq_cons (_, _) -> assert false (* absurd case *))
         | Coq_cons (a, l2) ->
           (match ls5 with
            | Coq_nil -> assert false (* absurd case *)
            | Coq_cons (a0, l3) ->
              (match x0 with
               | All_nil -> assert false (* absurd case *)
               | All_cons (_, _, x1, x2) ->
                 (match x1 with
                  | All2_fold_nil -> assert false (* absurd case *)
                  | All2_fold_cons (_, _, _, _, x3, x4) ->
                    (match x2 with
                     | All_nil -> assert false (* absurd case *)
                     | All_cons (_, _, x5, x6) ->
                       (match x5 with
                        | All2_fold_nil -> assert false (* absurd case *)
                        | All2_fold_cons (_, _, _, _, x7, x8) ->
                          All2_fold_cons (a, a0, l2, l3,
                            (coq_All2_fold_impl l2 l3
                              (coq_All2_fold_prod l2 l3 x3
                                (coq_All2_fold_impl l2 l3
                                  (coq_All2_fold_prod l2 l3 x7
                                    (coq_All2_fold_impl l2 l3
                                      (f l1 l2 l3 (All_cons (b, l1, x3,
                                        (coq_All_impl l1 x6 (fun _ x9 ->
                                          match x9 with
                                          | All2_fold_nil ->
                                            assert false (* absurd case *)
                                          | All2_fold_cons (_, _, _, _, x10, _) ->
                                            x10))))) (fun _ _ _ _ x9 ->
                                      match x9 with
                                      | All_nil ->
                                        assert false (* absurd case *)
                                      | All_cons (_, _, _, x10) -> x10)))
                                  (fun _ _ _ _ x9 ->
                                  let Coq_pair (y0, y1) = x9 in
                                  All_cons (y, l1, y0, y1))))
                              (fun _ _ _ _ x9 ->
                              let Coq_pair (y0, y1) = x9 in
                              All_cons (b, (Coq_cons (y, l1)), y0, y1))),
                            (All_cons (b, (Coq_cons (y, l1)), x4, (All_cons
                            (y, l1, x8,
                            (coq_All_impl l1 x6 (fun _ x9 ->
                              match x9 with
                              | All2_fold_nil ->
                                assert false (* absurd case *)
                              | All2_fold_cons (_, _, _, _, _, x10) -> x10)))))))))))))
    in f l ls2 ls3 x

(** val coq_All2_map2_right :
    'a1 list -> 'a2 list -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2, 'a4) coq_All2
    -> ('a1, 'a3, 'a4) coq_All2 **)

let rec coq_All2_map2_right _ _ f = function
| All2_nil -> All2_nil
| All2_cons (x0, y, l, l', y0, a) ->
  All2_cons (x0, (f x0 y), l, (map2 f l l'), y0,
    (coq_All2_map2_right l l' f a))

(** val coq_All2i_map2_right :
    nat -> 'a1 list -> 'a2 list -> ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2, 'a4)
    coq_All2i -> ('a1, 'a3, 'a4) coq_All2i **)

let rec coq_All2i_map2_right n _ _ f = function
| All2i_nil -> All2i_nil
| All2i_cons (x0, y, l, r, y0, a) ->
  All2i_cons (x0, (f x0 y), l, (map2 f l r), y0,
    (coq_All2i_map2_right (S n) l r f a))

(** val coq_All2_map2_right_inv :
    ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> ('a1, 'a3, 'a4) coq_All2
    -> ('a1, 'a2, 'a4) coq_All2 **)

let coq_All2_map2_right_inv g l l' x =
  let _evar_0_ = fun __top_assumption_ ->
    let _evar_0_ = fun _ -> All2_nil in
    let _evar_0_0 = fun _ _ _ -> assert false (* absurd case *) in
    (fun _ ->
    match __top_assumption_ with
    | Coq_nil -> _evar_0_
    | Coq_cons (a, l0) -> (fun x0 -> _evar_0_0 a l0 x0))
  in
  let _evar_0_0 = fun x0 xs ih __top_assumption_ ->
    let _evar_0_0 = fun _ -> assert false (* absurd case *) in
    let _evar_0_1 = fun y ys z ->
      let z0 = ((Coq_cons (x0, xs)),(Coq_cons ((g x0 y), (map2 g xs ys)))),z
      in
      let z2 = let _,pr2 = z0 in pr2 in
      (match z2 with
       | All2_nil -> assert false (* absurd case *)
       | All2_cons (_, _, _, _, r, a) ->
         All2_cons (x0, y, xs, ys, r, (ih ys __ a)))
    in
    (fun _ ->
    match __top_assumption_ with
    | Coq_nil -> _evar_0_0
    | Coq_cons (a, l0) -> (fun z -> _evar_0_1 a l0 z))
  in
  let rec f = function
  | Coq_nil -> _evar_0_
  | Coq_cons (y, l1) -> _evar_0_0 y l1 (f l1)
  in f l l' __ x

(** val coq_All2i_Alli_mix_left :
    nat -> 'a1 list -> 'a2 list -> ('a1, 'a3) coq_Alli -> ('a1, 'a2, 'a4)
    coq_All2i -> ('a1, 'a2, ('a3, 'a4) prod) coq_All2i **)

let coq_All2i_Alli_mix_left k l l' _Hyp_ h =
  let _evar_0_ = fun n q ->
    let q0 = (n,Coq_nil),q in
    let q2 = let _,pr2 = q0 in pr2 in
    (match q2 with
     | Alli_nil -> All2i_nil
     | Alli_cons (_, _, _, _) -> assert false (* absurd case *))
  in
  let _evar_0_0 = fun n x y xs ys r _ ih q ->
    let q0 = (n,(Coq_cons (x, xs))),q in
    let q2 = let _,pr2 = q0 in pr2 in
    (match q2 with
     | Alli_nil -> assert false (* absurd case *)
     | Alli_cons (_, _, q1, a) ->
       All2i_cons (x, y, xs, ys, (Coq_pair (q1, r)), (ih a)))
  in
  let rec f n _ _ = function
  | All2i_nil -> _evar_0_ n
  | All2i_cons (x, y, l0, r, y0, a0) ->
    _evar_0_0 n x y l0 r y0 a0 (f (S n) l0 r a0)
  in f k l l' h _Hyp_

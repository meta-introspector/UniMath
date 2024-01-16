open CRelationClasses
open Datatypes
open Relation
open Specif

(** val iffT_l : ('a1, 'a2) iffT -> 'a1 -> 'a2 **)

let iffT_l =
  fst

type ('a, 'b, 'r) on_Trel = 'r

(** val flip_Reflexive :
    ('a1, 'a2) coq_Reflexive -> ('a1, 'a2) coq_Reflexive **)

let flip_Reflexive =
  reflexivity

(** val flip_Symmetric :
    ('a1, 'a2) coq_Symmetric -> ('a1, 'a2) coq_Symmetric **)

let flip_Symmetric hR x y =
  symmetry hR y x

(** val flip_Transitive :
    ('a1, 'a2) coq_Transitive -> ('a1, 'a2) coq_Transitive **)

let flip_Transitive hR x y z xy yz =
  hR z y x yz xy

type ('a, 'r, 's) commutes =
  'a -> 'a -> 'a -> 'r -> 's -> ('a, ('s, 'r) prod) sigT

(** val clos_t_rt :
    'a1 -> 'a1 -> ('a1, 'a2) trans_clos -> ('a1, 'a2) clos_refl_trans **)

let rec clos_t_rt x _ = function
| Coq_t_step (y, r) -> Coq_rt_step (y, r)
| Coq_t_trans (y, z, t0, t1) ->
  Coq_rt_trans (y, z, (clos_t_rt x y t0), (clos_t_rt y z t1))

(** val clos_rt_monotone :
    ('a1, 'a2, 'a3) subrelation -> ('a1, ('a1, 'a2) clos_refl_trans, ('a1,
    'a3) clos_refl_trans) subrelation **)

let rec clos_rt_monotone incls x _ = function
| Coq_rt_step (y, r) -> Coq_rt_step (y, (incls x y r))
| Coq_rt_refl -> Coq_rt_refl
| Coq_rt_trans (y, z, c, c0) ->
  Coq_rt_trans (y, z, (clos_rt_monotone incls x y c),
    (clos_rt_monotone incls y z c0))

(** val relation_equivalence_inclusion :
    ('a1, 'a2, 'a3) subrelation -> ('a1, 'a3, 'a2) subrelation -> ('a1, 'a2,
    'a3) relation_equivalence **)

let relation_equivalence_inclusion x x0 x1 y =
  Coq_pair ((fun x2 -> x x1 y x2), (fun x2 -> x0 x1 y x2))

(** val clos_rt_disjunction_left :
    ('a1, ('a1, 'a2) clos_refl_trans, ('a1, ('a1, 'a2, 'a3)
    relation_disjunction) clos_refl_trans) subrelation **)

let clos_rt_disjunction_left x =
  clos_rt_monotone (fun _ _ h -> Coq_inl h) x

(** val clos_rt_disjunction_right :
    ('a1, ('a1, 'a3) clos_refl_trans, ('a1, ('a1, 'a2, 'a3)
    relation_disjunction) clos_refl_trans) subrelation **)

let clos_rt_disjunction_right x =
  clos_rt_monotone (fun _ _ h -> Coq_inr h) x

(** val clos_rt_trans : ('a1, ('a1, 'a2) clos_refl_trans) coq_Transitive **)

let clos_rt_trans _ y z h h' =
  Coq_rt_trans (y, z, h, h')

(** val clos_rt_refl : ('a1, ('a1, 'a2) clos_refl_trans) coq_Reflexive **)

let clos_rt_refl _ =
  Coq_rt_refl

(** val clos_refl_trans_prod_l :
    ('a1 -> 'a1 -> 'a2 -> 'a3 -> 'a4) -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a3)
    clos_refl_trans -> (('a1, 'a2) prod, 'a4) clos_refl_trans **)

let rec clos_refl_trans_prod_l x x0 _ b = function
| Coq_rt_step (y, r) -> Coq_rt_step ((Coq_pair (y, b)), (x x0 y b r))
| Coq_rt_refl -> Coq_rt_refl
| Coq_rt_trans (y, z, c, c0) ->
  Coq_rt_trans ((Coq_pair (y, b)), (Coq_pair (z, b)),
    (clos_refl_trans_prod_l x x0 y b c), (clos_refl_trans_prod_l x y z b c0))

(** val clos_refl_trans_prod_r :
    'a1 -> ('a2 -> 'a2 -> 'a3 -> 'a4) -> 'a2 -> 'a2 -> ('a2, 'a3)
    clos_refl_trans -> (('a1, 'a2) prod, 'a4) clos_refl_trans **)

let rec clos_refl_trans_prod_r a x x0 _ = function
| Coq_rt_step (y, r) -> Coq_rt_step ((Coq_pair (a, y)), (x x0 y r))
| Coq_rt_refl -> Coq_rt_refl
| Coq_rt_trans (y, z, c, c0) ->
  Coq_rt_trans ((Coq_pair (a, y)), (Coq_pair (a, z)),
    (clos_refl_trans_prod_r a x x0 y c), (clos_refl_trans_prod_r a x y z c0))

(** val clos_rt_t_incl :
    ('a1, 'a2) coq_Reflexive -> ('a1, ('a1, 'a2) clos_refl_trans, ('a1, 'a2)
    trans_clos) subrelation **)

let rec clos_rt_t_incl h x _ = function
| Coq_rt_step (y, r) -> Coq_t_step (y, r)
| Coq_rt_refl -> Coq_t_step (x, (h x))
| Coq_rt_trans (y, z, c, c0) ->
  Coq_t_trans (y, z, (clos_rt_t_incl h x y c), (clos_rt_t_incl h y z c0))

(** val clos_t_rt_incl :
    ('a1, 'a2) coq_Reflexive -> ('a1, ('a1, 'a2) trans_clos, ('a1, 'a2)
    clos_refl_trans) subrelation **)

let rec clos_t_rt_incl h x _ = function
| Coq_t_step (y, r) -> Coq_rt_step (y, r)
| Coq_t_trans (y, z, t, t0) ->
  Coq_rt_trans (y, z, (clos_t_rt_incl h x y t), (clos_t_rt_incl h y z t0))

(** val clos_t_rt_equiv :
    ('a1, 'a2) coq_Reflexive -> ('a1, ('a1, 'a2) trans_clos, ('a1, 'a2)
    clos_refl_trans) relation_equivalence **)

let clos_t_rt_equiv h =
  relation_equivalence_inclusion (clos_t_rt_incl h) (clos_rt_t_incl h)

(** val relation_disjunction_refl_l :
    ('a1, 'a2) coq_Reflexive -> ('a1, ('a1, 'a2, 'a3) relation_disjunction)
    coq_Reflexive **)

let relation_disjunction_refl_l hR x =
  Coq_inl (hR x)

(** val relation_disjunction_refl_r :
    ('a1, 'a3) coq_Reflexive -> ('a1, ('a1, 'a2, 'a3) relation_disjunction)
    coq_Reflexive **)

let relation_disjunction_refl_r hR x =
  Coq_inr (hR x)

(** val clos_rt_trans_Symmetric :
    ('a1, 'a2) coq_Symmetric -> ('a1, ('a1, 'a2) clos_refl_trans)
    coq_Symmetric **)

let rec clos_rt_trans_Symmetric x x0 _ = function
| Coq_rt_step (y, r) -> Coq_rt_step (x0, (x x0 y r))
| Coq_rt_refl -> Coq_rt_refl
| Coq_rt_trans (y, z, c, c0) ->
  clos_rt_trans z y x0 (clos_rt_trans_Symmetric x y z c0)
    (clos_rt_trans_Symmetric x x0 y c)

type ('a, 'r) clos_sym = ('a, 'r, 'r) relation_disjunction

(** val clos_sym_Symmetric : ('a1, ('a1, 'a2) clos_sym) coq_Symmetric **)

let clos_sym_Symmetric _ _ = function
| Coq_inl r -> Coq_inr r
| Coq_inr f -> Coq_inl f

(** val clos_refl_sym_trans_Symmetric :
    ('a1, ('a1, 'a2) clos_refl_sym_trans) coq_Symmetric **)

let clos_refl_sym_trans_Symmetric x x0 x1 =
  Coq_rst_sym (x, x0, x1)

(** val clos_refl_sym_trans_Reflexive :
    ('a1, ('a1, 'a2) clos_refl_sym_trans) coq_Reflexive **)

let clos_refl_sym_trans_Reflexive x =
  Coq_rst_refl x

(** val clos_refl_sym_trans_Transitive :
    ('a1, ('a1, 'a2) clos_refl_sym_trans) coq_Transitive **)

let clos_refl_sym_trans_Transitive x x0 x1 x2 x3 =
  Coq_rst_trans (x, x0, x1, x2, x3)

(** val relation_disjunction_Symmetric :
    ('a1, 'a2) coq_Symmetric -> ('a1, 'a3) coq_Symmetric -> ('a1, ('a1, 'a2,
    'a3) relation_disjunction) coq_Symmetric **)

let relation_disjunction_Symmetric hR hS x y = function
| Coq_inl r -> Coq_inl (hR x y r)
| Coq_inr s -> Coq_inr (hS x y s)

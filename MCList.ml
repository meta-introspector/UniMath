open CRelationClasses
open Classes
open Datatypes
open List
open Nat
open ReflectEq
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fold_left_i_aux :
    ('a1 -> nat -> 'a2 -> 'a1) -> nat -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left_i_aux f n0 l a0 =
  match l with
  | Coq_nil -> a0
  | Coq_cons (b, l0) -> fold_left_i_aux f (S n0) l0 (f a0 n0 b)

(** val fold_left_i : ('a1 -> nat -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let fold_left_i f =
  fold_left_i_aux f O

(** val mapi_rec : (nat -> 'a1 -> 'a2) -> 'a1 list -> nat -> 'a2 list **)

let rec mapi_rec f l n =
  match l with
  | Coq_nil -> Coq_nil
  | Coq_cons (hd, tl) -> Coq_cons ((f n hd), (mapi_rec f tl (S n)))

(** val mapi : (nat -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let mapi f l =
  mapi_rec f l O

(** val safe_nth_obligation_1 : 'a1 list -> nat -> 'a1 **)

let safe_nth_obligation_1 _ _ =
  assert false (* absurd case *)

(** val safe_nth : 'a1 list -> nat -> 'a1 **)

let rec safe_nth l n =
  match l with
  | Coq_nil -> safe_nth_obligation_1 l n
  | Coq_cons (hd, tl) -> (match n with
                          | O -> hd
                          | S n0 -> safe_nth tl n0)

(** val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2 f l l' =
  match l with
  | Coq_nil -> Coq_nil
  | Coq_cons (hd, tl) ->
    (match l' with
     | Coq_nil -> Coq_nil
     | Coq_cons (hd', tl') -> Coq_cons ((f hd hd'), (map2 f tl tl')))

(** val rev : 'a1 list -> 'a1 list **)

let rev l =
  let rec aux l0 acc =
    match l0 with
    | Coq_nil -> acc
    | Coq_cons (x, l1) -> aux l1 (Coq_cons (x, acc))
  in aux l Coq_nil

(** val rev_map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rev_map f l =
  let rec aux l0 acc =
    match l0 with
    | Coq_nil -> acc
    | Coq_cons (x, l1) -> aux l1 (Coq_cons ((f x), acc))
  in aux l Coq_nil

(** val rev_list_ind :
    'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let rec rev_list_ind x x0 = function
| Coq_nil -> x
| Coq_cons (y, l0) -> x0 y l0 (rev_list_ind x x0 l0)

(** val rev_ind :
    'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let rev_ind x x0 l =
  rev_list_ind x (fun a l0 x1 -> x0 a (List.rev l0) x1) (List.rev l)

type 'a nth_error_Spec =
| Coq_nth_error_Spec_Some of 'a
| Coq_nth_error_Spec_None

(** val nth_error_Spec_rect :
    'a1 list -> nat -> ('a1 -> __ -> __ -> 'a2) -> (__ -> 'a2) -> 'a1 option
    -> 'a1 nth_error_Spec -> 'a2 **)

let nth_error_Spec_rect _ _ f f0 _ = function
| Coq_nth_error_Spec_Some x -> f x __ __
| Coq_nth_error_Spec_None -> f0 __

(** val nth_error_Spec_rec :
    'a1 list -> nat -> ('a1 -> __ -> __ -> 'a2) -> (__ -> 'a2) -> 'a1 option
    -> 'a1 nth_error_Spec -> 'a2 **)

let nth_error_Spec_rec _ _ f f0 _ = function
| Coq_nth_error_Spec_Some x -> f x __ __
| Coq_nth_error_Spec_None -> f0 __

(** val nth_error_Some' : 'a1 list -> nat -> (('a1, __) sigT, __) iffT **)

let rec nth_error_Some' l n =
  match l with
  | Coq_nil ->
    Coq_pair ((Obj.magic __), (fun _ -> assert false (* absurd case *)))
  | Coq_cons (y, l0) ->
    (match n with
     | O -> Coq_pair ((Obj.magic __), (fun _ -> Coq_existT (y, __)))
     | S n0 ->
       let i = nth_error_Some' l0 n0 in
       let Coq_pair (_, x) = i in
       let s = Obj.magic x in Obj.magic (Coq_pair (__, (fun _ -> s __))))

(** val nth_error_spec : 'a1 list -> nat -> 'a1 nth_error_Spec **)

let nth_error_spec l n =
  let o = nth_error l n in
  (match o with
   | Some a -> Coq_nth_error_Spec_Some a
   | None -> Coq_nth_error_Spec_None)

(** val chop : nat -> 'a1 list -> ('a1 list, 'a1 list) prod **)

let rec chop n l =
  match n with
  | O -> Coq_pair (Coq_nil, l)
  | S n0 ->
    (match l with
     | Coq_nil -> Coq_pair (Coq_nil, Coq_nil)
     | Coq_cons (hd, tl) ->
       let Coq_pair (l0, r) = chop n0 tl in Coq_pair ((Coq_cons (hd, l0)), r))

(** val split_at_aux :
    nat -> 'a1 list -> 'a1 list -> ('a1 list, 'a1 list) prod **)

let rec split_at_aux n acc l =
  match n with
  | O -> Coq_pair ((List.rev acc), l)
  | S n' ->
    (match l with
     | Coq_nil -> Coq_pair ((List.rev acc), Coq_nil)
     | Coq_cons (hd, l') -> split_at_aux n' (Coq_cons (hd, acc)) l')

(** val split_at : nat -> 'a1 list -> ('a1 list, 'a1 list) prod **)

let split_at n l =
  split_at_aux n Coq_nil l

(** val list_rect_rev :
    'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2 **)

let list_rect_rev h1 h2 l =
  let l0 = rev l in
  let rec f = function
  | Coq_nil -> h1
  | Coq_cons (y, l2) -> h2 y (rev l2) (f l2)
  in f l0

(** val list_size : ('a1 -> nat) -> 'a1 list -> nat **)

let rec list_size size = function
| Coq_nil -> O
| Coq_cons (a, v) -> S (add (size a) (list_size size v))

(** val unfold : nat -> (nat -> 'a1) -> 'a1 list **)

let rec unfold n f =
  match n with
  | O -> Coq_nil
  | S n0 -> app (unfold n0 f) (Coq_cons ((f n0), Coq_nil))

(** val nth_nth_error' : nat -> 'a1 list -> 'a1 -> 'a1 -> (__, __) sum **)

let nth_nth_error' i l _ v =
  let _evar_0_ = fun _top_assumption_ ->
    let _evar_0_ = fun _ -> Coq_inr __ in
    let _evar_0_0 = fun _ _ -> Coq_inr __ in
    (fun v0 _ ->
    match _top_assumption_ with
    | O -> _evar_0_ v0
    | S n -> _evar_0_0 n v0)
  in
  let _evar_0_0 = fun _ _ iH _top_assumption_ ->
    let _evar_0_0 = fun _ -> Coq_inl __ in
    (match _top_assumption_ with
     | O -> (fun _v_ _ -> _evar_0_0 _v_)
     | S n -> iH n)
  in
  let rec f = function
  | Coq_nil -> _evar_0_
  | Coq_cons (y, l1) -> _evar_0_0 y l1 (f l1)
  in f l i v __

(** val rev_case : 'a2 -> ('a1 list -> 'a1 -> 'a2) -> 'a1 list -> 'a2 **)

let rev_case x x0 l =
  rev_ind x (fun x1 l0 _ -> x0 l0 x1) l

(** val map2i_rec :
    (nat -> 'a1 -> 'a2 -> 'a3) -> nat -> 'a1 list -> 'a2 list -> 'a3 list **)

let rec map2i_rec f i l l' =
  match l with
  | Coq_nil -> Coq_nil
  | Coq_cons (hd, tl) ->
    (match l' with
     | Coq_nil -> Coq_nil
     | Coq_cons (hd', tl') ->
       Coq_cons ((f i hd hd'), (map2i_rec f (S i) tl tl')))

(** val map2i :
    (nat -> 'a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)

let map2i f =
  map2i_rec f O

(** val map_In : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list **)

let rec map_In l f =
  match l with
  | Coq_nil -> Coq_nil
  | Coq_cons (y, l0) -> Coq_cons ((f y __), (map_In l0 (fun x _ -> f x __)))

type ('a, 'b) map_In_graph =
| Coq_map_In_graph_equation_1 of ('a -> __ -> 'b)
| Coq_map_In_graph_equation_2 of 'a * 'a list * ('a -> __ -> 'b)
   * ('a, 'b) map_In_graph

(** val map_In_graph_rect :
    (__ -> __ -> (__ -> __ -> __) -> 'a1) -> (__ -> __ -> __ -> __ list ->
    (__ -> __ -> __) -> (__, __) map_In_graph -> 'a1 -> 'a1) -> 'a2 list ->
    ('a2 -> __ -> 'a3) -> 'a3 list -> ('a2, 'a3) map_In_graph -> 'a1 **)

let rec map_In_graph_rect f f0 _ _ _ = function
| Coq_map_In_graph_equation_1 f1 -> Obj.magic f __ __ f1
| Coq_map_In_graph_equation_2 (x, xs, f1, hind) ->
  Obj.magic f0 __ __ x xs f1 hind
    (map_In_graph_rect f f0 xs (fun x0 _ -> f1 x0 __)
      (map_In xs (fun x0 _ -> f1 x0 __)) hind)

(** val map_In_graph_correct :
    'a1 list -> ('a1 -> __ -> 'a2) -> ('a1, 'a2) map_In_graph **)

let rec map_In_graph_correct l f =
  match l with
  | Coq_nil -> Coq_map_In_graph_equation_1 f
  | Coq_cons (y, l0) ->
    Coq_map_In_graph_equation_2 (y, l0, f,
      (map_In_graph_correct l0 (fun x _ -> f x __)))

(** val map_In_elim :
    (__ -> __ -> (__ -> __ -> __) -> 'a1) -> (__ -> __ -> __ -> __ list ->
    (__ -> __ -> __) -> 'a1 -> 'a1) -> 'a2 list -> ('a2 -> __ -> 'a3) -> 'a1 **)

let map_In_elim f f0 l f1 =
  let rec f2 _ _ _ = function
  | Coq_map_In_graph_equation_1 f3 -> Obj.magic f __ __ f3
  | Coq_map_In_graph_equation_2 (x, xs, f3, hind) ->
    Obj.magic f0 __ __ x xs f3
      (f2 xs (fun x0 _ -> f3 x0 __) (map_In xs (fun x0 _ -> f3 x0 __)) hind)
  in f2 l f1 (map_In l f1) (map_In_graph_correct l f1)

(** val coq_FunctionalElimination_map_In :
    (__ -> __ -> (__ -> __ -> __) -> __) -> (__ -> __ -> __ -> __ list -> (__
    -> __ -> __) -> __ -> __) -> __ list -> (__ -> __ -> __) -> __ **)

let coq_FunctionalElimination_map_In =
  map_In_elim

(** val coq_FunctionalInduction_map_In :
    (__ -> __ -> __ list -> (__ -> __ -> __) -> __ list)
    coq_FunctionalInduction **)

let coq_FunctionalInduction_map_In =
  Obj.magic (fun _ _ -> map_In_graph_correct)

(** val split_prefix_clause_3_clause_1 :
    ('a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1 list) prod) ->
    'a1 -> 'a1 list -> 'a1 -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1
    list) prod -> (('a1 list, 'a1 list) prod, 'a1 list) prod **)

let split_prefix_clause_3_clause_1 _ a1 _ _ _ = function
| Coq_pair (p, l) ->
  let Coq_pair (l0, l1) = p in
  Coq_pair ((Coq_pair ((Coq_cons (a1, l0)), l1)), l)

(** val split_prefix_clause_3 :
    ('a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1 list) prod) ->
    'a1 -> 'a1 list -> 'a1 -> bool -> 'a1 list -> (('a1 list, 'a1 list) prod,
    'a1 list) prod **)

let split_prefix_clause_3 split_prefix0 a1 l1 a2 refine l2 =
  match refine with
  | Coq_true ->
    let Coq_pair (p, l) = split_prefix0 l1 l2 in
    let Coq_pair (l0, l3) = p in
    Coq_pair ((Coq_pair ((Coq_cons (a1, l0)), l3)), l)
  | Coq_false ->
    Coq_pair ((Coq_pair (Coq_nil, (Coq_cons (a1, l1)))), (Coq_cons (a2, l2)))

(** val split_prefix :
    'a1 coq_ReflectEq -> 'a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod,
    'a1 list) prod **)

let rec split_prefix h l1 l2 =
  match l1 with
  | Coq_nil -> Coq_pair ((Coq_pair (Coq_nil, Coq_nil)), l2)
  | Coq_cons (a, l) ->
    (match l2 with
     | Coq_nil -> Coq_pair ((Coq_pair (Coq_nil, (Coq_cons (a, l)))), Coq_nil)
     | Coq_cons (a0, l0) ->
       (match eqb h a a0 with
        | Coq_true ->
          let Coq_pair (p, l3) = split_prefix h l l0 in
          let Coq_pair (l4, l5) = p in
          Coq_pair ((Coq_pair ((Coq_cons (a, l4)), l5)), l3)
        | Coq_false ->
          Coq_pair ((Coq_pair (Coq_nil, (Coq_cons (a, l)))), (Coq_cons (a0,
            l0)))))

type 'a split_prefix_graph =
| Coq_split_prefix_graph_equation_1 of 'a list
| Coq_split_prefix_graph_equation_2 of 'a * 'a list
| Coq_split_prefix_graph_refinement_3 of 'a * 'a list * 'a * 'a list
   * 'a split_prefix_clause_3_graph
and 'a split_prefix_clause_3_graph =
| Coq_split_prefix_clause_3_graph_refinement_1 of 'a * 'a list * 'a * 
   'a list * 'a split_prefix_graph * 'a split_prefix_clause_3_clause_1_graph
| Coq_split_prefix_clause_3_graph_equation_2 of 'a * 'a list * 'a * 'a list
and 'a split_prefix_clause_3_clause_1_graph =
| Coq_split_prefix_clause_3_clause_1_graph_equation_1 of 'a * 'a list * 
   'a * 'a list * 'a list * 'a list * 'a list

(** val split_prefix_clause_3_clause_1_graph_mut :
    'a1 coq_ReflectEq -> ('a1 list -> 'a2) -> ('a1 -> 'a1 list -> 'a2) ->
    ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_clause_3_graph ->
    'a3 -> 'a2) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1
    split_prefix_graph -> 'a2 -> 'a1 split_prefix_clause_3_clause_1_graph ->
    'a4 -> 'a3) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1
    list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> 'a4) ->
    'a1 -> 'a1 list -> 'a1 -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1
    list) prod -> (('a1 list, 'a1 list) prod, 'a1 list) prod -> 'a1
    split_prefix_clause_3_clause_1_graph -> 'a4 **)

let split_prefix_clause_3_clause_1_graph_mut _ _ _ _ _ _ f4 _ _ _ _ _ _ = function
| Coq_split_prefix_clause_3_clause_1_graph_equation_1 (a1, l1, a2, l2,
                                                       prefix, l1', l2') ->
  f4 a1 l1 a2 l2 prefix l1' l2'

(** val split_prefix_clause_3_graph_mut :
    'a1 coq_ReflectEq -> ('a1 list -> 'a2) -> ('a1 -> 'a1 list -> 'a2) ->
    ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_clause_3_graph ->
    'a3 -> 'a2) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1
    split_prefix_graph -> 'a2 -> 'a1 split_prefix_clause_3_clause_1_graph ->
    'a4 -> 'a3) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1
    list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> 'a4) ->
    'a1 -> 'a1 list -> 'a1 -> bool -> 'a1 list -> (('a1 list, 'a1 list) prod,
    'a1 list) prod -> 'a1 split_prefix_clause_3_graph -> 'a3 **)

let split_prefix_clause_3_graph_mut h f f0 f1 f2 f3 f4 =
  let rec f5 _ _ _ = function
  | Coq_split_prefix_graph_equation_1 l2 -> f l2
  | Coq_split_prefix_graph_equation_2 (a, l) -> f0 a l
  | Coq_split_prefix_graph_refinement_3 (a1, l1, a2, l2, hind) ->
    f1 a1 l1 a2 l2 hind
      (f6 a1 l1 a2 (eqb h a1 a2) l2
        (match eqb h a1 a2 with
         | Coq_true ->
           let Coq_pair (p, l) = split_prefix h l1 l2 in
           let Coq_pair (l0, l3) = p in
           Coq_pair ((Coq_pair ((Coq_cons (a1, l0)), l3)), l)
         | Coq_false ->
           Coq_pair ((Coq_pair (Coq_nil, (Coq_cons (a1, l1)))), (Coq_cons
             (a2, l2)))) hind)
  and f6 _ _ _ _ _ _ = function
  | Coq_split_prefix_clause_3_graph_refinement_1 (a1, l1, a2, l2, hind, hind0) ->
    f2 a1 l1 a2 l2 hind (f5 l1 l2 (split_prefix h l1 l2) hind) hind0
      (f7 a1 l1 a2 l2 (split_prefix h l1 l2)
        (let Coq_pair (p, l) = split_prefix h l1 l2 in
         let Coq_pair (l0, l3) = p in
         Coq_pair ((Coq_pair ((Coq_cons (a1, l0)), l3)), l)) hind0)
  | Coq_split_prefix_clause_3_graph_equation_2 (a1, l1, a2, l2) ->
    f3 a1 l1 a2 l2
  and f7 _ _ _ _ _ _ = function
  | Coq_split_prefix_clause_3_clause_1_graph_equation_1 (a1, l1, a2, l2,
                                                         prefix, l1', l2') ->
    f4 a1 l1 a2 l2 prefix l1' l2'
  in f6

(** val split_prefix_graph_mut :
    'a1 coq_ReflectEq -> ('a1 list -> 'a2) -> ('a1 -> 'a1 list -> 'a2) ->
    ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_clause_3_graph ->
    'a3 -> 'a2) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1
    split_prefix_graph -> 'a2 -> 'a1 split_prefix_clause_3_clause_1_graph ->
    'a4 -> 'a3) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1
    list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> 'a4) ->
    'a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1 list) prod -> 'a1
    split_prefix_graph -> 'a2 **)

let split_prefix_graph_mut h f f0 f1 f2 f3 f4 =
  let rec f5 _ _ _ = function
  | Coq_split_prefix_graph_equation_1 l2 -> f l2
  | Coq_split_prefix_graph_equation_2 (a, l) -> f0 a l
  | Coq_split_prefix_graph_refinement_3 (a1, l1, a2, l2, hind) ->
    f1 a1 l1 a2 l2 hind
      (f6 a1 l1 a2 (eqb h a1 a2) l2
        (match eqb h a1 a2 with
         | Coq_true ->
           let Coq_pair (p, l) = split_prefix h l1 l2 in
           let Coq_pair (l0, l3) = p in
           Coq_pair ((Coq_pair ((Coq_cons (a1, l0)), l3)), l)
         | Coq_false ->
           Coq_pair ((Coq_pair (Coq_nil, (Coq_cons (a1, l1)))), (Coq_cons
             (a2, l2)))) hind)
  and f6 _ _ _ _ _ _ = function
  | Coq_split_prefix_clause_3_graph_refinement_1 (a1, l1, a2, l2, hind, hind0) ->
    f2 a1 l1 a2 l2 hind (f5 l1 l2 (split_prefix h l1 l2) hind) hind0
      (f7 a1 l1 a2 l2 (split_prefix h l1 l2)
        (let Coq_pair (p, l) = split_prefix h l1 l2 in
         let Coq_pair (l0, l3) = p in
         Coq_pair ((Coq_pair ((Coq_cons (a1, l0)), l3)), l)) hind0)
  | Coq_split_prefix_clause_3_graph_equation_2 (a1, l1, a2, l2) ->
    f3 a1 l1 a2 l2
  and f7 _ _ _ _ _ _ = function
  | Coq_split_prefix_clause_3_clause_1_graph_equation_1 (a1, l1, a2, l2,
                                                         prefix, l1', l2') ->
    f4 a1 l1 a2 l2 prefix l1' l2'
  in f5

(** val split_prefix_graph_rect :
    'a1 coq_ReflectEq -> ('a1 list -> 'a2) -> ('a1 -> 'a1 list -> 'a2) ->
    ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_clause_3_graph ->
    'a3 -> 'a2) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1
    split_prefix_graph -> 'a2 -> 'a1 split_prefix_clause_3_clause_1_graph ->
    'a4 -> 'a3) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1
    list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> 'a4) ->
    'a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1 list) prod -> 'a1
    split_prefix_graph -> 'a2 **)

let split_prefix_graph_rect =
  split_prefix_graph_mut

(** val split_prefix_graph_correct :
    'a1 coq_ReflectEq -> 'a1 list -> 'a1 list -> 'a1 split_prefix_graph **)

let rec split_prefix_graph_correct h l1 l2 =
  match l1 with
  | Coq_nil -> Coq_split_prefix_graph_equation_1 l2
  | Coq_cons (a, l) ->
    (match l2 with
     | Coq_nil -> Coq_split_prefix_graph_equation_2 (a, l)
     | Coq_cons (a0, l0) ->
       Coq_split_prefix_graph_refinement_3 (a, l, a0, l0,
         (let refine = eqb h a a0 in
          match refine with
          | Coq_true ->
            Coq_split_prefix_clause_3_graph_refinement_1 (a, l, a0, l0,
              (split_prefix_graph_correct h l l0),
              (let refine0 = split_prefix h l l0 in
               let Coq_pair (p, l3) = refine0 in
               let Coq_pair (l4, l5) = p in
               Coq_split_prefix_clause_3_clause_1_graph_equation_1 (a, l, a0,
               l0, l4, l5, l3)))
          | Coq_false ->
            Coq_split_prefix_clause_3_graph_equation_2 (a, l, a0, l0))))

(** val split_prefix_elim :
    'a1 coq_ReflectEq -> ('a1 list -> 'a2) -> ('a1 -> 'a1 list -> 'a2) ->
    ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> __ -> 'a2) -> ('a1 -> 'a1 list ->
    'a1 -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> __ -> 'a2 -> __ ->
    'a2) -> 'a1 list -> 'a1 list -> 'a2 **)

let split_prefix_elim h f f0 f3 f4 l1 l2 =
  split_prefix_graph_mut h f f0 (fun _ _ _ _ _ x -> x __)
    (fun _ _ _ _ _ x _ x0 -> x0 __ x) f3 f4 l1 l2 (split_prefix h l1 l2)
    (split_prefix_graph_correct h l1 l2)

(** val coq_FunctionalElimination_split_prefix :
    'a1 coq_ReflectEq -> ('a1 list -> __) -> ('a1 -> 'a1 list -> __) -> ('a1
    -> 'a1 list -> 'a1 -> 'a1 list -> __ -> __) -> ('a1 -> 'a1 list -> 'a1 ->
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> __ -> __ -> __ -> __) ->
    'a1 list -> 'a1 list -> __ **)

let coq_FunctionalElimination_split_prefix =
  split_prefix_elim

(** val coq_FunctionalInduction_split_prefix :
    'a1 coq_ReflectEq -> ('a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod,
    'a1 list) prod) coq_FunctionalInduction **)

let coq_FunctionalInduction_split_prefix h =
  Obj.magic split_prefix_graph_correct h

(** val split_suffix :
    'a1 coq_ReflectEq -> 'a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod,
    'a1 list) prod **)

let split_suffix h l1 l2 =
  let Coq_pair (p, l3) = split_prefix h (rev l1) (rev l2) in
  let Coq_pair (suffix, l4) = p in
  Coq_pair ((Coq_pair ((rev l4), (rev l3))), (rev suffix))

(** val forallb_InP : 'a1 list -> ('a1 -> __ -> bool) -> bool **)

let rec forallb_InP l h =
  match l with
  | Coq_nil -> Coq_true
  | Coq_cons (a, l0) ->
    (match h a __ with
     | Coq_true -> forallb_InP l0 (fun x _ -> h x __)
     | Coq_false -> Coq_false)

type 'a forallb_InP_graph =
| Coq_forallb_InP_graph_equation_1 of ('a -> __ -> bool)
| Coq_forallb_InP_graph_equation_2 of 'a * 'a list * ('a -> __ -> bool)
   * 'a forallb_InP_graph

(** val forallb_InP_graph_rect :
    (('a1 -> __ -> bool) -> 'a2) -> ('a1 -> 'a1 list -> ('a1 -> __ -> bool)
    -> 'a1 forallb_InP_graph -> 'a2 -> 'a2) -> 'a1 list -> ('a1 -> __ ->
    bool) -> bool -> 'a1 forallb_InP_graph -> 'a2 **)

let rec forallb_InP_graph_rect f f0 _ _ _ = function
| Coq_forallb_InP_graph_equation_1 h -> f h
| Coq_forallb_InP_graph_equation_2 (x, xs, h, hind) ->
  f0 x xs h hind
    (forallb_InP_graph_rect f f0 xs (fun x0 _ -> h x0 __)
      (forallb_InP xs (fun x0 _ -> h x0 __)) hind)

(** val forallb_InP_graph_correct :
    'a1 list -> ('a1 -> __ -> bool) -> 'a1 forallb_InP_graph **)

let rec forallb_InP_graph_correct l h =
  match l with
  | Coq_nil -> Coq_forallb_InP_graph_equation_1 h
  | Coq_cons (a, l0) ->
    Coq_forallb_InP_graph_equation_2 (a, l0, h,
      (forallb_InP_graph_correct l0 (fun x _ -> h x __)))

(** val forallb_InP_elim :
    (('a1 -> __ -> bool) -> 'a2) -> ('a1 -> 'a1 list -> ('a1 -> __ -> bool)
    -> 'a2 -> 'a2) -> 'a1 list -> ('a1 -> __ -> bool) -> 'a2 **)

let forallb_InP_elim f f0 l h =
  let rec f1 _ _ _ = function
  | Coq_forallb_InP_graph_equation_1 h0 -> f h0
  | Coq_forallb_InP_graph_equation_2 (x, xs, h0, hind) ->
    f0 x xs h0
      (f1 xs (fun x0 _ -> h0 x0 __) (forallb_InP xs (fun x0 _ -> h0 x0 __))
        hind)
  in f1 l h (forallb_InP l h) (forallb_InP_graph_correct l h)

(** val coq_FunctionalElimination_forallb_InP :
    (('a1 -> __ -> bool) -> __) -> ('a1 -> 'a1 list -> ('a1 -> __ -> bool) ->
    __ -> __) -> 'a1 list -> ('a1 -> __ -> bool) -> __ **)

let coq_FunctionalElimination_forallb_InP =
  forallb_InP_elim

(** val coq_FunctionalInduction_forallb_InP :
    ('a1 list -> ('a1 -> __ -> bool) -> bool) coq_FunctionalInduction **)

let coq_FunctionalInduction_forallb_InP =
  Obj.magic forallb_InP_graph_correct

(** val map_InP : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list **)

let rec map_InP l f =
  match l with
  | Coq_nil -> Coq_nil
  | Coq_cons (a, l0) -> Coq_cons ((f a __), (map_InP l0 (fun x _ -> f x __)))

type ('a, 'b) map_InP_graph =
| Coq_map_InP_graph_equation_1 of ('a -> __ -> 'b)
| Coq_map_InP_graph_equation_2 of 'a * 'a list * ('a -> __ -> 'b)
   * ('a, 'b) map_InP_graph

(** val map_InP_graph_rect :
    (('a1 -> __ -> 'a2) -> 'a3) -> ('a1 -> 'a1 list -> ('a1 -> __ -> 'a2) ->
    ('a1, 'a2) map_InP_graph -> 'a3 -> 'a3) -> 'a1 list -> ('a1 -> __ -> 'a2)
    -> 'a2 list -> ('a1, 'a2) map_InP_graph -> 'a3 **)

let rec map_InP_graph_rect f f0 _ _ _ = function
| Coq_map_InP_graph_equation_1 f1 -> f f1
| Coq_map_InP_graph_equation_2 (x, xs, f1, hind) ->
  f0 x xs f1 hind
    (map_InP_graph_rect f f0 xs (fun x0 _ -> f1 x0 __)
      (map_InP xs (fun x0 _ -> f1 x0 __)) hind)

(** val map_InP_graph_correct :
    'a1 list -> ('a1 -> __ -> 'a2) -> ('a1, 'a2) map_InP_graph **)

let rec map_InP_graph_correct l f =
  match l with
  | Coq_nil -> Coq_map_InP_graph_equation_1 f
  | Coq_cons (a, l0) ->
    Coq_map_InP_graph_equation_2 (a, l0, f,
      (map_InP_graph_correct l0 (fun x _ -> f x __)))

(** val map_InP_elim :
    (('a1 -> __ -> 'a2) -> 'a3) -> ('a1 -> 'a1 list -> ('a1 -> __ -> 'a2) ->
    'a3 -> 'a3) -> 'a1 list -> ('a1 -> __ -> 'a2) -> 'a3 **)

let map_InP_elim f f0 l f1 =
  let rec f2 _ _ _ = function
  | Coq_map_InP_graph_equation_1 f3 -> f f3
  | Coq_map_InP_graph_equation_2 (x, xs, f3, hind) ->
    f0 x xs f3
      (f2 xs (fun x0 _ -> f3 x0 __) (map_InP xs (fun x0 _ -> f3 x0 __)) hind)
  in f2 l f1 (map_InP l f1) (map_InP_graph_correct l f1)

(** val coq_FunctionalElimination_map_InP :
    (('a1 -> __ -> 'a2) -> __) -> ('a1 -> 'a1 list -> ('a1 -> __ -> 'a2) ->
    __ -> __) -> 'a1 list -> ('a1 -> __ -> 'a2) -> __ **)

let coq_FunctionalElimination_map_InP =
  map_InP_elim

(** val coq_FunctionalInduction_map_InP :
    ('a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list) coq_FunctionalInduction **)

let coq_FunctionalInduction_map_InP =
  Obj.magic map_InP_graph_correct

(** val remove_last : 'a1 list -> 'a1 list **)

let remove_last args =
  firstn (sub (length args) (S O)) args

type 'a snoc_view =
| Coq_snoc_view_nil
| Coq_snoc_view_snoc of 'a list * 'a

(** val snoc_view_rect :
    'a2 -> ('a1 list -> 'a1 -> 'a2) -> 'a1 list -> 'a1 snoc_view -> 'a2 **)

let snoc_view_rect f f0 _ = function
| Coq_snoc_view_nil -> f
| Coq_snoc_view_snoc (l, x) -> f0 l x

(** val snoc_view_rec :
    'a2 -> ('a1 list -> 'a1 -> 'a2) -> 'a1 list -> 'a1 snoc_view -> 'a2 **)

let snoc_view_rec f f0 _ = function
| Coq_snoc_view_nil -> f
| Coq_snoc_view_snoc (l, x) -> f0 l x

(** val snocP : 'a1 list -> 'a1 snoc_view **)

let snocP l =
  let _evar_0_ = Coq_snoc_view_nil in
  let _evar_0_0 = fun a _ _top_assumption_ ->
    let _evar_0_0 = Coq_snoc_view_snoc (Coq_nil, a) in
    let _evar_0_1 = fun l' z -> Coq_snoc_view_snoc ((Coq_cons (a, l')), z) in
    (match _top_assumption_ with
     | Coq_snoc_view_nil -> _evar_0_0
     | Coq_snoc_view_snoc (l0, x) -> _evar_0_1 l0 x)
  in
  let rec f = function
  | Coq_nil -> _evar_0_
  | Coq_cons (y, l1) -> _evar_0_0 y l1 (f l1)
  in f l

open CRelationClasses
open Classes
open Datatypes
open List
open Nat
open ReflectEq
open Specif

type __ = Obj.t

val fold_left_i_aux :
  ('a1 -> nat -> 'a2 -> 'a1) -> nat -> 'a2 list -> 'a1 -> 'a1

val fold_left_i : ('a1 -> nat -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val mapi_rec : (nat -> 'a1 -> 'a2) -> 'a1 list -> nat -> 'a2 list

val mapi : (nat -> 'a1 -> 'a2) -> 'a1 list -> 'a2 list

val safe_nth_obligation_1 : 'a1 list -> nat -> 'a1

val safe_nth : 'a1 list -> nat -> 'a1

val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val rev : 'a1 list -> 'a1 list

val rev_map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val rev_list_ind : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val rev_ind : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

type 'a nth_error_Spec =
| Coq_nth_error_Spec_Some of 'a
| Coq_nth_error_Spec_None

val nth_error_Spec_rect :
  'a1 list -> nat -> ('a1 -> __ -> __ -> 'a2) -> (__ -> 'a2) -> 'a1 option ->
  'a1 nth_error_Spec -> 'a2

val nth_error_Spec_rec :
  'a1 list -> nat -> ('a1 -> __ -> __ -> 'a2) -> (__ -> 'a2) -> 'a1 option ->
  'a1 nth_error_Spec -> 'a2

val nth_error_Some' : 'a1 list -> nat -> (('a1, __) sigT, __) iffT

val nth_error_spec : 'a1 list -> nat -> 'a1 nth_error_Spec

val chop : nat -> 'a1 list -> ('a1 list, 'a1 list) prod

val split_at_aux : nat -> 'a1 list -> 'a1 list -> ('a1 list, 'a1 list) prod

val split_at : nat -> 'a1 list -> ('a1 list, 'a1 list) prod

val list_rect_rev : 'a2 -> ('a1 -> 'a1 list -> 'a2 -> 'a2) -> 'a1 list -> 'a2

val list_size : ('a1 -> nat) -> 'a1 list -> nat

val unfold : nat -> (nat -> 'a1) -> 'a1 list

val nth_nth_error' : nat -> 'a1 list -> 'a1 -> 'a1 -> (__, __) sum

val rev_case : 'a2 -> ('a1 list -> 'a1 -> 'a2) -> 'a1 list -> 'a2

val map2i_rec :
  (nat -> 'a1 -> 'a2 -> 'a3) -> nat -> 'a1 list -> 'a2 list -> 'a3 list

val map2i : (nat -> 'a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val map_In : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list

type ('a, 'b) map_In_graph =
| Coq_map_In_graph_equation_1 of ('a -> __ -> 'b)
| Coq_map_In_graph_equation_2 of 'a * 'a list * ('a -> __ -> 'b)
   * ('a, 'b) map_In_graph

val map_In_graph_rect :
  (__ -> __ -> (__ -> __ -> __) -> 'a1) -> (__ -> __ -> __ -> __ list -> (__
  -> __ -> __) -> (__, __) map_In_graph -> 'a1 -> 'a1) -> 'a2 list -> ('a2 ->
  __ -> 'a3) -> 'a3 list -> ('a2, 'a3) map_In_graph -> 'a1

val map_In_graph_correct :
  'a1 list -> ('a1 -> __ -> 'a2) -> ('a1, 'a2) map_In_graph

val map_In_elim :
  (__ -> __ -> (__ -> __ -> __) -> 'a1) -> (__ -> __ -> __ -> __ list -> (__
  -> __ -> __) -> 'a1 -> 'a1) -> 'a2 list -> ('a2 -> __ -> 'a3) -> 'a1

val coq_FunctionalElimination_map_In :
  (__ -> __ -> (__ -> __ -> __) -> __) -> (__ -> __ -> __ -> __ list -> (__
  -> __ -> __) -> __ -> __) -> __ list -> (__ -> __ -> __) -> __

val coq_FunctionalInduction_map_In :
  (__ -> __ -> __ list -> (__ -> __ -> __) -> __ list) coq_FunctionalInduction

val split_prefix_clause_3_clause_1 :
  ('a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1 list) prod) -> 'a1
  -> 'a1 list -> 'a1 -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1 list)
  prod -> (('a1 list, 'a1 list) prod, 'a1 list) prod

val split_prefix_clause_3 :
  ('a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1 list) prod) -> 'a1
  -> 'a1 list -> 'a1 -> bool -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1
  list) prod

val split_prefix :
  'a1 coq_ReflectEq -> 'a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod,
  'a1 list) prod

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

val split_prefix_clause_3_clause_1_graph_mut :
  'a1 coq_ReflectEq -> ('a1 list -> 'a2) -> ('a1 -> 'a1 list -> 'a2) -> ('a1
  -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_clause_3_graph -> 'a3 ->
  'a2) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_graph ->
  'a2 -> 'a1 split_prefix_clause_3_clause_1_graph -> 'a4 -> 'a3) -> ('a1 ->
  'a1 list -> 'a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list
  -> 'a1 list -> 'a1 list -> 'a1 list -> 'a4) -> 'a1 -> 'a1 list -> 'a1 ->
  'a1 list -> (('a1 list, 'a1 list) prod, 'a1 list) prod -> (('a1 list, 'a1
  list) prod, 'a1 list) prod -> 'a1 split_prefix_clause_3_clause_1_graph ->
  'a4

val split_prefix_clause_3_graph_mut :
  'a1 coq_ReflectEq -> ('a1 list -> 'a2) -> ('a1 -> 'a1 list -> 'a2) -> ('a1
  -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_clause_3_graph -> 'a3 ->
  'a2) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_graph ->
  'a2 -> 'a1 split_prefix_clause_3_clause_1_graph -> 'a4 -> 'a3) -> ('a1 ->
  'a1 list -> 'a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list
  -> 'a1 list -> 'a1 list -> 'a1 list -> 'a4) -> 'a1 -> 'a1 list -> 'a1 ->
  bool -> 'a1 list -> (('a1 list, 'a1 list) prod, 'a1 list) prod -> 'a1
  split_prefix_clause_3_graph -> 'a3

val split_prefix_graph_mut :
  'a1 coq_ReflectEq -> ('a1 list -> 'a2) -> ('a1 -> 'a1 list -> 'a2) -> ('a1
  -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_clause_3_graph -> 'a3 ->
  'a2) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_graph ->
  'a2 -> 'a1 split_prefix_clause_3_clause_1_graph -> 'a4 -> 'a3) -> ('a1 ->
  'a1 list -> 'a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list
  -> 'a1 list -> 'a1 list -> 'a1 list -> 'a4) -> 'a1 list -> 'a1 list ->
  (('a1 list, 'a1 list) prod, 'a1 list) prod -> 'a1 split_prefix_graph -> 'a2

val split_prefix_graph_rect :
  'a1 coq_ReflectEq -> ('a1 list -> 'a2) -> ('a1 -> 'a1 list -> 'a2) -> ('a1
  -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_clause_3_graph -> 'a3 ->
  'a2) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list -> 'a1 split_prefix_graph ->
  'a2 -> 'a1 split_prefix_clause_3_clause_1_graph -> 'a4 -> 'a3) -> ('a1 ->
  'a1 list -> 'a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1 list -> 'a1 -> 'a1 list
  -> 'a1 list -> 'a1 list -> 'a1 list -> 'a4) -> 'a1 list -> 'a1 list ->
  (('a1 list, 'a1 list) prod, 'a1 list) prod -> 'a1 split_prefix_graph -> 'a2

val split_prefix_graph_correct :
  'a1 coq_ReflectEq -> 'a1 list -> 'a1 list -> 'a1 split_prefix_graph

val split_prefix_elim :
  'a1 coq_ReflectEq -> ('a1 list -> 'a2) -> ('a1 -> 'a1 list -> 'a2) -> ('a1
  -> 'a1 list -> 'a1 -> 'a1 list -> __ -> 'a2) -> ('a1 -> 'a1 list -> 'a1 ->
  'a1 list -> 'a1 list -> 'a1 list -> 'a1 list -> __ -> 'a2 -> __ -> 'a2) ->
  'a1 list -> 'a1 list -> 'a2

val coq_FunctionalElimination_split_prefix :
  'a1 coq_ReflectEq -> ('a1 list -> __) -> ('a1 -> 'a1 list -> __) -> ('a1 ->
  'a1 list -> 'a1 -> 'a1 list -> __ -> __) -> ('a1 -> 'a1 list -> 'a1 -> 'a1
  list -> 'a1 list -> 'a1 list -> 'a1 list -> __ -> __ -> __ -> __) -> 'a1
  list -> 'a1 list -> __

val coq_FunctionalInduction_split_prefix :
  'a1 coq_ReflectEq -> ('a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod,
  'a1 list) prod) coq_FunctionalInduction

val split_suffix :
  'a1 coq_ReflectEq -> 'a1 list -> 'a1 list -> (('a1 list, 'a1 list) prod,
  'a1 list) prod

val forallb_InP : 'a1 list -> ('a1 -> __ -> bool) -> bool

type 'a forallb_InP_graph =
| Coq_forallb_InP_graph_equation_1 of ('a -> __ -> bool)
| Coq_forallb_InP_graph_equation_2 of 'a * 'a list * ('a -> __ -> bool)
   * 'a forallb_InP_graph

val forallb_InP_graph_rect :
  (('a1 -> __ -> bool) -> 'a2) -> ('a1 -> 'a1 list -> ('a1 -> __ -> bool) ->
  'a1 forallb_InP_graph -> 'a2 -> 'a2) -> 'a1 list -> ('a1 -> __ -> bool) ->
  bool -> 'a1 forallb_InP_graph -> 'a2

val forallb_InP_graph_correct :
  'a1 list -> ('a1 -> __ -> bool) -> 'a1 forallb_InP_graph

val forallb_InP_elim :
  (('a1 -> __ -> bool) -> 'a2) -> ('a1 -> 'a1 list -> ('a1 -> __ -> bool) ->
  'a2 -> 'a2) -> 'a1 list -> ('a1 -> __ -> bool) -> 'a2

val coq_FunctionalElimination_forallb_InP :
  (('a1 -> __ -> bool) -> __) -> ('a1 -> 'a1 list -> ('a1 -> __ -> bool) ->
  __ -> __) -> 'a1 list -> ('a1 -> __ -> bool) -> __

val coq_FunctionalInduction_forallb_InP :
  ('a1 list -> ('a1 -> __ -> bool) -> bool) coq_FunctionalInduction

val map_InP : 'a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list

type ('a, 'b) map_InP_graph =
| Coq_map_InP_graph_equation_1 of ('a -> __ -> 'b)
| Coq_map_InP_graph_equation_2 of 'a * 'a list * ('a -> __ -> 'b)
   * ('a, 'b) map_InP_graph

val map_InP_graph_rect :
  (('a1 -> __ -> 'a2) -> 'a3) -> ('a1 -> 'a1 list -> ('a1 -> __ -> 'a2) ->
  ('a1, 'a2) map_InP_graph -> 'a3 -> 'a3) -> 'a1 list -> ('a1 -> __ -> 'a2)
  -> 'a2 list -> ('a1, 'a2) map_InP_graph -> 'a3

val map_InP_graph_correct :
  'a1 list -> ('a1 -> __ -> 'a2) -> ('a1, 'a2) map_InP_graph

val map_InP_elim :
  (('a1 -> __ -> 'a2) -> 'a3) -> ('a1 -> 'a1 list -> ('a1 -> __ -> 'a2) ->
  'a3 -> 'a3) -> 'a1 list -> ('a1 -> __ -> 'a2) -> 'a3

val coq_FunctionalElimination_map_InP :
  (('a1 -> __ -> 'a2) -> __) -> ('a1 -> 'a1 list -> ('a1 -> __ -> 'a2) -> __
  -> __) -> 'a1 list -> ('a1 -> __ -> 'a2) -> __

val coq_FunctionalInduction_map_InP :
  ('a1 list -> ('a1 -> __ -> 'a2) -> 'a2 list) coq_FunctionalInduction

val remove_last : 'a1 list -> 'a1 list

type 'a snoc_view =
| Coq_snoc_view_nil
| Coq_snoc_view_snoc of 'a list * 'a

val snoc_view_rect :
  'a2 -> ('a1 list -> 'a1 -> 'a2) -> 'a1 list -> 'a1 snoc_view -> 'a2

val snoc_view_rec :
  'a2 -> ('a1 list -> 'a1 -> 'a2) -> 'a1 list -> 'a1 snoc_view -> 'a2

val snocP : 'a1 list -> 'a1 snoc_view

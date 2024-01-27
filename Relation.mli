open Datatypes
open Logic1

type ('a, 'r) trans_clos =
| Coq_t_step of 'a * 'r
| Coq_t_trans of 'a * 'a * ('a, 'r) trans_clos * ('a, 'r) trans_clos

val trans_clos_rect :
  ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1, 'a2) trans_clos
  -> 'a3 -> ('a1, 'a2) trans_clos -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2)
  trans_clos -> 'a3

val trans_clos_rec :
  ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1, 'a2) trans_clos
  -> 'a3 -> ('a1, 'a2) trans_clos -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2)
  trans_clos -> 'a3

type ('a, 'r) trans_clos_1n =
| Coq_t1n_step of 'a * 'r
| Coq_t1n_trans of 'a * 'a * 'r * ('a, 'r) trans_clos_1n

val trans_clos_1n_rect :
  ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2)
  trans_clos_1n -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2) trans_clos_1n ->
  'a3

val trans_clos_1n_rec :
  ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2)
  trans_clos_1n -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2) trans_clos_1n ->
  'a3

type ('a, 'r) trans_clos_n1 =
| Coq_tn1_step of 'a * 'r
| Coq_tn1_trans of 'a * 'a * 'r * ('a, 'r) trans_clos_n1

val trans_clos_n1_rect :
  'a1 -> ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2)
  trans_clos_n1 -> 'a3 -> 'a3) -> 'a1 -> ('a1, 'a2) trans_clos_n1 -> 'a3

val trans_clos_n1_rec :
  'a1 -> ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2)
  trans_clos_n1 -> 'a3 -> 'a3) -> 'a1 -> ('a1, 'a2) trans_clos_n1 -> 'a3

type ('a, 'r) clos_refl =
| Coq_r_step of 'a * 'r
| Coq_r_refl

val clos_refl_rect :
  'a1 -> ('a1 -> 'a2 -> 'a3) -> 'a3 -> 'a1 -> ('a1, 'a2) clos_refl -> 'a3

val clos_refl_rec :
  'a1 -> ('a1 -> 'a2 -> 'a3) -> 'a3 -> 'a1 -> ('a1, 'a2) clos_refl -> 'a3

type ('a, 'r) clos_refl_trans =
| Coq_rt_step of 'a * 'r
| Coq_rt_refl
| Coq_rt_trans of 'a * 'a * ('a, 'r) clos_refl_trans
   * ('a, 'r) clos_refl_trans

val clos_refl_trans_rect :
  ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1,
  'a2) clos_refl_trans -> 'a3 -> ('a1, 'a2) clos_refl_trans -> 'a3 -> 'a3) ->
  'a1 -> 'a1 -> ('a1, 'a2) clos_refl_trans -> 'a3

val clos_refl_trans_rec :
  ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1,
  'a2) clos_refl_trans -> 'a3 -> ('a1, 'a2) clos_refl_trans -> 'a3 -> 'a3) ->
  'a1 -> 'a1 -> ('a1, 'a2) clos_refl_trans -> 'a3

type ('a, 'r) clos_refl_trans_1n =
| Coq_rt1n_refl
| Coq_rt1n_trans of 'a * 'a * 'r * ('a, 'r) clos_refl_trans_1n

val clos_refl_trans_1n_rect :
  ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2) clos_refl_trans_1n
  -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2) clos_refl_trans_1n -> 'a3

val clos_refl_trans_1n_rec :
  ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2) clos_refl_trans_1n
  -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2) clos_refl_trans_1n -> 'a3

type ('a, 'r) clos_refl_trans_n1 =
| Coq_rtn1_refl
| Coq_rtn1_trans of 'a * 'a * 'r * ('a, 'r) clos_refl_trans_n1

val clos_refl_trans_n1_rect :
  'a1 -> 'a3 -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2) clos_refl_trans_n1 -> 'a3 ->
  'a3) -> 'a1 -> ('a1, 'a2) clos_refl_trans_n1 -> 'a3

val clos_refl_trans_n1_rec :
  'a1 -> 'a3 -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2) clos_refl_trans_n1 -> 'a3 ->
  'a3) -> 'a1 -> ('a1, 'a2) clos_refl_trans_n1 -> 'a3

type ('a, 'r) clos_refl_sym_trans =
| Coq_rst_step of 'a * 'a * 'r
| Coq_rst_refl of 'a
| Coq_rst_sym of 'a * 'a * ('a, 'r) clos_refl_sym_trans
| Coq_rst_trans of 'a * 'a * 'a * ('a, 'r) clos_refl_sym_trans
   * ('a, 'r) clos_refl_sym_trans

val clos_refl_sym_trans_rect :
  ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> ('a1, 'a2)
  clos_refl_sym_trans -> 'a3 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1, 'a2)
  clos_refl_sym_trans -> 'a3 -> ('a1, 'a2) clos_refl_sym_trans -> 'a3 -> 'a3)
  -> 'a1 -> 'a1 -> ('a1, 'a2) clos_refl_sym_trans -> 'a3

val clos_refl_sym_trans_rec :
  ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> ('a1, 'a2)
  clos_refl_sym_trans -> 'a3 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1, 'a2)
  clos_refl_sym_trans -> 'a3 -> ('a1, 'a2) clos_refl_sym_trans -> 'a3 -> 'a3)
  -> 'a1 -> 'a1 -> ('a1, 'a2) clos_refl_sym_trans -> 'a3

type ('a, 'r) clos_refl_sym_trans_1n =
| Coq_rst1n_refl
| Coq_rst1n_trans of 'a * 'a * ('r, 'r) sum * ('a, 'r) clos_refl_sym_trans_1n

val clos_refl_sym_trans_1n_rect :
  ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a2, 'a2) sum -> ('a1, 'a2)
  clos_refl_sym_trans_1n -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2)
  clos_refl_sym_trans_1n -> 'a3

val clos_refl_sym_trans_1n_rec :
  ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a2, 'a2) sum -> ('a1, 'a2)
  clos_refl_sym_trans_1n -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2)
  clos_refl_sym_trans_1n -> 'a3

type ('a, 'r) clos_refl_sym_trans_n1 =
| Coq_rstn1_refl
| Coq_rstn1_trans of 'a * 'a * ('r, 'r) sum * ('a, 'r) clos_refl_sym_trans_n1

val clos_refl_sym_trans_n1_rect :
  'a1 -> 'a3 -> ('a1 -> 'a1 -> ('a2, 'a2) sum -> ('a1, 'a2)
  clos_refl_sym_trans_n1 -> 'a3 -> 'a3) -> 'a1 -> ('a1, 'a2)
  clos_refl_sym_trans_n1 -> 'a3

val clos_refl_sym_trans_n1_rec :
  'a1 -> 'a3 -> ('a1 -> 'a1 -> ('a2, 'a2) sum -> ('a1, 'a2)
  clos_refl_sym_trans_n1 -> 'a3 -> 'a3) -> 'a1 -> ('a1, 'a2)
  clos_refl_sym_trans_n1 -> 'a3

type ('a, 'r) transp = 'r

type ('a, 'r1, 'r2) union = ('r1, 'r2) sum

type ('a, 'b, 'leA, 'leB) le_AsB =
| Coq_le_aa of 'a * 'a * 'leA
| Coq_le_ab of 'a * 'b
| Coq_le_bb of 'b * 'b * 'leB

val le_AsB_rect :
  ('a1 -> 'a1 -> 'a3 -> 'a5) -> ('a1 -> 'a2 -> 'a5) -> ('a2 -> 'a2 -> 'a4 ->
  'a5) -> ('a1, 'a2) sum -> ('a1, 'a2) sum -> ('a1, 'a2, 'a3, 'a4) le_AsB ->
  'a5

val le_AsB_rec :
  ('a1 -> 'a1 -> 'a3 -> 'a5) -> ('a1 -> 'a2 -> 'a5) -> ('a2 -> 'a2 -> 'a4 ->
  'a5) -> ('a1, 'a2) sum -> ('a1, 'a2) sum -> ('a1, 'a2, 'a3, 'a4) le_AsB ->
  'a5

type ('a, 'b, 'leA, 'leB) lexprod =
| Coq_left_lex of 'a * 'a * 'b * 'b * 'leA
| Coq_right_lex of 'a * 'b * 'b * 'leB

val lexprod_rect :
  ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a3 -> 'a5) -> ('a1 -> 'a2 -> 'a2 -> 'a4 ->
  'a5) -> ('a1 * 'a2) -> ('a1 * 'a2) -> ('a1, 'a2, 'a3, 'a4) lexprod -> 'a5

val lexprod_rec :
  ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a3 -> 'a5) -> ('a1 -> 'a2 -> 'a2 -> 'a4 ->
  'a5) -> ('a1 * 'a2) -> ('a1 * 'a2) -> ('a1, 'a2, 'a3, 'a4) lexprod -> 'a5

type ('a, 'b, 'leA, 'leB) symprod =
| Coq_left_sym of 'a * 'a * 'leA * 'b
| Coq_right_sym of 'b * 'b * 'leB * 'a

val symprod_rect :
  ('a1 -> 'a1 -> 'a3 -> 'a2 -> 'a5) -> ('a2 -> 'a2 -> 'a4 -> 'a1 -> 'a5) ->
  ('a1, 'a2) prod -> ('a1, 'a2) prod -> ('a1, 'a2, 'a3, 'a4) symprod -> 'a5

val symprod_rec :
  ('a1 -> 'a1 -> 'a3 -> 'a2 -> 'a5) -> ('a2 -> 'a2 -> 'a4 -> 'a1 -> 'a5) ->
  ('a1, 'a2) prod -> ('a1, 'a2) prod -> ('a1, 'a2, 'a3, 'a4) symprod -> 'a5

type ('a, 'r) swapprod =
| Coq_sp_noswap of 'a * 'a * ('a, 'a) prod * ('a, 'a, 'r, 'r) symprod
| Coq_sp_swap of 'a * 'a * ('a, 'a) prod * ('a, 'a, 'r, 'r) symprod

val swapprod_rect :
  ('a1 -> 'a1 -> ('a1, 'a1) prod -> ('a1, 'a1, 'a2, 'a2) symprod -> 'a3) ->
  ('a1 -> 'a1 -> ('a1, 'a1) prod -> ('a1, 'a1, 'a2, 'a2) symprod -> 'a3) ->
  ('a1, 'a1) prod -> ('a1, 'a1) prod -> ('a1, 'a2) swapprod -> 'a3

val swapprod_rec :
  ('a1 -> 'a1 -> ('a1, 'a1) prod -> ('a1, 'a1, 'a2, 'a2) symprod -> 'a3) ->
  ('a1 -> 'a1 -> ('a1, 'a1) prod -> ('a1, 'a1, 'a2, 'a2) symprod -> 'a3) ->
  ('a1, 'a1) prod -> ('a1, 'a1) prod -> ('a1, 'a2) swapprod -> 'a3

type ('a, 'leA) coq_Ltl =
| Lt_nil of 'a * 'a list
| Lt_hd of 'a * 'a * 'leA * 'a list * 'a list
| Lt_tl of 'a * 'a list * 'a list * ('a, 'leA) coq_Ltl

val coq_Ltl_rect :
  ('a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1 -> 'a2 -> 'a1 list -> 'a1 list ->
  'a3) -> ('a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Ltl -> 'a3 -> 'a3)
  -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Ltl -> 'a3

val coq_Ltl_rec :
  ('a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1 -> 'a2 -> 'a1 list -> 'a1 list ->
  'a3) -> ('a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Ltl -> 'a3 -> 'a3)
  -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Ltl -> 'a3

type ('a, 'leA) coq_Desc =
| Coq_d_nil
| Coq_d_one of 'a
| Coq_d_conc of 'a * 'a * 'a list * ('a, 'leA) clos_refl * ('a, 'leA) coq_Desc

val coq_Desc_rect :
  'a3 -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 list -> ('a1, 'a2) clos_refl ->
  ('a1, 'a2) coq_Desc -> 'a3 -> 'a3) -> 'a1 list -> ('a1, 'a2) coq_Desc -> 'a3

val coq_Desc_rec :
  'a3 -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 list -> ('a1, 'a2) clos_refl ->
  ('a1, 'a2) coq_Desc -> 'a3 -> 'a3) -> 'a1 list -> ('a1, 'a2) coq_Desc -> 'a3

type ('a, 'leA) coq_Pow = 'a list * ('a, 'leA) coq_Desc

type ('a, 'leA) lex_exp = ('a, 'leA) coq_Ltl

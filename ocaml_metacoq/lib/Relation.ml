open Datatypes
open Logic1

type ('a, 'r) trans_clos =
| Coq_t_step of 'a * 'r
| Coq_t_trans of 'a * 'a * ('a, 'r) trans_clos * ('a, 'r) trans_clos

(** val trans_clos_rect :
    ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1, 'a2) trans_clos
    -> 'a3 -> ('a1, 'a2) trans_clos -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1,
    'a2) trans_clos -> 'a3 **)

let rec trans_clos_rect f f0 x _ = function
| Coq_t_step (y, r) -> f x y r
| Coq_t_trans (y, z, t0, t1) ->
  f0 x y z t0 (trans_clos_rect f f0 x y t0) t1 (trans_clos_rect f f0 y z t1)

(** val trans_clos_rec :
    ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1, 'a2) trans_clos
    -> 'a3 -> ('a1, 'a2) trans_clos -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1,
    'a2) trans_clos -> 'a3 **)

let rec trans_clos_rec f f0 x _ = function
| Coq_t_step (y, r) -> f x y r
| Coq_t_trans (y, z, t0, t1) ->
  f0 x y z t0 (trans_clos_rec f f0 x y t0) t1 (trans_clos_rec f f0 y z t1)

type ('a, 'r) trans_clos_1n =
| Coq_t1n_step of 'a * 'r
| Coq_t1n_trans of 'a * 'a * 'r * ('a, 'r) trans_clos_1n

(** val trans_clos_1n_rect :
    ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2)
    trans_clos_1n -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2) trans_clos_1n ->
    'a3 **)

let rec trans_clos_1n_rect f f0 x _ = function
| Coq_t1n_step (y, r) -> f x y r
| Coq_t1n_trans (y, z, r, t0) ->
  f0 x y z r t0 (trans_clos_1n_rect f f0 y z t0)

(** val trans_clos_1n_rec :
    ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2)
    trans_clos_1n -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2) trans_clos_1n ->
    'a3 **)

let rec trans_clos_1n_rec f f0 x _ = function
| Coq_t1n_step (y, r) -> f x y r
| Coq_t1n_trans (y, z, r, t0) -> f0 x y z r t0 (trans_clos_1n_rec f f0 y z t0)

type ('a, 'r) trans_clos_n1 =
| Coq_tn1_step of 'a * 'r
| Coq_tn1_trans of 'a * 'a * 'r * ('a, 'r) trans_clos_n1

(** val trans_clos_n1_rect :
    'a1 -> ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2)
    trans_clos_n1 -> 'a3 -> 'a3) -> 'a1 -> ('a1, 'a2) trans_clos_n1 -> 'a3 **)

let rec trans_clos_n1_rect x f f0 _ = function
| Coq_tn1_step (y, r) -> f y r
| Coq_tn1_trans (y, z, r, t0) -> f0 y z r t0 (trans_clos_n1_rect x f f0 y t0)

(** val trans_clos_n1_rec :
    'a1 -> ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2)
    trans_clos_n1 -> 'a3 -> 'a3) -> 'a1 -> ('a1, 'a2) trans_clos_n1 -> 'a3 **)

let rec trans_clos_n1_rec x f f0 _ = function
| Coq_tn1_step (y, r) -> f y r
| Coq_tn1_trans (y, z, r, t0) -> f0 y z r t0 (trans_clos_n1_rec x f f0 y t0)

type ('a, 'r) clos_refl =
| Coq_r_step of 'a * 'r
| Coq_r_refl

(** val clos_refl_rect :
    'a1 -> ('a1 -> 'a2 -> 'a3) -> 'a3 -> 'a1 -> ('a1, 'a2) clos_refl -> 'a3 **)

let clos_refl_rect _ f f0 _ = function
| Coq_r_step (y, r) -> f y r
| Coq_r_refl -> f0

(** val clos_refl_rec :
    'a1 -> ('a1 -> 'a2 -> 'a3) -> 'a3 -> 'a1 -> ('a1, 'a2) clos_refl -> 'a3 **)

let clos_refl_rec _ f f0 _ = function
| Coq_r_step (y, r) -> f y r
| Coq_r_refl -> f0

type ('a, 'r) clos_refl_trans =
| Coq_rt_step of 'a * 'r
| Coq_rt_refl
| Coq_rt_trans of 'a * 'a * ('a, 'r) clos_refl_trans
   * ('a, 'r) clos_refl_trans

(** val clos_refl_trans_rect :
    ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1,
    'a2) clos_refl_trans -> 'a3 -> ('a1, 'a2) clos_refl_trans -> 'a3 -> 'a3)
    -> 'a1 -> 'a1 -> ('a1, 'a2) clos_refl_trans -> 'a3 **)

let rec clos_refl_trans_rect f f0 f1 x _ = function
| Coq_rt_step (y, r) -> f x y r
| Coq_rt_refl -> f0 x
| Coq_rt_trans (y, z, c0, c1) ->
  f1 x y z c0 (clos_refl_trans_rect f f0 f1 x y c0) c1
    (clos_refl_trans_rect f f0 f1 y z c1)

(** val clos_refl_trans_rec :
    ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1,
    'a2) clos_refl_trans -> 'a3 -> ('a1, 'a2) clos_refl_trans -> 'a3 -> 'a3)
    -> 'a1 -> 'a1 -> ('a1, 'a2) clos_refl_trans -> 'a3 **)

let rec clos_refl_trans_rec f f0 f1 x _ = function
| Coq_rt_step (y, r) -> f x y r
| Coq_rt_refl -> f0 x
| Coq_rt_trans (y, z, c0, c1) ->
  f1 x y z c0 (clos_refl_trans_rec f f0 f1 x y c0) c1
    (clos_refl_trans_rec f f0 f1 y z c1)

type ('a, 'r) clos_refl_trans_1n =
| Coq_rt1n_refl
| Coq_rt1n_trans of 'a * 'a * 'r * ('a, 'r) clos_refl_trans_1n

(** val clos_refl_trans_1n_rect :
    ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2)
    clos_refl_trans_1n -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2)
    clos_refl_trans_1n -> 'a3 **)

let rec clos_refl_trans_1n_rect f f0 x _ = function
| Coq_rt1n_refl -> f x
| Coq_rt1n_trans (y, z, r, c0) ->
  f0 x y z r c0 (clos_refl_trans_1n_rect f f0 y z c0)

(** val clos_refl_trans_1n_rec :
    ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> 'a2 -> ('a1, 'a2)
    clos_refl_trans_1n -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2)
    clos_refl_trans_1n -> 'a3 **)

let rec clos_refl_trans_1n_rec f f0 x _ = function
| Coq_rt1n_refl -> f x
| Coq_rt1n_trans (y, z, r, c0) ->
  f0 x y z r c0 (clos_refl_trans_1n_rec f f0 y z c0)

type ('a, 'r) clos_refl_trans_n1 =
| Coq_rtn1_refl
| Coq_rtn1_trans of 'a * 'a * 'r * ('a, 'r) clos_refl_trans_n1

(** val clos_refl_trans_n1_rect :
    'a1 -> 'a3 -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2) clos_refl_trans_n1 -> 'a3
    -> 'a3) -> 'a1 -> ('a1, 'a2) clos_refl_trans_n1 -> 'a3 **)

let rec clos_refl_trans_n1_rect x f f0 _ = function
| Coq_rtn1_refl -> f
| Coq_rtn1_trans (y, z, r, c0) ->
  f0 y z r c0 (clos_refl_trans_n1_rect x f f0 y c0)

(** val clos_refl_trans_n1_rec :
    'a1 -> 'a3 -> ('a1 -> 'a1 -> 'a2 -> ('a1, 'a2) clos_refl_trans_n1 -> 'a3
    -> 'a3) -> 'a1 -> ('a1, 'a2) clos_refl_trans_n1 -> 'a3 **)

let rec clos_refl_trans_n1_rec x f f0 _ = function
| Coq_rtn1_refl -> f
| Coq_rtn1_trans (y, z, r, c0) ->
  f0 y z r c0 (clos_refl_trans_n1_rec x f f0 y c0)

type ('a, 'r) clos_refl_sym_trans =
| Coq_rst_step of 'a * 'a * 'r
| Coq_rst_refl of 'a
| Coq_rst_sym of 'a * 'a * ('a, 'r) clos_refl_sym_trans
| Coq_rst_trans of 'a * 'a * 'a * ('a, 'r) clos_refl_sym_trans
   * ('a, 'r) clos_refl_sym_trans

(** val clos_refl_sym_trans_rect :
    ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> ('a1, 'a2)
    clos_refl_sym_trans -> 'a3 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1, 'a2)
    clos_refl_sym_trans -> 'a3 -> ('a1, 'a2) clos_refl_sym_trans -> 'a3 ->
    'a3) -> 'a1 -> 'a1 -> ('a1, 'a2) clos_refl_sym_trans -> 'a3 **)

let rec clos_refl_sym_trans_rect f f0 f1 f2 _ _ = function
| Coq_rst_step (x, y, r) -> f x y r
| Coq_rst_refl x -> f0 x
| Coq_rst_sym (x, y, c0) ->
  f1 x y c0 (clos_refl_sym_trans_rect f f0 f1 f2 x y c0)
| Coq_rst_trans (x, y, z, c0, c1) ->
  f2 x y z c0 (clos_refl_sym_trans_rect f f0 f1 f2 x y c0) c1
    (clos_refl_sym_trans_rect f f0 f1 f2 y z c1)

(** val clos_refl_sym_trans_rec :
    ('a1 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> ('a1, 'a2)
    clos_refl_sym_trans -> 'a3 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a1, 'a2)
    clos_refl_sym_trans -> 'a3 -> ('a1, 'a2) clos_refl_sym_trans -> 'a3 ->
    'a3) -> 'a1 -> 'a1 -> ('a1, 'a2) clos_refl_sym_trans -> 'a3 **)

let rec clos_refl_sym_trans_rec f f0 f1 f2 _ _ = function
| Coq_rst_step (x, y, r) -> f x y r
| Coq_rst_refl x -> f0 x
| Coq_rst_sym (x, y, c0) ->
  f1 x y c0 (clos_refl_sym_trans_rec f f0 f1 f2 x y c0)
| Coq_rst_trans (x, y, z, c0, c1) ->
  f2 x y z c0 (clos_refl_sym_trans_rec f f0 f1 f2 x y c0) c1
    (clos_refl_sym_trans_rec f f0 f1 f2 y z c1)

type ('a, 'r) clos_refl_sym_trans_1n =
| Coq_rst1n_refl
| Coq_rst1n_trans of 'a * 'a * ('r, 'r) sum * ('a, 'r) clos_refl_sym_trans_1n

(** val clos_refl_sym_trans_1n_rect :
    ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a2, 'a2) sum -> ('a1, 'a2)
    clos_refl_sym_trans_1n -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2)
    clos_refl_sym_trans_1n -> 'a3 **)

let rec clos_refl_sym_trans_1n_rect f f0 x _ = function
| Coq_rst1n_refl -> f x
| Coq_rst1n_trans (y, z, s, c0) ->
  f0 x y z s c0 (clos_refl_sym_trans_1n_rect f f0 y z c0)

(** val clos_refl_sym_trans_1n_rec :
    ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 -> ('a2, 'a2) sum -> ('a1, 'a2)
    clos_refl_sym_trans_1n -> 'a3 -> 'a3) -> 'a1 -> 'a1 -> ('a1, 'a2)
    clos_refl_sym_trans_1n -> 'a3 **)

let rec clos_refl_sym_trans_1n_rec f f0 x _ = function
| Coq_rst1n_refl -> f x
| Coq_rst1n_trans (y, z, s, c0) ->
  f0 x y z s c0 (clos_refl_sym_trans_1n_rec f f0 y z c0)

type ('a, 'r) clos_refl_sym_trans_n1 =
| Coq_rstn1_refl
| Coq_rstn1_trans of 'a * 'a * ('r, 'r) sum * ('a, 'r) clos_refl_sym_trans_n1

(** val clos_refl_sym_trans_n1_rect :
    'a1 -> 'a3 -> ('a1 -> 'a1 -> ('a2, 'a2) sum -> ('a1, 'a2)
    clos_refl_sym_trans_n1 -> 'a3 -> 'a3) -> 'a1 -> ('a1, 'a2)
    clos_refl_sym_trans_n1 -> 'a3 **)

let rec clos_refl_sym_trans_n1_rect x f f0 _ = function
| Coq_rstn1_refl -> f
| Coq_rstn1_trans (y, z, s, c0) ->
  f0 y z s c0 (clos_refl_sym_trans_n1_rect x f f0 y c0)

(** val clos_refl_sym_trans_n1_rec :
    'a1 -> 'a3 -> ('a1 -> 'a1 -> ('a2, 'a2) sum -> ('a1, 'a2)
    clos_refl_sym_trans_n1 -> 'a3 -> 'a3) -> 'a1 -> ('a1, 'a2)
    clos_refl_sym_trans_n1 -> 'a3 **)

let rec clos_refl_sym_trans_n1_rec x f f0 _ = function
| Coq_rstn1_refl -> f
| Coq_rstn1_trans (y, z, s, c0) ->
  f0 y z s c0 (clos_refl_sym_trans_n1_rec x f f0 y c0)

type ('a, 'r) transp = 'r

type ('a, 'r1, 'r2) union = ('r1, 'r2) sum

type ('a, 'b, 'leA, 'leB) le_AsB =
| Coq_le_aa of 'a * 'a * 'leA
| Coq_le_ab of 'a * 'b
| Coq_le_bb of 'b * 'b * 'leB

(** val le_AsB_rect :
    ('a1 -> 'a1 -> 'a3 -> 'a5) -> ('a1 -> 'a2 -> 'a5) -> ('a2 -> 'a2 -> 'a4
    -> 'a5) -> ('a1, 'a2) sum -> ('a1, 'a2) sum -> ('a1, 'a2, 'a3, 'a4)
    le_AsB -> 'a5 **)

let le_AsB_rect f f0 f1 _ _ = function
| Coq_le_aa (x, y, l0) -> f x y l0
| Coq_le_ab (x, y) -> f0 x y
| Coq_le_bb (x, y, l0) -> f1 x y l0

(** val le_AsB_rec :
    ('a1 -> 'a1 -> 'a3 -> 'a5) -> ('a1 -> 'a2 -> 'a5) -> ('a2 -> 'a2 -> 'a4
    -> 'a5) -> ('a1, 'a2) sum -> ('a1, 'a2) sum -> ('a1, 'a2, 'a3, 'a4)
    le_AsB -> 'a5 **)

let le_AsB_rec f f0 f1 _ _ = function
| Coq_le_aa (x, y, l0) -> f x y l0
| Coq_le_ab (x, y) -> f0 x y
| Coq_le_bb (x, y, l0) -> f1 x y l0

type ('a, 'b, 'leA, 'leB) lexprod =
| Coq_left_lex of 'a * 'a * 'b * 'b * 'leA
| Coq_right_lex of 'a * 'b * 'b * 'leB

(** val lexprod_rect :
    ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a3 -> 'a5) -> ('a1 -> 'a2 -> 'a2 -> 'a4 ->
    'a5) -> ('a1 * 'a2) -> ('a1 * 'a2) -> ('a1, 'a2, 'a3, 'a4) lexprod -> 'a5 **)

let lexprod_rect f f0 _ _ = function
| Coq_left_lex (x, x', y, y', l0) -> f x x' y y' l0
| Coq_right_lex (x, y, y', l0) -> f0 x y y' l0

(** val lexprod_rec :
    ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a3 -> 'a5) -> ('a1 -> 'a2 -> 'a2 -> 'a4 ->
    'a5) -> ('a1 * 'a2) -> ('a1 * 'a2) -> ('a1, 'a2, 'a3, 'a4) lexprod -> 'a5 **)

let lexprod_rec f f0 _ _ = function
| Coq_left_lex (x, x', y, y', l0) -> f x x' y y' l0
| Coq_right_lex (x, y, y', l0) -> f0 x y y' l0

type ('a, 'b, 'leA, 'leB) symprod =
| Coq_left_sym of 'a * 'a * 'leA * 'b
| Coq_right_sym of 'b * 'b * 'leB * 'a

(** val symprod_rect :
    ('a1 -> 'a1 -> 'a3 -> 'a2 -> 'a5) -> ('a2 -> 'a2 -> 'a4 -> 'a1 -> 'a5) ->
    ('a1, 'a2) prod -> ('a1, 'a2) prod -> ('a1, 'a2, 'a3, 'a4) symprod -> 'a5 **)

let symprod_rect f f0 _ _ = function
| Coq_left_sym (x, x', l, y) -> f x x' l y
| Coq_right_sym (y, y', l, x) -> f0 y y' l x

(** val symprod_rec :
    ('a1 -> 'a1 -> 'a3 -> 'a2 -> 'a5) -> ('a2 -> 'a2 -> 'a4 -> 'a1 -> 'a5) ->
    ('a1, 'a2) prod -> ('a1, 'a2) prod -> ('a1, 'a2, 'a3, 'a4) symprod -> 'a5 **)

let symprod_rec f f0 _ _ = function
| Coq_left_sym (x, x', l, y) -> f x x' l y
| Coq_right_sym (y, y', l, x) -> f0 y y' l x

type ('a, 'r) swapprod =
| Coq_sp_noswap of 'a * 'a * ('a, 'a) prod * ('a, 'a, 'r, 'r) symprod
| Coq_sp_swap of 'a * 'a * ('a, 'a) prod * ('a, 'a, 'r, 'r) symprod

(** val swapprod_rect :
    ('a1 -> 'a1 -> ('a1, 'a1) prod -> ('a1, 'a1, 'a2, 'a2) symprod -> 'a3) ->
    ('a1 -> 'a1 -> ('a1, 'a1) prod -> ('a1, 'a1, 'a2, 'a2) symprod -> 'a3) ->
    ('a1, 'a1) prod -> ('a1, 'a1) prod -> ('a1, 'a2) swapprod -> 'a3 **)

let swapprod_rect f f0 _ _ = function
| Coq_sp_noswap (x, y, p, s0) -> f x y p s0
| Coq_sp_swap (x, y, p, s0) -> f0 x y p s0

(** val swapprod_rec :
    ('a1 -> 'a1 -> ('a1, 'a1) prod -> ('a1, 'a1, 'a2, 'a2) symprod -> 'a3) ->
    ('a1 -> 'a1 -> ('a1, 'a1) prod -> ('a1, 'a1, 'a2, 'a2) symprod -> 'a3) ->
    ('a1, 'a1) prod -> ('a1, 'a1) prod -> ('a1, 'a2) swapprod -> 'a3 **)

let swapprod_rec f f0 _ _ = function
| Coq_sp_noswap (x, y, p, s0) -> f x y p s0
| Coq_sp_swap (x, y, p, s0) -> f0 x y p s0

type ('a, 'leA) coq_Ltl =
| Lt_nil of 'a * 'a list
| Lt_hd of 'a * 'a * 'leA * 'a list * 'a list
| Lt_tl of 'a * 'a list * 'a list * ('a, 'leA) coq_Ltl

(** val coq_Ltl_rect :
    ('a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1 -> 'a2 -> 'a1 list -> 'a1 list ->
    'a3) -> ('a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Ltl -> 'a3 -> 'a3)
    -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Ltl -> 'a3 **)

let rec coq_Ltl_rect f f0 f1 _ _ = function
| Lt_nil (a, x) -> f a x
| Lt_hd (a, b, l, x, y) -> f0 a b l x y
| Lt_tl (a, x, y, l) -> f1 a x y l (coq_Ltl_rect f f0 f1 x y l)

(** val coq_Ltl_rec :
    ('a1 -> 'a1 list -> 'a3) -> ('a1 -> 'a1 -> 'a2 -> 'a1 list -> 'a1 list ->
    'a3) -> ('a1 -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Ltl -> 'a3 -> 'a3)
    -> 'a1 list -> 'a1 list -> ('a1, 'a2) coq_Ltl -> 'a3 **)

let rec coq_Ltl_rec f f0 f1 _ _ = function
| Lt_nil (a, x) -> f a x
| Lt_hd (a, b, l, x, y) -> f0 a b l x y
| Lt_tl (a, x, y, l) -> f1 a x y l (coq_Ltl_rec f f0 f1 x y l)

type ('a, 'leA) coq_Desc =
| Coq_d_nil
| Coq_d_one of 'a
| Coq_d_conc of 'a * 'a * 'a list * ('a, 'leA) clos_refl * ('a, 'leA) coq_Desc

(** val coq_Desc_rect :
    'a3 -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 list -> ('a1, 'a2) clos_refl ->
    ('a1, 'a2) coq_Desc -> 'a3 -> 'a3) -> 'a1 list -> ('a1, 'a2) coq_Desc ->
    'a3 **)

let coq_Desc_rect f f0 f1 l d =
  let nil = Coq_nil in
  let rec f2 _ = function
  | Coq_d_nil -> f
  | Coq_d_one x -> f0 x
  | Coq_d_conc (x, y, l0, c, d1) ->
    f1 x y l0 c d1 (f2 (app l0 (Coq_cons (y, nil))) d1)
  in f2 l d

(** val coq_Desc_rec :
    'a3 -> ('a1 -> 'a3) -> ('a1 -> 'a1 -> 'a1 list -> ('a1, 'a2) clos_refl ->
    ('a1, 'a2) coq_Desc -> 'a3 -> 'a3) -> 'a1 list -> ('a1, 'a2) coq_Desc ->
    'a3 **)

let coq_Desc_rec f f0 f1 l d =
  let nil = Coq_nil in
  let rec f2 _ = function
  | Coq_d_nil -> f
  | Coq_d_one x -> f0 x
  | Coq_d_conc (x, y, l0, c, d1) ->
    f1 x y l0 c d1 (f2 (app l0 (Coq_cons (y, nil))) d1)
  in f2 l d

type ('a, 'leA) coq_Pow = 'a list * ('a, 'leA) coq_Desc

type ('a, 'leA) lex_exp = ('a, 'leA) coq_Ltl

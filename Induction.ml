open All_Forall
open Ast
open AstUtils
open BasicAst
open Datatypes
open Kernames
open PrimFloat
open PrimInt63
open Universes

(** val term_forall_list_rect :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> (term, 'a1)
    coq_All -> 'a1) -> (Universe.t -> 'a1) -> (term -> 'a1 -> cast_kind ->
    term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) ->
    (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 ->
    term -> 'a1 -> term -> 'a1 -> 'a1) -> (term -> 'a1 -> term list -> (term,
    'a1) coq_All -> 'a1) -> (kername -> Level.t list -> 'a1) -> (inductive ->
    Level.t list -> 'a1) -> (inductive -> nat -> Level.t list -> 'a1) ->
    (case_info -> term predicate -> (term, 'a1, 'a1) tCasePredProp -> term ->
    'a1 -> term branch list -> (term, 'a1) tCaseBrsType -> 'a1) ->
    (projection -> term -> 'a1 -> 'a1) -> (term mfixpoint -> nat -> (term,
    'a1, 'a1) tFixType -> 'a1) -> (term mfixpoint -> nat -> (term, 'a1, 'a1)
    tFixType -> 'a1) -> (int -> 'a1) -> (float -> 'a1) -> term -> 'a1 **)

let rec term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 = function
| Coq_tRel n -> x n
| Coq_tVar id -> x0 id
| Coq_tEvar (ev, args) ->
  x1 ev args
    (let rec aux_arg = function
     | Coq_nil -> All_nil
     | Coq_cons (t1, l) ->
       All_cons (t1, l,
         (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
           x13 x14 x15 x16 t1), (aux_arg l))
     in aux_arg args)
| Coq_tSort s -> x2 s
| Coq_tCast (t1, kind, v) ->
  x3 t1
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 t1) kind v
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 v)
| Coq_tProd (na, ty, body) ->
  x4 na ty
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 ty) body
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 body)
| Coq_tLambda (na, ty, body) ->
  x5 na ty
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 ty) body
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 body)
| Coq_tLetIn (na, def, def_ty, body) ->
  x6 na def
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 def) def_ty
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 def_ty) body
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 body)
| Coq_tApp (f, args) ->
  x7 f
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 f) args
    (let rec aux_arg = function
     | Coq_nil -> All_nil
     | Coq_cons (t1, l) ->
       All_cons (t1, l,
         (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
           x13 x14 x15 x16 t1), (aux_arg l))
     in aux_arg args)
| Coq_tConst (c, u) -> x8 c u
| Coq_tInd (ind, u) -> x9 ind u
| Coq_tConstruct (ind, idx, u) -> x10 ind idx u
| Coq_tCase (ci, type_info, discr, branches) ->
  x11 ci type_info
    (let { puinst = _; pparams = pparams0; pcontext = _; preturn =
       preturn0 } = type_info
     in
     Coq_pair
     ((let rec aux_pparams = function
       | Coq_nil -> All_nil
       | Coq_cons (t1, l) ->
         All_cons (t1, l,
           (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
             x13 x14 x15 x16 t1), (aux_pparams l))
       in aux_pparams pparams0),
     (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
       x14 x15 x16 preturn0))) discr
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 discr) branches
    (let rec aux_arg = function
     | Coq_nil -> All_nil
     | Coq_cons (b, l) ->
       All_cons (b, l,
         (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
           x13 x14 x15 x16 b.bbody), (aux_arg l))
     in aux_arg branches)
| Coq_tProj (proj, t1) ->
  x12 proj t1
    (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
      x14 x15 x16 t1)
| Coq_tFix (mfix, idx) ->
  x13 mfix idx
    (let rec aux_arg = function
     | Coq_nil -> All_nil
     | Coq_cons (d, l) ->
       All_cons (d, l, (Coq_pair
         ((term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
            x13 x14 x15 x16 d.dtype),
         (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
           x13 x14 x15 x16 d.dbody))), (aux_arg l))
     in aux_arg mfix)
| Coq_tCoFix (mfix, idx) ->
  x14 mfix idx
    (let rec aux_arg = function
     | Coq_nil -> All_nil
     | Coq_cons (d, l) ->
       All_cons (d, l, (Coq_pair
         ((term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
            x13 x14 x15 x16 d.dtype),
         (term_forall_list_rect x x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
           x13 x14 x15 x16 d.dbody))), (aux_arg l))
     in aux_arg mfix)
| Coq_tInt i -> x15 i
| Coq_tFloat f -> x16 f

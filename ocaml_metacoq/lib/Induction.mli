open All_Forall
open Ast
open AstUtils
open BasicAst
open Datatypes
open Kernames
open PrimFloat
open PrimInt63
open Universes

val term_forall_list_rect :
  (nat -> 'a1) -> (ident -> 'a1) -> (nat -> term list -> (term, 'a1) coq_All
  -> 'a1) -> (Universe.t -> 'a1) -> (term -> 'a1 -> cast_kind -> term -> 'a1
  -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term
  -> 'a1 -> term -> 'a1 -> 'a1) -> (aname -> term -> 'a1 -> term -> 'a1 ->
  term -> 'a1 -> 'a1) -> (term -> 'a1 -> term list -> (term, 'a1) coq_All ->
  'a1) -> (kername -> Level.t list -> 'a1) -> (inductive -> Level.t list ->
  'a1) -> (inductive -> nat -> Level.t list -> 'a1) -> (case_info -> term
  predicate -> (term, 'a1, 'a1) tCasePredProp -> term -> 'a1 -> term branch
  list -> (term, 'a1) tCaseBrsType -> 'a1) -> (projection -> term -> 'a1 ->
  'a1) -> (term mfixpoint -> nat -> (term, 'a1, 'a1) tFixType -> 'a1) ->
  (term mfixpoint -> nat -> (term, 'a1, 'a1) tFixType -> 'a1) -> (int -> 'a1)
  -> (float -> 'a1) -> term -> 'a1

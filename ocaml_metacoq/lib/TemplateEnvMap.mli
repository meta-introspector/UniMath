open Ast
open Datatypes
open Kernames
open List
open Monad_utils

module GlobalEnvMap :
 sig
  type t = { env : Env.global_env; map : Env.global_decl EnvMap.EnvMap.t }

  val env : t -> Env.global_env

  val map : t -> Env.global_decl EnvMap.EnvMap.t

  val lookup_env : t -> kername -> Env.global_decl option

  val lookup_minductive : t -> kername -> Env.mutual_inductive_body option

  val lookup_inductive :
    t -> inductive -> (Env.mutual_inductive_body, Env.one_inductive_body)
    prod option

  val lookup_constructor :
    t -> inductive -> nat -> ((Env.mutual_inductive_body,
    Env.one_inductive_body) prod, Env.constructor_body) prod option

  val lookup_projection :
    t -> projection -> (((Env.mutual_inductive_body, Env.one_inductive_body)
    prod, Env.constructor_body) prod, Env.projection_body) prod option

  val make : Env.global_env -> t
 end

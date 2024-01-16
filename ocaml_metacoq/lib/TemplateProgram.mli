open Ast
open Byte
open Datatypes
open Specif
open TemplateEnvMap
open Typing
open Bytestring
open Config

type template_program = Env.program

type template_program_env = (GlobalEnvMap.t, term) prod

type wt_template_program = (wf_ext, (term, typing) sigT) prod

type wt_template_program_env = (wf_ext, (term, typing) sigT) prod

val make_template_program_env :
  checker_flags -> template_program -> template_program_env

val build_template_program_env :
  checker_flags -> (Env.global_env, GlobalEnvMap.t, term, term, term, term)
  Transform.Transform.t

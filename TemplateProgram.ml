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

(** val make_template_program_env :
    checker_flags -> template_program -> template_program_env **)

let make_template_program_env _ p =
  Coq_pair ((GlobalEnvMap.make (fst p)), (snd p))

(** val build_template_program_env :
    checker_flags -> (Env.global_env, GlobalEnvMap.t, term, term, term, term)
    Transform.Transform.t **)

let build_template_program_env cf =
  { Transform.Transform.name = (String.String (Coq_x72, (String.String
    (Coq_x65, (String.String (Coq_x62, (String.String (Coq_x75,
    (String.String (Coq_x69, (String.String (Coq_x6c, (String.String
    (Coq_x64, (String.String (Coq_x69, (String.String (Coq_x6e,
    (String.String (Coq_x67, (String.String (Coq_x20, (String.String
    (Coq_x65, (String.String (Coq_x6e, (String.String (Coq_x76,
    (String.String (Coq_x69, (String.String (Coq_x72, (String.String
    (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x6d,
    (String.String (Coq_x65, (String.String (Coq_x6e, (String.String
    (Coq_x74, (String.String (Coq_x20, (String.String (Coq_x6c,
    (String.String (Coq_x6f, (String.String (Coq_x6f, (String.String
    (Coq_x6b, (String.String (Coq_x75, (String.String (Coq_x70,
    (String.String (Coq_x20, (String.String (Coq_x74, (String.String
    (Coq_x61, (String.String (Coq_x62, (String.String (Coq_x6c,
    (String.String (Coq_x65,
    String.EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));
    Transform.Transform.transform = (fun p _ ->
    make_template_program_env cf p) }

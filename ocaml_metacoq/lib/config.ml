open Datatypes

type checker_flags = { check_univs : bool; prop_sub_type : bool;
                       indices_matter : bool;
                       lets_in_constructor_types : bool }

(** val check_univs : checker_flags -> bool **)

let check_univs checker_flags0 =
  checker_flags0.check_univs

(** val prop_sub_type : checker_flags -> bool **)

let prop_sub_type checker_flags0 =
  checker_flags0.prop_sub_type

(** val indices_matter : checker_flags -> bool **)

let indices_matter checker_flags0 =
  checker_flags0.indices_matter

(** val lets_in_constructor_types : checker_flags -> bool **)

let lets_in_constructor_types checker_flags0 =
  checker_flags0.lets_in_constructor_types

(** val default_checker_flags : checker_flags **)

let default_checker_flags =
  { check_univs = Coq_true; prop_sub_type = Coq_true; indices_matter =
    Coq_false; lets_in_constructor_types = Coq_true }

(** val type_in_type : checker_flags **)

let type_in_type =
  { check_univs = Coq_false; prop_sub_type = Coq_true; indices_matter =
    Coq_false; lets_in_constructor_types = Coq_true }

(** val extraction_checker_flags : checker_flags **)

let extraction_checker_flags =
  { check_univs = Coq_true; prop_sub_type = Coq_false; indices_matter =
    Coq_false; lets_in_constructor_types = Coq_false }

(** val impl : checker_flags -> checker_flags -> bool **)

let impl cf1 cf2 =
  match match match implb cf2.check_univs cf1.check_univs with
              | Coq_true -> implb cf1.prop_sub_type cf2.prop_sub_type
              | Coq_false -> Coq_false with
        | Coq_true -> implb cf2.indices_matter cf1.indices_matter
        | Coq_false -> Coq_false with
  | Coq_true ->
    implb cf1.lets_in_constructor_types cf2.lets_in_constructor_types
  | Coq_false -> Coq_false

(** val laxest_checker_flags : checker_flags **)

let laxest_checker_flags =
  { check_univs = Coq_false; prop_sub_type = Coq_true; indices_matter =
    Coq_false; lets_in_constructor_types = Coq_true }

(** val strictest_checker_flags : checker_flags **)

let strictest_checker_flags =
  { check_univs = Coq_true; prop_sub_type = Coq_false; indices_matter =
    Coq_true; lets_in_constructor_types = Coq_false }

(** val union_checker_flags :
    checker_flags -> checker_flags -> checker_flags **)

let union_checker_flags cf1 cf2 =
  { check_univs =
    (match cf2.check_univs with
     | Coq_true -> cf1.check_univs
     | Coq_false -> Coq_false); prop_sub_type =
    (match cf1.prop_sub_type with
     | Coq_true -> Coq_true
     | Coq_false -> cf2.prop_sub_type); indices_matter =
    (match cf2.indices_matter with
     | Coq_true -> cf1.indices_matter
     | Coq_false -> Coq_false); lets_in_constructor_types =
    (match cf1.lets_in_constructor_types with
     | Coq_true -> Coq_true
     | Coq_false -> cf2.lets_in_constructor_types) }

(** val inter_checker_flags :
    checker_flags -> checker_flags -> checker_flags **)

let inter_checker_flags cf1 cf2 =
  { check_univs =
    (match cf2.check_univs with
     | Coq_true -> Coq_true
     | Coq_false -> cf1.check_univs); prop_sub_type =
    (match cf1.prop_sub_type with
     | Coq_true -> cf2.prop_sub_type
     | Coq_false -> Coq_false); indices_matter =
    (match cf2.indices_matter with
     | Coq_true -> Coq_true
     | Coq_false -> cf1.indices_matter); lets_in_constructor_types =
    (match cf1.lets_in_constructor_types with
     | Coq_true -> cf2.lets_in_constructor_types
     | Coq_false -> Coq_false) }

open Datatypes

type checker_flags = { check_univs : bool; prop_sub_type : bool;
                       indices_matter : bool;
                       lets_in_constructor_types : bool }

val check_univs : checker_flags -> bool

val prop_sub_type : checker_flags -> bool

val indices_matter : checker_flags -> bool

val lets_in_constructor_types : checker_flags -> bool

val default_checker_flags : checker_flags

val type_in_type : checker_flags

val extraction_checker_flags : checker_flags

val impl : checker_flags -> checker_flags -> bool

val laxest_checker_flags : checker_flags

val strictest_checker_flags : checker_flags

val union_checker_flags : checker_flags -> checker_flags -> checker_flags

val inter_checker_flags : checker_flags -> checker_flags -> checker_flags


type equations_tag =
| Coq_the_equations_tag

(** val bang : equations_tag **)

let bang =
  Coq_the_equations_tag

(** val inaccessible_pattern : 'a1 -> 'a1 **)

let inaccessible_pattern t =
  t

module EquationsNotations =
 struct
 end

(** val fixproto : equations_tag **)

let fixproto =
  Coq_the_equations_tag

(** val hidebody : 'a1 -> 'a1 **)

let hidebody a =
  a

(** val pr1 : ('a1 * 'a2) -> 'a1 **)

let pr1 = function
| pr3,_ -> pr3

(** val pr2 : ('a1 * 'a2) -> 'a2 **)

let pr2 = function
| _,pr3 -> pr3

module Sigma_Notations =
 struct
 end


type equations_tag =
| Coq_the_equations_tag

val bang : equations_tag

val inaccessible_pattern : 'a1 -> 'a1

module EquationsNotations :
 sig
 end

val fixproto : equations_tag

val hidebody : 'a1 -> 'a1

val pr1 : ('a1 * 'a2) -> 'a1

val pr2 : ('a1 * 'a2) -> 'a2

module Sigma_Notations :
 sig
 end

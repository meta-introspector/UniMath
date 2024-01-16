
type __ = Obj.t

type coq_UU = __

type 'x fromUUtoType = 'x

type empty = |

val empty_rect : empty -> 'a1

val empty_rec : empty -> 'a1

type coq_unit =
| Coq_tt

val unit_rect : 'a1 -> coq_unit -> 'a1

val unit_rec : 'a1 -> coq_unit -> 'a1

type bool =
| Coq_true
| Coq_false

val bool_rect : 'a1 -> 'a1 -> bool -> 'a1

val bool_rec : 'a1 -> 'a1 -> bool -> 'a1

val negb : bool -> bool

type ('a, 'b) coprod =
| Coq_ii1 of 'a
| Coq_ii2 of 'b

val coprod_rect : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) coprod -> 'a3

val coprod_rec : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) coprod -> 'a3

type nat =
| O
| S of nat

val nat_rect : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

val nat_rec : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

val succ : nat -> nat

val add : nat -> nat -> nat

val sub : nat -> nat -> nat

val mul : nat -> nat -> nat

val max : nat -> nat -> nat

val min : nat -> nat -> nat

type 'a paths =
| Coq_paths_refl

val paths_rect : 'a1 -> 'a2 -> 'a1 -> 'a1 paths -> 'a2

val paths_rec : 'a1 -> 'a2 -> 'a1 -> 'a1 paths -> 'a2

type ('t, 'p) total2 = { pr1 : 't; pr2 : 'p }

val total2_rect : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3

val total2_rec : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3

val pr1 : ('a1, 'a2) total2 -> 'a1

val pr2 : ('a1, 'a2) total2 -> 'a2

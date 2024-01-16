
type empty = |

type coq_unit =
| Coq_tt

type bool =
| Coq_true
| Coq_false

type ('a, 'b) coprod =
| Coq_ii1 of 'a
| Coq_ii2 of 'b

type nat =
| O
| S of nat

type 'a paths =
| Coq_paths_refl

type ('t, 'p) total2 = { pr1 : 't; pr2 : 'p }

open All_Forall
open Datatypes
open PeanoNat
open Specif

type __ = Obj.t

type 'm coq_Monad = { ret : (__ -> __ -> 'm);
                      bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

val ret : 'a1 coq_Monad -> 'a2 -> 'a1

val bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1

type ('e, 'm) coq_MonadExc = { raise : (__ -> 'e -> 'm);
                               catch : (__ -> 'm -> ('e -> 'm) -> 'm) }

val raise : ('a1, 'a2) coq_MonadExc -> 'a1 -> 'a2

val catch : ('a1, 'a2) coq_MonadExc -> 'a2 -> ('a1 -> 'a2) -> 'a2

module MCMonadNotation :
 sig
 end

val option_monad : __ option coq_Monad

val id_monad : __ coq_Monad

val option_monad_exc : (coq_unit, __ option) coq_MonadExc

val mapopt : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option

val monad_map : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1

val monad_option_map : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 option -> 'a1

val monad_fold_left :
  'a1 coq_Monad -> ('a2 -> 'a3 -> 'a1) -> 'a3 list -> 'a2 -> 'a1

val monad_fold_right :
  'a1 coq_Monad -> ('a2 -> 'a3 -> 'a1) -> 'a3 list -> 'a2 -> 'a1

val monad_map_i_aux :
  'a1 coq_Monad -> (nat -> 'a2 -> 'a1) -> nat -> 'a2 list -> 'a1

val monad_map_i : 'a1 coq_Monad -> (nat -> 'a2 -> 'a1) -> 'a2 list -> 'a1

val monad_map2 :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> ('a3 -> 'a4 -> 'a1) -> 'a2 ->
  'a3 list -> 'a4 list -> 'a1

val monad_iter : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1

val monad_All : 'a1 coq_Monad -> ('a2 -> 'a1) -> 'a2 list -> 'a1

val monad_All2 :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> 'a2 -> ('a3 -> 'a4 -> 'a1) ->
  'a3 list -> 'a4 list -> 'a1

val monad_prod : 'a1 coq_Monad -> 'a1 -> 'a1 -> 'a1

val check_dec :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> 'a2 -> sumbool -> 'a1

val check_eq_true :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> bool -> 'a2 -> 'a1

val check_eq_nat :
  'a1 coq_Monad -> ('a2, 'a1) coq_MonadExc -> nat -> nat -> 'a2 -> 'a1

val monad_Alli :
  'a1 coq_Monad -> (nat -> 'a2 -> 'a1) -> 'a2 list -> nat -> 'a1

val monad_Alli_All :
  'a1 coq_Monad -> (nat -> 'a2 -> __ -> 'a1) -> 'a2 list -> nat -> 'a1

val monad_Alli_nth_gen :
  'a1 coq_Monad -> 'a2 list -> nat -> (nat -> 'a2 -> __ -> 'a1) -> 'a1

val monad_Alli_nth :
  'a1 coq_Monad -> 'a2 list -> (nat -> 'a2 -> __ -> 'a1) -> 'a1

val monad_All_All : 'a1 coq_Monad -> ('a2 -> __ -> 'a1) -> 'a2 list -> 'a1

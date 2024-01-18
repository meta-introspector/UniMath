
type __ = Obj.t

val eq_dep_rect : 'a1 -> 'a2 -> 'a3 -> 'a1 -> 'a2 -> 'a3

val eq_dep_rec : 'a1 -> 'a2 -> 'a3 -> 'a1 -> 'a2 -> 'a3

val eq_dep1_rect : 'a1 -> 'a2 -> 'a1 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val eq_dep1_rec : 'a1 -> 'a2 -> 'a1 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3

val internal_eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2

module type EqdepElimination =
 sig
 end

module EqdepTheory :
 functor (M:EqdepElimination) ->
 sig
 end

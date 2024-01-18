
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val eq_dep_rect : 'a1 -> 'a2 -> 'a3 -> 'a1 -> 'a2 -> 'a3 **)

let eq_dep_rect _ _ f _ _ =
  f

(** val eq_dep_rec : 'a1 -> 'a2 -> 'a3 -> 'a1 -> 'a2 -> 'a3 **)

let eq_dep_rec _ _ f _ _ =
  f

(** val eq_dep1_rect :
    'a1 -> 'a2 -> 'a1 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_dep1_rect _ _ _ _ f =
  f __ __

(** val eq_dep1_rec : 'a1 -> 'a2 -> 'a1 -> 'a2 -> (__ -> __ -> 'a3) -> 'a3 **)

let eq_dep1_rec _ _ _ _ f =
  f __ __

(** val internal_eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2 **)

let internal_eq_rew_r_dep _ _ hC =
  hC

module type EqdepElimination =
 sig
 end

module EqdepTheory =
 functor (M:EqdepElimination) ->
 struct
 end

open Propositions
open Sets

(** val hasSmallest : 'a1 hrel -> hProp **)

let hasSmallest _ =
  forall_hProp (fun _ -> himpl ishinh)

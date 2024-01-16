open Propositions

(** val hequiv : hProp -> hProp -> hProp **)

let hequiv p q =
  hconj (himpl q) (himpl p)

(** val total2_hProp : hProp -> (hProptoType -> hProp) -> hProp **)

let total2_hProp x y =
  make_hProp (isaprop_total2 x y)

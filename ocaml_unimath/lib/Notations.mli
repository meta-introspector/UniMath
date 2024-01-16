open Propositions

type hProp = ()
             
val hequiv : hProp -> hProp -> hProp

val total2_hProp : hProp -> (hProptoType -> hProp) -> hProp

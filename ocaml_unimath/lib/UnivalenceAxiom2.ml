open PartA
open PartB
open PartD
open Preamble
open UnivalenceAxiom

(** val isaprop_univalenceStatement : univalenceStatement isaprop **)

let isaprop_univalenceStatement =
  impred_isaprop (fun _ -> impred_isaprop (fun _ -> isapropisweq eqweqmap))

(** val isaprop_funextemptyStatement : funextemptyStatement isaprop **)

let isaprop_funextemptyStatement =
  impred_isaprop (fun _ ->
    impred_isaprop (fun f ->
      impred_isaprop (fun g -> impred_isaset (fun _ -> isasetempty) f g)))

(** val isaprop_isweqtoforallpathsStatement :
    isweqtoforallpathsStatement isaprop **)

let isaprop_isweqtoforallpathsStatement =
  impred_isaprop (fun _ ->
    impred_isaprop (fun _ ->
      impred_isaprop (fun f ->
        impred_isaprop (fun g -> isapropisweq (toforallpaths f g)))))

(** val isaprop_propositionalUnivalenceStatement :
    propositionalUnivalenceStatement isaprop **)
let univalence =
  univalenceUAH (fun _ _ -> univalenceAxiom)

let isaprop_propositionalUnivalenceStatement =
  impred_isaprop (fun _ ->
    impred_isaprop (fun _ ->
      impred_isaprop (fun _ ->
        impred_isaprop (fun j ->
          impred_isaprop (fun _ ->
            impred_isaprop (fun _ ->
              isofhlevelweqb (S O) univalence (isapropweqtoprop j)))))))

(** val isaprop_funcontrStatement : funcontrStatement isaprop **)

let isaprop_funcontrStatement =
  impred_isaprop (fun _ ->
    impred_isaprop (fun _ -> impred_isaprop (fun _ -> isapropiscontr)))

(** val isaprop_funextcontrStatement : funextcontrStatement isaprop **)

let isaprop_funextcontrStatement =
  impred_isaprop (fun _ ->
    impred_isaprop (fun _ -> impred_isaprop (fun _ -> isapropiscontr)))

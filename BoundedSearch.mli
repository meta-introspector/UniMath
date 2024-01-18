open NaturalNumbers
open PartA
open PartB
open PartD
open Preamble
open Propositions
open Propositions0

type minimal = nat -> hProptoType -> hProptoType

val isapropminimal : (nat -> hProp) -> nat -> minimal isaprop

type min_n_UUU = (nat, (hProptoType, minimal) dirprod) total2

val isapropmin_n : (nat -> hProp) -> min_n_UUU isaprop

val min_n : (nat -> hProp) -> hProp

type smaller =
  (nat, (hProptoType, (minimal, hProptoType) dirprod) dirprod) total2

val smaller_S : (nat -> hProp) -> nat -> smaller -> smaller

val bounded_search :
  (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) -> nat ->
  (smaller, nat -> hProptoType -> hProptoType neg) coprod

val n_to_min_n :
  (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) -> nat ->
  hProptoType -> hProptoType

val prop_n_to_min_n :
  (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) ->
  hProptoType -> hProptoType

val minimal_n :
  (nat -> hProp) -> (nat -> (hProptoType, hProptoType neg) coprod) ->
  hProptoType -> (nat, hProptoType) total2

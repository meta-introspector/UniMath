open DecidablePropositions
open PartA
open PartB
open PartC
open Preamble
open Propositions
open Sets

val pr1_issurjective :
  ('a1 -> hProptoType) -> (('a1, 'a2) total2, 'a1) issurjective

val eqrel_on_bool : hProp -> pr1hSet eqrel

val eqrel_on_bool_iff : hProp -> (pr1hSet setquot paths, hProptoType) logeq

val coq_AC_impl2 : (hProptoType, hProptoType) logeq

val coq_AC_to_LEM : hProptoType -> hProptoType

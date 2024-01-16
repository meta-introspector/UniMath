open PartA
open Preamble
open Propositions

type 'x isdecrel = 'x -> 'x -> (hProptoType, hProptoType neg) coprod

type 'x isantisymm = 'x -> 'x -> hProptoType -> hProptoType -> 'x paths

open Notations
open PartA
open PartB
open PartD
open Preamble
open Propositions

type ('x, 'y) nullHomotopyTo = 'x -> 'y paths

type ('x, 'y) coq_NullHomotopyTo = ('y, ('x, 'y) nullHomotopyTo) total2

val coq_NullHomotopyTo_center :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyTo -> 'a2

val coq_NullHomotopyTo_path :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyTo -> ('a1, 'a2) nullHomotopyTo

type ('x, 'y) nullHomotopyFrom = 'x -> 'y paths

type ('x, 'y) coq_NullHomotopyFrom = ('y, ('x, 'y) nullHomotopyFrom) total2

val coq_NullHomotopyFrom_center :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyFrom -> 'a2

val coq_NullHomotopyFrom_path :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyFrom -> ('a1, 'a2)
  nullHomotopyFrom

val nullHomotopyTo_transport :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) nullHomotopyTo -> 'a2 -> 'a2 paths -> 'a1
  -> 'a2 paths paths

val isaset_NullHomotopyTo :
  'a2 isaset -> ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyTo isaset

val isaprop_nullHomotopyTo :
  'a2 isaset -> ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) nullHomotopyTo isaprop

val isaprop_NullHomotopyTo :
  'a2 isaset -> ('a1 -> 'a2) -> hProptoType -> ('a1, 'a2) coq_NullHomotopyTo
  isaprop

val cone_squash_map :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) nullHomotopyTo -> hProptoType -> 'a2

val coq_Unnamed_thm :
  'a2 -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1 -> 'a2) paths

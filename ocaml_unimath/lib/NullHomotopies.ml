open Notations
open PartA
open PartB
open PartD
open Preamble
open Propositions

type ('x, 'y) nullHomotopyTo = 'x -> 'y paths

type ('x, 'y) coq_NullHomotopyTo = ('y, ('x, 'y) nullHomotopyTo) total2

(** val coq_NullHomotopyTo_center :
    ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyTo -> 'a2 **)

let coq_NullHomotopyTo_center _ t =
  t.pr1

(** val coq_NullHomotopyTo_path :
    ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyTo -> ('a1, 'a2) nullHomotopyTo **)

let coq_NullHomotopyTo_path _ r =
  r.pr2

type ('x, 'y) nullHomotopyFrom = 'x -> 'y paths

type ('x, 'y) coq_NullHomotopyFrom = ('y, ('x, 'y) nullHomotopyFrom) total2

(** val coq_NullHomotopyFrom_center :
    ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyFrom -> 'a2 **)

let coq_NullHomotopyFrom_center _ t =
  t.pr1

(** val coq_NullHomotopyFrom_path :
    ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyFrom -> ('a1, 'a2)
    nullHomotopyFrom **)

let coq_NullHomotopyFrom_path _ r =
  r.pr2

(** val nullHomotopyTo_transport :
    ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) nullHomotopyTo -> 'a2 -> 'a2 paths ->
    'a1 -> 'a2 paths paths **)

let nullHomotopyTo_transport f y h _ _ x =
  pathsinv0 (pathscomp0 (f x) y y (h x) Coq_paths_refl)
    (transportf y y Coq_paths_refl h x)
    (pathscomp0rid (f x) y (transportf y y Coq_paths_refl h x))

(** val isaset_NullHomotopyTo :
    'a2 isaset -> ('a1 -> 'a2) -> ('a1, 'a2) coq_NullHomotopyTo isaset **)

let isaset_NullHomotopyTo i f =
  Obj.magic isofhleveltotal2 (S (S O)) i (fun y ->
    impred (S (S O)) (fun x -> Obj.magic isasetaprop (i (f x) y)))

(** val isaprop_nullHomotopyTo :
    'a2 isaset -> ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) nullHomotopyTo isaprop **)

let isaprop_nullHomotopyTo is f y =
  impred (S O) (fun x -> is (f x) y)

(** val isaprop_NullHomotopyTo :
    'a2 isaset -> ('a1 -> 'a2) -> hProptoType -> ('a1, 'a2)
    coq_NullHomotopyTo isaprop **)

let isaprop_NullHomotopyTo is f =
  factor_through_squash isapropisaprop (fun x ->
    invproofirrelevance (fun x0 ->
      let r = x0.pr1 in
      let i = x0.pr2 in
      (fun y ->
      let s = y.pr1 in
      let j = y.pr2 in
      subtypePairEquality (fun n -> isaprop_nullHomotopyTo is f n) r s i j
        (pathscomp0 r (f x) s (pathsinv0 (f x) r (i x)) (j x)))))

(** val cone_squash_map :
    ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) nullHomotopyTo -> hProptoType -> 'a2 **)

let cone_squash_map f y e h =
  point_from y
    (Obj.magic h (paths_to_prop y) (fun x -> { pr1 = (f x); pr2 = (e x) }))

(** val coq_Unnamed_thm :
    'a2 -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1 -> 'a2) paths **)

let coq_Unnamed_thm _ _ _ =
  Coq_paths_refl

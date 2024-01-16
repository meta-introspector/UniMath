open Preamble

(** val andb : bool -> bool -> bool **)

let andb b1 b2 =
  match b1 with
  | Coq_true -> b2
  | Coq_false -> Coq_false

(** val orb : bool -> bool -> bool **)

let orb b1 b2 =
  match b1 with
  | Coq_true -> Coq_true
  | Coq_false -> b2

(** val implb : bool -> bool -> bool **)

let implb b1 b2 =
  match b1 with
  | Coq_true -> b2
  | Coq_false -> Coq_true

(** val andb_is_associative : bool -> bool -> bool -> bool paths **)

let andb_is_associative _ _ _ =
  Coq_paths_refl

(** val orb_is_associative : bool -> bool -> bool -> bool paths **)

let orb_is_associative _ _ _ =
  Coq_paths_refl

(** val andb_is_commutative : bool -> bool -> bool paths **)

let andb_is_commutative _ _ =
  Coq_paths_refl

(** val orb_is_commutative : bool -> bool -> bool paths **)

let orb_is_commutative _ _ =
  Coq_paths_refl

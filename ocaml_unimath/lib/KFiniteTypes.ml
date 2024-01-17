open FiniteSets
open PartA
open PartA0
open Preamble
open Propositions
open StandardFiniteSets

type 'x kfinstruct = (nat, (stn -> 'x, (stn, 'x) issurjective) total2) total2

(** val make_kfinstruct :
    nat -> (stn -> 'a1) -> (stn, 'a1) issurjective -> 'a1 kfinstruct **)

let make_kfinstruct n f fsurjective =
  { pr1 = n; pr2 = { pr1 = f; pr2 = fsurjective } }

(** val kfinstruct_cardinality : 'a1 kfinstruct -> nat **)

let kfinstruct_cardinality f =
  f.pr1

(** val kfinstruct_map : 'a1 kfinstruct -> stn -> 'a1 **)

let kfinstruct_map f =
  f.pr2.pr1

(** val issurjective_kfinstruct :
    'a1 kfinstruct -> (stn, 'a1) issurjective **)

let issurjective_kfinstruct f =
  f.pr2.pr2

(** val kfinstruct_from_surjection :
    ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> 'a1 kfinstruct -> 'a2
    kfinstruct **)

let kfinstruct_from_surjection g gsurjective f =
  make_kfinstruct (kfinstruct_cardinality f) (funcomp (kfinstruct_map f) g)
    (issurjcomp (kfinstruct_map f) g (issurjective_kfinstruct f) gsurjective)

(** val kfinstruct_weqf :
    ('a1, 'a2) weq -> 'a1 kfinstruct -> 'a2 kfinstruct **)

let kfinstruct_weqf w =
  kfinstruct_from_surjection (pr1weq w)
    (issurjectiveweq (pr1weq w) (weqproperty w))

(** val kfinstruct_weqb :
    ('a1, 'a2) weq -> 'a2 kfinstruct -> 'a1 kfinstruct **)

let kfinstruct_weqb w =
  kfinstruct_from_surjection (invmap w)
    (issurjectiveweq (invmap w) (isweqinvmap w))

(** val kfinstruct_contr : 'a1 iscontr -> 'a1 kfinstruct **)

let kfinstruct_contr contr = contr
  (* make_kfinstruct (S O) (fun _ -> iscontrpr1 contr) *)
  (*   (issurjective_to_contr { pr1 = O; pr2 = Coq_paths_refl } (fun _ -> *)
  (*     iscontrpr1 contr) contr) *)

(** val kfinstruct_coprod :
    'a1 kfinstruct -> 'a2 kfinstruct -> ('a1, 'a2) coprod kfinstruct **)

let kfinstruct_coprod f g = f g
  (* let n = kfinstruct_cardinality f in *)
  (* let m = kfinstruct_cardinality g in *)
  (* make_kfinstruct (add n m) *)
  (*   (funcomp (pr1weq (invweq (weqfromcoprodofstn n m))) *)
  (*     (coprodf (kfinstruct_map f) (kfinstruct_map g))) *)
  (*   (issurjcomp (pr1weq (invweq (weqfromcoprodofstn n m))) *)
  (*     (coprodf (kfinstruct_map f) (kfinstruct_map g)) *)
  (*     (issurjectiveweq (pr1weq (invweq (weqfromcoprodofstn n m))) *)
  (*       (weqproperty (invweq (weqfromcoprodofstn n m)))) *)
  (*     (issurjective_coprodf (kfinstruct_map f) (kfinstruct_map g) *)
  (*       (issurjective_kfinstruct f) (issurjective_kfinstruct g))) *)

(** val kfinstruct_dirprod :
    'a1 kfinstruct -> 'a2 kfinstruct -> ('a1, 'a2) dirprod kfinstruct **)

let kfinstruct_dirprod f g = f g
  (* let k = kfinstruct_cardinality f in *)
  (* let l = kfinstruct_cardinality g in *)
  (* make_kfinstruct (mul k l) *)
  (*   (funcomp (pr1weq (invweq (weqfromprodofstn k l))) *)
  (*     (dirprodf (kfinstruct_map f) (kfinstruct_map g))) *)
  (*   (issurjcomp (pr1weq (invweq (weqfromprodofstn k l))) *)
  (*     (dirprodf (kfinstruct_map f) (kfinstruct_map g)) *)
  (*     (issurjectiveweq (pr1weq (invweq (weqfromprodofstn k l))) *)
  (*       (weqproperty (invweq (weqfromprodofstn k l)))) *)
  (*     (issurjective_dirprodf (kfinstruct_map f) (kfinstruct_map g) *)
  (*       (issurjective_kfinstruct f) (issurjective_kfinstruct g))) *)

(** val kfinstruct_finstruct : 'a1 finstruct -> 'a1 kfinstruct **)

let kfinstruct_finstruct finstr =
  make_kfinstruct finstr.pr1 (let x0 = finstr.pr2 in x0.pr1)
    (issurjectiveweq (let x0 = finstr.pr2 in x0.pr1) (weqproperty finstr.pr2))

(** val kfinstruct_unit : coq_unit kfinstruct **)

let kfinstruct_unit =
  kfinstruct_contr iscontrunit

(** val kfinstruct_bool : bool kfinstruct **)

let kfinstruct_bool =false
  (* make_kfinstruct (S (S O)) (two_rec Coq_false Coq_true) (fun b -> *)
  (*   match b with *)
  (*   | Coq_true -> *)
  (*     hinhpr { pr1 = { pr1 = (S O); pr2 = Coq_paths_refl }; pr2 = *)
  (*       Coq_paths_refl } *)
  (*   | Coq_false -> *)
  (*     hinhpr { pr1 = { pr1 = O; pr2 = Coq_paths_refl }; pr2 = Coq_paths_refl }) *)

(** val kfinstruct_stn : nat -> stn kfinstruct **)

let kfinstruct_stn n = n
  (* make_kfinstruct n idfun issurjective_idfun *)

(** val kfinstruct_stn_indexed :
    nat -> (stn -> 'a1 kfinstruct) -> (stn, 'a1) total2 kfinstruct **)

let kfinstruct_stn_indexed n index = n
  (* let j = fun j -> kfinstruct_cardinality (index j) in *)
  (* kfinstruct_from_surjection *)
  (*   (totalfun (let x = fun k -> (index k).pr2 in fun k -> (x k).pr1)) *)
  (*   (issurjective_totalfun *)
  (*     (let x = fun k -> (index k).pr2 in fun k -> (x k).pr1) (fun x -> *)
  (*     issurjective_kfinstruct (index x))) *)
  (*   (kfinstruct_weqb (weqstnsum1 n j) (kfinstruct_stn (stnsum n j))) *)

type 'x iskfinite = hProptoType

(** val kfinstruct_iskfinite : 'a1 kfinstruct -> 'a1 iskfinite **)

let kfinstruct_iskfinite =
  hinhpr

(** val iskfinite_weqf : ('a1, 'a2) weq -> 'a1 iskfinite -> 'a2 iskfinite **)

let iskfinite_weqf w =
  hinhfun (kfinstruct_weqf w)

(** val iskfinite_weqb : ('a1, 'a2) weq -> 'a2 iskfinite -> 'a1 iskfinite **)

let iskfinite_weqb w =
  hinhfun (kfinstruct_weqb w)

(** val iskfinite_from_surjection :
    ('a1 -> 'a2) -> ('a1, 'a2) issurjective -> 'a1 iskfinite -> 'a2 iskfinite **)

let iskfinite_from_surjection f fsurjective =
  hinhfun (kfinstruct_from_surjection f fsurjective)

(** val iskfinite_unit : coq_unit iskfinite **)

let iskfinite_unit =
  hinhpr kfinstruct_unit

(** val iskfinite_bool : bool iskfinite **)

let iskfinite_bool =
  hinhpr kfinstruct_bool

(** val iskfinite_contr : 'a1 iscontr -> 'a1 iskfinite **)

let iskfinite_contr xcontr =
  hinhpr (kfinstruct_contr xcontr)

(** val iskfinite_coprod :
    'a1 iskfinite -> 'a2 iskfinite -> ('a1, 'a2) coprod iskfinite **)

let iskfinite_coprod x =
  hinhfun2 kfinstruct_coprod x

(** val iskfinite_dirprod :
    'a1 iskfinite -> 'a2 iskfinite -> ('a1, 'a2) dirprod iskfinite **)

let iskfinite_dirprod x =
  hinhfun2 kfinstruct_dirprod x

(** val iskfinite_isfinite : hProptoType -> 'a1 iskfinite **)

let iskfinite_isfinite x =
  hinhfun kfinstruct_finstruct x

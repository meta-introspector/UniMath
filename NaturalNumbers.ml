open PartA
open PartB
open Preamble
open Propositions
open Sets

(** val negpaths0sx : nat -> nat paths neg **)

let negpaths0sx x =
  let f = fun n -> match n with
                   | O -> Coq_true
                   | S _ -> Coq_false in
  negf (maponpaths f O (S x)) nopathstruetofalse

(** val negpathssx0 : nat -> nat paths neg **)

let negpathssx0 x x0 =
  negpaths0sx x (pathsinv0 (S x) O x0)

(** val invmaponpathsS : nat -> nat -> nat paths -> nat paths **)

let invmaponpathsS n m e =
  let f = fun n0 -> match n0 with
                    | O -> O
                    | S m0 -> m0 in
  maponpaths f (S n) (S m) e

(** val noeqinjS : nat -> nat -> nat paths neg -> nat paths neg **)

let noeqinjS x x' =
  negf (invmaponpathsS x x')

(** val natneq_iff_neq : nat -> nat -> (nat paths neg, hProptoType) logeq **)

let rec natneq_iff_neq = function
| O ->
  (fun m ->
    match m with
    | O -> logeq_both_false (fun n0 -> n0 Coq_paths_refl) (Obj.magic idfun)
    | S n0 -> logeq_both_true (negpaths0sx n0) (Obj.magic Coq_tt))
| S n0 ->
  let n1 = natneq_iff_neq n0 in
  (fun m ->
  match m with
  | O -> logeq_both_true (negpathssx0 n0) (Obj.magic Coq_tt)
  | S n2 ->
    { pr1 = (fun ne ->
      (n1 n2).pr1 (fun r -> ne (maponpaths (fun x -> S x) n0 n2 r))); pr2 =
      (fun neq -> noeqinjS n0 n2 ((n1 n2).pr2 neq)) })

(** val nat_nopath_to_neq : nat -> nat -> nat paths neg -> hProptoType **)

let nat_nopath_to_neq n m =
  (natneq_iff_neq n m).pr1

(** val isdeceqnat : nat isdeceq **)

let rec isdeceqnat n x' =
  match n with
  | O ->
    (match x' with
     | O -> Coq_ii1 Coq_paths_refl
     | S n0 -> Coq_ii2 (negpaths0sx n0))
  | S n0 ->
    (match x' with
     | O -> Coq_ii2 (negpathssx0 n0)
     | S n1 ->
       let d = isdeceqnat n0 n1 in
       (match d with
        | Coq_ii1 a -> Coq_ii1 (maponpaths (fun x -> S x) n0 n1 a)
        | Coq_ii2 b -> Coq_ii2 (noeqinjS n0 n1 b)))

(** val natgtb : nat -> nat -> bool **)

let rec natgtb n m =
  match n with
  | O -> Coq_false
  | S n0 -> (match m with
             | O -> Coq_true
             | S m0 -> natgtb n0 m0)

(** val natgthsnn : nat -> hProptoType **)

let rec natgthsnn = function
| O -> Obj.magic Coq_paths_refl
| S n0 -> natgthsnn n0

(** val natgthsn0 : nat -> hProptoType **)

let natgthsn0 _ =
  Obj.magic Coq_paths_refl

(** val nat1gthtois0 : nat -> hProptoType -> nat paths **)

let nat1gthtois0 n _ =
  match n with
  | O -> Coq_paths_refl
  | S _ -> assert false (* absurd case *)

(** val istransnatgth :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let rec istransnatgth n m k =
  match n with
  | O -> (fun _ -> assert false (* absurd case *))
  | S n0 ->
    (match m with
     | O -> (fun _ _ -> assert false (* absurd case *))
     | S n1 ->
       (match k with
        | O -> (fun _ _ -> natgthsn0 n0)
        | S n2 -> istransnatgth n0 n1 n2))

(** val isdecrelnatgth : nat isdecrel **)

let isdecrelnatgth n m =
  Obj.magic isdeceqbool (natgtb n m) Coq_true

(** val natlthnsn : nat -> hProptoType **)

let natlthnsn =
  natgthsnn

(** val natlth1tois0 : nat -> hProptoType -> nat paths **)

let natlth1tois0 =
  nat1gthtois0

(** val negnatgthtoleh : nat -> nat -> hProptoType neg -> hProptoType **)

let rec negnatgthtoleh n m r =
  match n with
  | O -> natgthsn0 m
  | S n0 ->
    (match m with
     | O -> assert false (* absurd case *)
     | S n1 -> negnatgthtoleh n0 n1 r)

(** val natleh0tois0 : nat -> hProptoType -> nat paths **)

let natleh0tois0 =
  natlth1tois0

(** val natleh0n : nat -> hProptoType **)

let natleh0n =
  natgthsn0

(** val istransnatleh :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let istransnatleh n _ k _ _ =
  negnatgthtoleh n k (fun _ -> assert false (* absurd case *))

(** val isreflnatleh : nat -> hProptoType **)

let isreflnatleh =
  natgthsnn

(** val isantisymmnatleh : nat isantisymm **)

let rec isantisymmnatleh n n0 _H s =
  match n with
  | O -> pathsinv0 n0 O (nat1gthtois0 n0 s)
  | S n1 ->
    (match n0 with
     | O -> assert false (* absurd case *)
     | S n2 -> maponpaths (fun x -> S x) n1 n2 (isantisymmnatleh n1 n2 _H s))

(** val natlthtoleh : nat -> nat -> hProptoType -> hProptoType **)

let rec natlthtoleh m n r =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 -> (match m with
             | O -> natgthsn0 (S n0)
             | S n1 -> natlthtoleh n1 n0 r)

(** val natgehn0 : nat -> hProptoType **)

let natgehn0 =
  natleh0n

(** val istransnatgeh :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let istransnatgeh n m k gnm gmk =
  istransnatleh k m n gmk gnm

(** val natgthorleh : nat -> nat -> (hProptoType, hProptoType) coprod **)

let natgthorleh n m =
  let c = isdecrelnatgth n m in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 (negnatgthtoleh n m b))

(** val natlthorgeh : nat -> nat -> (hProptoType, hProptoType) coprod **)

let natlthorgeh n m =
  natgthorleh m n

(** val natneqchoice :
    nat -> nat -> hProptoType -> (hProptoType, hProptoType) coprod **)

let natneqchoice n m _ =
  let c = natgthorleh n m in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 _ ->
     let c0 = natlthorgeh n m in
     (match c0 with
      | Coq_ii1 a -> Coq_ii2 a
      | Coq_ii2 _ -> assert false (* absurd case *)))

(** val natgehchoice :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natgehchoice n m g =
  let c = natgthorleh n m in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 (isantisymmnatleh n m b g))

(** val natgthgehtrans :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natgthgehtrans n m k gnm gmk =
  let c = natgehchoice m k gmk in
  (match c with
   | Coq_ii1 a -> istransnatgth n m k gnm a
   | Coq_ii2 b -> internal_paths_rew m gnm k b)

(** val natlehlthtrans :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natlehlthtrans n m k l1 l2 =
  natgthgehtrans k m n l2 l1

(** val natgthtogehsn : nat -> nat -> hProptoType -> hProptoType **)

let rec natgthtogehsn n m x =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 -> (match m with
             | O -> natgehn0 n0
             | S n1 -> natgthtogehsn n0 n1 x)

(** val natlthtolehsn : nat -> nat -> hProptoType -> hProptoType **)

let natlthtolehsn n m x =
  natgthtogehsn m n x

(** val natlthsntoleh : nat -> nat -> hProptoType -> hProptoType **)

let natlthsntoleh n m a =
  natlthtolehsn n (S m) a

(** val natplusr0 : nat -> nat paths **)

let rec natplusr0 = function
| O -> Coq_paths_refl
| S n0 -> maponpaths (fun x -> S x) (add n0 O) n0 (natplusr0 n0)

(** val natplusnsm : nat -> nat -> nat paths **)

let rec natplusnsm n m =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    maponpaths (fun x -> S x) (add n0 (S m)) (S (add n0 m)) (natplusnsm n0 m)

(** val natpluscomm : nat -> nat -> nat paths **)

let rec natpluscomm n m =
  match n with
  | O -> pathsinv0 (add m O) (add O m) (natplusr0 (add O m))
  | S n0 ->
    let int = natpluscomm n0 (S m) in
    let int2 = pathsinv0 (add n0 (S m)) (add (S n0) m) (natplusnsm n0 m) in
    let int3 = pathsinv0 (add m (S n0)) (add (S m) n0) (natplusnsm m n0) in
    let int4 =
      pathscomp0 (add (S n0) m) (add n0 (S m)) (add (S m) n0) int2 int
    in
    pathscomp0 (add (S n0) m) (add (S m) n0) (add m (S n0)) int4 int3

(** val natplusassoc : nat -> nat -> nat -> nat paths **)

let rec natplusassoc n m k =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    maponpaths (fun x -> S x) (add (add n0 m) k) (add n0 (add m k))
      (natplusassoc n0 m k)

(** val natgthandplusl : nat -> nat -> nat -> hProptoType -> hProptoType **)

let rec natgthandplusl n m k l =
  match k with
  | O -> l
  | S n0 -> natgthandplusl n m n0 l

(** val natgthandplusr : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natgthandplusr n m k x =
  internal_paths_rew_r (add n k) (add k n)
    (internal_paths_rew_r (add m k) (add k m) (natgthandplusl n m k x)
      (natpluscomm m k)) (natpluscomm n k)

(** val natgthandpluslinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let rec natgthandpluslinv n m k l =
  match k with
  | O -> l
  | S n0 -> natgthandpluslinv n m n0 l

(** val natgthandplusrinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natgthandplusrinv n m k l =
  let l0 = internal_paths_rew (add n k) l (add k n) (natpluscomm n k) in
  let l1 = internal_paths_rew (add m k) l0 (add k m) (natpluscomm m k) in
  natgthandpluslinv n m k l1

(** val natlehtolehs : nat -> nat -> hProptoType -> hProptoType **)

let natlehtolehs n m is =
  istransnatleh n m (S m) is (natlthtoleh m (S m) (natlthnsn m))

(** val natlehmplusnm : nat -> nat -> hProptoType **)

let rec natlehmplusnm n m =
  match n with
  | O -> isreflnatleh m
  | S n0 ->
    natlehtolehs m
      (let rec add0 n1 m0 =
         match n1 with
         | O -> m0
         | S p -> S (add0 p m0)
       in add0 n0 m) (natlehmplusnm n0 m)

(** val plus_n_Sm : nat -> nat -> nat paths **)

let rec plus_n_Sm n m =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    maponpaths (fun x -> S x) (S (add n0 m)) (add n0 (S m)) (plus_n_Sm n0 m)

(** val natlehandplusl : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlehandplusl n m k r =
  internal_paths_rew_r (S (add k m)) (add k (S m))
    (natgthandplusl (S m) n k r) (plus_n_Sm k m)

(** val natlehandplusr : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlehandplusr n m k r =
  natgthandplusr (S m) n k r

(** val natlehandpluslinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlehandpluslinv n m k r =
  let r0 = internal_paths_rew (S (add k m)) r (add k (S m)) (plus_n_Sm k m) in
  natgthandpluslinv (S m) n k r0

(** val natlehandplusrinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlehandplusrinv n m k r =
  natgthandplusrinv (S m) n k r

(** val natlthp1toleh : nat -> nat -> hProptoType -> hProptoType **)

let natlthp1toleh =
  natlthsntoleh

(** val natminuseqn : nat -> nat paths **)

let natminuseqn _ =
  Coq_paths_refl

(** val minusplusnmm : nat -> nat -> hProptoType -> nat paths **)

let rec minusplusnmm = function
| O -> natleh0tois0
| S n0 ->
  (fun m is ->
    match m with
    | O -> internal_paths_rew_r (add n0 O) n0 Coq_paths_refl (natplusr0 n0)
    | S n1 ->
      internal_paths_rew_r (add (sub n0 n1) (S n1)) (add (S (sub n0 n1)) n1)
        (maponpaths (fun x -> S x) (add (sub n0 n1) n1) n0
          (minusplusnmm n0 n1 is)) (natplusnsm (sub n0 n1) n1))

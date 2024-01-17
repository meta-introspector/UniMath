open PartA
open PartB
open PartC
open Preamble
open Propositions
open Sets

(** val natnegpaths : nat -> nat -> hProp **)

let natnegpaths _ _ =
  make_hProp isapropneg

(** val natneq_hProp : nat -> nat -> hProp **)

let rec natneq_hProp n m =
  match n with
  | O -> (match m with
          | O -> hfalse
          | S _ -> htrue)
  | S n0 -> (match m with
             | O -> htrue
             | S m0 -> natneq_hProp n0 m0)

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

(** val nat_neq_to_nopath : nat -> nat -> hProptoType -> nat paths neg **)

let nat_neq_to_nopath n m =
  (natneq_iff_neq n m).pr2

(** val nat_nopath_to_neq : nat -> nat -> nat paths neg -> hProptoType **)

let nat_nopath_to_neq n m =
  (natneq_iff_neq n m).pr1

(** val natneq0sx : nat -> hProptoType **)

let natneq0sx x =
  nat_nopath_to_neq O (S x) (negpaths0sx x)

(** val natneqsx0 : nat -> hProptoType **)

let natneqsx0 x =
  nat_nopath_to_neq (S x) O (negpathssx0 x)

(** val natneqinjS : nat -> nat -> hProptoType -> hProptoType **)

let natneqinjS x x' r =
  nat_nopath_to_neq (S x) (S x') (noeqinjS x x' (nat_neq_to_nopath x x' r))

(** val isirrefl_natneq : nat -> hProptoType neg **)

let isirrefl_natneq i ne =
  nat_neq_to_nopath i i ne Coq_paths_refl

(** val issymm_natneq : nat -> nat -> hProptoType -> hProptoType **)

let issymm_natneq i j ne =
  nat_nopath_to_neq j i (fun _ -> isirrefl_natneq j ne)

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

(** val isisolatedn : nat -> nat isisolated **)

let isisolatedn =
  isdeceqnat

(** val isasetnat : nat isaset **)

let isasetnat =
  isasetifdeceq isdeceqnat

(** val natset : hSet **)

let natset =false
  (* make_hSet isasetnat *)

(** val nat_eq_or_neq : nat -> nat -> (nat paths, hProptoType) coprod **)

let rec nat_eq_or_neq m = function
| O ->
  (match m with
   | O -> Coq_ii1 Coq_paths_refl
   | S _ -> Coq_ii2 (Obj.magic Coq_tt))
| S n0 ->
  (match m with
   | O -> Coq_ii2 (Obj.magic Coq_tt)
   | S n1 ->
     let c = nat_eq_or_neq n1 n0 in
     (match c with
      | Coq_ii1 a -> Coq_ii1 (maponpaths (fun x -> S x) n1 n0 a)
      | Coq_ii2 b -> Coq_ii2 b))

(** val isdecrel_natneq : nat isdecrel **)

let rec isdecrel_natneq n m =
  match n with
  | O ->
    (match m with
     | O -> Coq_ii2 (Obj.magic idfun)
     | S _ -> Coq_ii1 (Obj.magic Coq_tt))
  | S n0 ->
    (match m with
     | O -> Coq_ii1 (Obj.magic Coq_tt)
     | S n1 -> isdecrel_natneq n0 n1)

(** val nateq : nat -> nat -> hProp **)

let nateq x y =
  make_hProp (isasetnat x y)

(** val isdecrelnateq : nat isdecrel **)

let isdecrelnateq a b =
  Obj.magic isdeceqnat a b

(** val natdeceq : nat decrel **)

let natdeceq =false
  (* make_decrel nateq isdecrelnateq *)

(** val natdecneq : nat decrel **)

let natdecneq =
  make_decrel natneq_hProp isdecrel_natneq

(** val natboolneq : nat brel **)

let natboolneq =
  decreltobrel natdecneq

(** val isinclS : (nat, nat) isincl **)

let isinclS =
  isinclbetweensets (fun x -> S x) isasetnat isasetnat invmaponpathsS

(** val isdecinclS : (nat, nat) isdecincl **)

let isdecinclS n =
  isdecpropif (isinclS n)
    (match n with
     | O ->
       let nh = fun hf -> let m = hf.pr1 in let e = hf.pr2 in negpathssx0 m e
       in
       Coq_ii2 nh
     | S n0 -> Coq_ii1 (make_hfiber (fun x -> S x) (S n0) n0 Coq_paths_refl))

(** val natgtb : nat -> nat -> bool **)

let rec natgtb n m =
  match n with
  | O -> Coq_false
  | S n0 -> (match m with
             | O -> Coq_true
             | S m0 -> natgtb n0 m0)

(** val natgth : nat -> nat -> hProp **)

let natgth n m =
  make_hProp (isasetbool (natgtb n m) Coq_true)

(** val negnatgth0n : nat -> hProptoType neg **)

let negnatgth0n _ np =
  nopathsfalsetotrue (Obj.magic np)

(** val natgthsnn : nat -> hProptoType **)

let rec natgthsnn = function
| O -> Obj.magic Coq_paths_refl
| S n0 -> natgthsnn n0

(** val natgthsn0 : nat -> hProptoType **)

let natgthsn0 _ =
  Obj.magic Coq_paths_refl

(** val negnatgth0tois0 : nat -> hProptoType neg -> nat paths **)

let negnatgth0tois0 n _ =
  match n with
  | O -> Coq_paths_refl
  | S _ -> assert false (* absurd case *)

(** val natneq0togth0 : nat -> hProptoType -> hProptoType **)

let natneq0togth0 n _ =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 -> natgthsn0 n0

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

(** val isirreflnatgth : nat -> hProptoType neg **)

let rec isirreflnatgth = function
| O -> negnatgth0n O
| S n0 -> isirreflnatgth n0

(** val natgthtoneq : nat -> nat -> hProptoType -> hProptoType **)

let natgthtoneq n m g =
  nat_nopath_to_neq n m (fun e ->
    let g0 = internal_paths_rew n g m e in isirreflnatgth m g0)

(** val isasymmnatgth : nat -> nat -> hProptoType -> hProptoType -> empty **)

let isasymmnatgth n m is is' =
  isirreflnatgth n (istransnatgth n m n is is')

(** val isantisymmnegnatgth :
    nat -> nat -> hProptoType neg -> hProptoType neg -> nat paths **)

let rec isantisymmnegnatgth n m ng0m ngm0 =
  match n with
  | O -> pathsinv0 m O (negnatgth0tois0 m ngm0)
  | S n0 ->
    (match m with
     | O -> assert false (* absurd case *)
     | S n1 ->
       maponpaths (fun x -> S x) n0 n1 (isantisymmnegnatgth n0 n1 ng0m ngm0))

(** val isdecrelnatgth : nat isdecrel **)

let isdecrelnatgth n m =
  Obj.magic isdeceqbool (natgtb n m) Coq_true

(** val natgthdec : nat decrel **)

let natgthdec =
  make_decrel natgth isdecrelnatgth

(** val isnegrelnatgth : nat isnegrel **)

let isnegrelnatgth =
  isdecreltoisnegrel natgth isdecrelnatgth

(** val iscoantisymmnatgth :
    nat -> nat -> hProptoType neg -> (hProptoType, nat paths) coprod **)

let iscoantisymmnatgth n m =
  isantisymmnegtoiscoantisymm natgth isdecrelnatgth isantisymmnegnatgth n m

(** val iscotransnatgth :
    nat -> nat -> nat -> hProptoType -> (hProptoType, hProptoType) coprod **)

let iscotransnatgth n m k gnk =
  let c = isdecrelnatgth n m in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 _ ->
     Coq_ii2
       (let c0 = isdecrelnatgth m n in
        match c0 with
        | Coq_ii1 a -> istransnatgth m n k a gnk
        | Coq_ii2 _ -> gnk))

(** val natlth : nat -> nat -> hProp **)

let natlth n m =
  natgth m n

(** val negnatlthn0 : nat -> hProptoType neg **)

let negnatlthn0 =
  negnatgth0n

(** val natlthnsn : nat -> hProptoType **)

let natlthnsn =
  natgthsnn

(** val negnat0lthtois0 : nat -> hProptoType neg -> nat paths **)

let negnat0lthtois0 =
  negnatgth0tois0

(** val natneq0to0lth : nat -> hProptoType -> hProptoType **)

let natneq0to0lth =
  natneq0togth0

(** val natlth1tois0 : nat -> hProptoType -> nat paths **)

let natlth1tois0 =
  nat1gthtois0

(** val istransnatlth :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let istransnatlth n m k lnm lmk =
  istransnatgth k m n lmk lnm

(** val isirreflnatlth : nat -> hProptoType neg **)

let isirreflnatlth =
  isirreflnatgth

(** val natlthtoneq : nat -> nat -> hProptoType -> hProptoType **)

let natlthtoneq n m g =
  nat_nopath_to_neq n m (fun e ->
    let g0 = internal_paths_rew n g m e in isirreflnatlth m g0)

(** val isasymmnatlth : nat -> nat -> hProptoType -> hProptoType -> empty **)

let isasymmnatlth n m lnm lmn =
  isasymmnatgth n m lmn lnm

(** val isantisymmnegnattth :
    nat -> nat -> hProptoType neg -> hProptoType neg -> nat paths **)

let isantisymmnegnattth n m nlnm nlmn =
  isantisymmnegnatgth n m nlmn nlnm

(** val isdecrelnatlth : nat isdecrel **)

let isdecrelnatlth n m =
  isdecrelnatgth m n

(** val natlthdec : nat decrel **)

let natlthdec =
  make_decrel natlth isdecrelnatlth

(** val isnegrelnatlth : nat isnegrel **)

let isnegrelnatlth n m =
  isnegrelnatgth m n

(** val iscoantisymmnatlth :
    nat -> nat -> hProptoType neg -> (hProptoType, nat paths) coprod **)

let iscoantisymmnatlth n m nlnm =
  let c = iscoantisymmnatgth m n nlnm in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 (pathsinv0 m n b))

(** val iscotransnatlth :
    nat -> nat -> nat -> hProptoType -> (hProptoType, hProptoType) coprod **)

let iscotransnatlth n m k lnk =
  coprodcomm (iscotransnatgth k m n lnk)

(** val natleh : nat -> nat -> hProp **)

let natleh n m =
  natgth (S m) n

(** val isdecrelnatleh : nat isdecrel **)

let isdecrelnatleh m n =
  isdecrelnatgth (S n) m

(** val negnatlehsn0 : nat -> hProptoType neg **)

let negnatlehsn0 =
  negnatlthn0

(** val natlehneggth : nat -> nat -> hProptoType -> hProptoType neg **)

let rec natlehneggth n m =
  match n with
  | O -> (fun _ -> negnatgth0n m)
  | S n0 ->
    (match m with
     | O -> (fun r _ -> negnatlehsn0 n0 r)
     | S n1 -> natlehneggth n0 n1)

(** val natgthnegleh : nat -> nat -> hProptoType -> hProptoType neg **)

let natgthnegleh n m r s =
  natlehneggth n m s r

(** val negnatSleh : nat -> hProptoType neg **)

let negnatSleh n =
  isirreflnatgth (S n)

(** val negnatgthtoleh : nat -> nat -> hProptoType neg -> hProptoType **)

let rec negnatgthtoleh n m r =
  match n with
  | O -> natgthsn0 m
  | S n0 ->
    (match m with
     | O -> assert false (* absurd case *)
     | S n1 -> negnatgthtoleh n0 n1 r)

(** val negnatlehtogth : nat -> nat -> hProptoType neg -> hProptoType **)

let negnatlehtogth n m r =
  isdecreltoisnegrel natgth isdecrelnatgth n m (fun s ->
    r (negnatgthtoleh n m s))

(** val neggth_logeq_leh :
    nat -> nat -> (hProptoType neg, hProptoType) logeq **)

let neggth_logeq_leh n m =
  { pr1 = (negnatgthtoleh n m); pr2 = (natlehneggth n m) }

(** val natleh0tois0 : nat -> hProptoType -> nat paths **)

let natleh0tois0 =
  natlth1tois0

(** val natleh0n : nat -> hProptoType **)

let natleh0n =
  natgthsn0

(** val negnatlehsnn : nat -> hProptoType neg **)

let negnatlehsnn n =
  isirreflnatlth (S n)

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

(** val natlehdec : nat decrel **)

let natlehdec =
  make_decrel natleh isdecrelnatleh

(** val isnegrelnatleh : nat isnegrel **)

let isnegrelnatleh =
  isdecreltoisnegrel natleh isdecrelnatleh

(** val natlthtoleh : nat -> nat -> hProptoType -> hProptoType **)

let rec natlthtoleh m n r =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 -> (match m with
             | O -> natgthsn0 (S n0)
             | S n1 -> natlthtoleh n1 n0 r)

(** val iscoasymmnatleh : nat -> nat -> hProptoType neg -> hProptoType **)

let iscoasymmnatleh n m r =
  negnatgthtoleh m n (fun s -> r (natlthtoleh n m s))

(** val istotalnatleh : nat istotal **)

let istotalnatleh x y =
  let c = isdecrelnatleh x y in
  (match c with
   | Coq_ii1 a -> hinhpr (Coq_ii1 a)
   | Coq_ii2 b -> hinhpr (Coq_ii2 (iscoasymmnatleh x y b)))

(** val natgeh : nat -> nat -> hProp **)

let natgeh n m =
  natleh m n

(** val nat0gehtois0 : nat -> hProptoType -> nat paths **)

let nat0gehtois0 =
  natleh0tois0

(** val natgehn0 : nat -> hProptoType **)

let natgehn0 =
  natleh0n

(** val negnatgeh0sn : nat -> hProptoType neg **)

let negnatgeh0sn =
  negnatlehsn0

(** val negnatgehnsn : nat -> hProptoType neg **)

let negnatgehnsn =
  negnatlehsnn

(** val istransnatgeh :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let istransnatgeh n m k gnm gmk =
  istransnatleh k m n gmk gnm

(** val isreflnatgeh : nat -> hProptoType **)

let isreflnatgeh =
  isreflnatleh

(** val isantisymmnatgeh :
    nat -> nat -> hProptoType -> hProptoType -> nat paths **)

let isantisymmnatgeh n m gnm gmn =
  isantisymmnatleh n m gmn gnm

(** val isdecrelnatgeh : nat isdecrel **)

let isdecrelnatgeh n m =
  isdecrelnatleh m n

(** val natgehdec : nat decrel **)

let natgehdec =
  make_decrel natgeh isdecrelnatgeh

(** val isnegrelnatgeh : nat isnegrel **)

let isnegrelnatgeh n m =
  isnegrelnatleh m n

(** val iscoasymmnatgeh : nat -> nat -> hProptoType neg -> hProptoType **)

let iscoasymmnatgeh n m nl =
  iscoasymmnatleh m n nl

(** val istotalnatgeh : nat istotal **)

let istotalnatgeh n m =
  istotalnatleh m n

(** val natgthtogeh : nat -> nat -> hProptoType -> hProptoType **)

let natgthtogeh n m =
  natlthtoleh m n

(** val natlehtonegnatgth : nat -> nat -> hProptoType -> hProptoType neg **)

let natlehtonegnatgth =
  natlehneggth

(** val natgthtonegnatleh : nat -> nat -> hProptoType -> hProptoType neg **)

let natgthtonegnatleh n m g l =
  natlehtonegnatgth n m l g

(** val natgehtonegnatlth : nat -> nat -> hProptoType -> hProptoType neg **)

let natgehtonegnatlth n m gnm lnm =
  natlehtonegnatgth m n gnm lnm

(** val natlthtonegnatgeh : nat -> nat -> hProptoType -> hProptoType neg **)

let natlthtonegnatgeh n m gnm lnm =
  natlehtonegnatgth m n lnm gnm

(** val negnatgehtolth : nat -> nat -> hProptoType neg -> hProptoType **)

let negnatgehtolth n m r =
  negnatlehtogth m n r

(** val negnatlthtogeh : nat -> nat -> hProptoType neg -> hProptoType **)

let negnatlthtogeh n m nl =
  negnatgthtoleh m n nl

(** val natlehnsn : nat -> hProptoType **)

let natlehnsn n =
  natlthtoleh n (S n) (natgthsnn n)

(** val natgehsnn : nat -> hProptoType **)

let natgehsnn =
  natlehnsn

(** val natgthorleh : nat -> nat -> (hProptoType, hProptoType) coprod **)

let natgthorleh n m =
  let c = isdecrelnatgth n m in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 (negnatgthtoleh n m b))

(** val natlthorgeh : nat -> nat -> (hProptoType, hProptoType) coprod **)

let natlthorgeh n m =
  natgthorleh m n

(** val natchoice0 : nat -> (nat paths, hProptoType) coprod **)

let natchoice0 = function
| O -> Coq_ii1 Coq_paths_refl
| S n0 -> Coq_ii2 (natgthsn0 n0)

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

(** val natlehchoice :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natlehchoice n m l =
  let c = natlthorgeh n m in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 (isantisymmnatleh n m l b))

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

(** val natgehgthtrans :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natgehgthtrans n m k gnm gmk =
  let c = natgehchoice n m gnm in
  (match c with
   | Coq_ii1 a -> istransnatgth n m k a gmk
   | Coq_ii2 b -> internal_paths_rew_r n m gmk b)

(** val natlthlehtrans :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natlthlehtrans n m k l1 l2 =
  natgehgthtrans k m n l2 l1

(** val natlehlthtrans :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natlehlthtrans n m k l1 l2 =
  natgthgehtrans k m n l2 l1

(** val natltltSlt :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natltltSlt =
  natlthlehtrans

(** val natgthtogehsn : nat -> nat -> hProptoType -> hProptoType **)

let rec natgthtogehsn n m x =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 -> (match m with
             | O -> natgehn0 n0
             | S n1 -> natgthtogehsn n0 n1 x)

(** val natgthsntogeh : nat -> nat -> hProptoType -> hProptoType **)

let natgthsntogeh n m a =
  natgthtogehsn (S n) m a

(** val natgehtogthsn : nat -> nat -> hProptoType -> hProptoType **)

let natgehtogthsn n m x =
  natgthgehtrans (S n) n m (natgthsnn n) x

(** val natgehsntogth : nat -> nat -> hProptoType -> hProptoType **)

let natgehsntogth n m x =
  natgehgthtrans n (S m) m x (natgthsnn m)

(** val natlthtolehsn : nat -> nat -> hProptoType -> hProptoType **)

let natlthtolehsn n m x =
  natgthtogehsn m n x

(** val natlehsntolth : nat -> nat -> hProptoType -> hProptoType **)

let natlehsntolth n m x =
  natgehsntogth m n x

(** val natlehtolthsn : nat -> nat -> hProptoType -> hProptoType **)

let natlehtolthsn n m x =
  natgehtogthsn m n x

(** val natlthsntoleh : nat -> nat -> hProptoType -> hProptoType **)

let natlthsntoleh n m a =
  natlthtolehsn n (S m) a

(** val natlehchoice2 :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natlehchoice2 n m l =
  let c = natlehchoice n m l in
  (match c with
   | Coq_ii1 a -> Coq_ii1 (natlthtolehsn n m a)
   | Coq_ii2 b -> Coq_ii2 b)

(** val natgehchoice2 :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natgehchoice2 n m g =
  let c = natgehchoice n m g in
  (match c with
   | Coq_ii1 a -> Coq_ii1 (natgthtogehsn n m a)
   | Coq_ii2 b -> Coq_ii2 b)

(** val natgthchoice2 :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natgthchoice2 n m g =
  let c = natgehchoice n (S m) (natgthtogehsn n m g) in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 b)

(** val natlthchoice2 :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natlthchoice2 n m l =
  let c = natlehchoice (S n) m (natlthtolehsn n m l) in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 b)

(** val natplusl0 : nat -> nat paths **)

let natplusl0 _ =
  Coq_paths_refl

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

(** val natgthtogths : nat -> nat -> hProptoType -> hProptoType **)

let natgthtogths n m is =
  istransnatgth (S n) n m (natgthsnn n) is

(** val negnatgthmplusnm : nat -> nat -> hProptoType neg **)

let rec negnatgthmplusnm n m =
  match n with
  | O -> isirreflnatgth (add O m)
  | S n0 ->
    natlehtonegnatgth m (add (S n0) m)
      (let r = negnatgthtoleh m (add n0 m) (negnatgthmplusnm n0 m) in
       istransnatleh m (add n0 m) (S (add n0 m)) r
         (natlthtoleh (add n0 m) (S (add n0 m)) (natlthnsn (add n0 m))))

(** val negnatgthnplusnm : nat -> nat -> hProptoType neg **)

let negnatgthnplusnm n m =
  internal_paths_rew_r (add n m) (add m n) (negnatgthmplusnm m n)
    (natpluscomm n m)

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

(** val natgthandplusm : nat -> nat -> hProptoType -> hProptoType **)

let natgthandplusm n m h =
  match n with
  | O -> internal_paths_rew_r (add O m) m h (natplusl0 m)
  | S n0 ->
    internal_paths_rew (add n0 (S m))
      (internal_paths_rew_r (add (S O) n0) (add n0 (S O))
        (natgthandplusl (S m) (S O) n0 h) (natpluscomm (S O) n0))
      (add (S n0) m) (natplusnsm n0 m)

(** val natlthtolths : nat -> nat -> hProptoType -> hProptoType **)

let natlthtolths n m =
  natgthtogths m n

(** val negnatlthplusnmm : nat -> nat -> hProptoType neg **)

let negnatlthplusnmm =
  negnatgthmplusnm

(** val negnatlthplusnmn : nat -> nat -> hProptoType neg **)

let negnatlthplusnmn =
  negnatgthnplusnm

(** val natlthandplusl : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlthandplusl n m k =
  natgthandplusl m n k

(** val natlthandplusr : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlthandplusr n m k =
  natgthandplusr m n k

(** val natlthandpluslinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlthandpluslinv n m k =
  natgthandpluslinv m n k

(** val natlthandplusrinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlthandplusrinv n m k =
  natgthandplusrinv m n k

(** val natlthandplusm : nat -> nat -> hProptoType -> hProptoType **)

let natlthandplusm =
  natgthandplusm

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

(** val natlehnplusnm : nat -> nat -> hProptoType **)

let rec natlehnplusnm n = function
| O -> isreflnatleh n
| S n0 -> natlehtolehs n (add n n0) (natlehnplusnm n n0)

(** val natlehandplusl : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlehandplusl n m k r =
  internal_paths_rew_r (S (add k m)) (add k (S m))
    (natgthandplusl (S m) n k r) (plus_n_Sm k m)

(** val natlehandplusr : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlehandplusr n m k r =
  natgthandplusr (S m) n k r

(** val natlehandplus :
    nat -> nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natlehandplus i j k l r s =
  istransnatleh (add i k) (add j k) (add j l) (natlehandplusr i j k r)
    (natlehandplusl k l j s)

(** val natlehandpluslinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlehandpluslinv n m k r =
  let r0 = internal_paths_rew (S (add k m)) r (add k (S m)) (plus_n_Sm k m) in
  natgthandpluslinv (S m) n k r0

(** val natlehandplusrinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlehandplusrinv n m k r =
  natgthandplusrinv (S m) n k r

(** val natgehtogehs : nat -> nat -> hProptoType -> hProptoType **)

let natgehtogehs n m =
  natlehtolehs m n

(** val natgehplusnmm : nat -> nat -> hProptoType **)

let natgehplusnmm =
  natlehmplusnm

(** val natgehplusnmn : nat -> nat -> hProptoType **)

let natgehplusnmn =
  natlehnplusnm

(** val natgehandplusl : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natgehandplusl n m k =
  natlehandplusl m n k

(** val natgehandplusr : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natgehandplusr n m k =
  natlehandplusr m n k

(** val natgehandpluslinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natgehandpluslinv n m k =
  natlehandpluslinv m n k

(** val natgehandplusrinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natgehandplusrinv n m k =
  natlehandplusrinv m n k

(** val natgthtogthp1 : nat -> nat -> hProptoType -> hProptoType **)

let natgthtogthp1 =
  natgthtogths

(** val natlthtolthp1 : nat -> nat -> hProptoType -> hProptoType **)

let natlthtolthp1 n m =
  natgthtogthp1 m n

(** val natlehtolehp1 : nat -> nat -> hProptoType -> hProptoType **)

let natlehtolehp1 =
  natlehtolehs

(** val natgehtogehp1 : nat -> nat -> hProptoType -> hProptoType **)

let natgehtogehp1 n m =
  natlehtolehp1 m n

(** val natgthtogehp1 : nat -> nat -> hProptoType -> hProptoType **)

let natgthtogehp1 =
  natgthtogehsn

(** val natgthp1togeh : nat -> nat -> hProptoType -> hProptoType **)

let natgthp1togeh =
  natgthsntogeh

(** val natlehp1tolth : nat -> nat -> hProptoType -> hProptoType **)

let natlehp1tolth =
  natlehsntolth

(** val natlthtolehp1 : nat -> nat -> hProptoType -> hProptoType **)

let natlthtolehp1 =
  natlthtolehsn

(** val natlthp1toleh : nat -> nat -> hProptoType -> hProptoType **)

let natlthp1toleh =
  natlthsntoleh

(** val natgehp1togth : nat -> nat -> hProptoType -> hProptoType **)

let natgehp1togth =
  natgehsntogth

(** val natlehchoice3 :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natlehchoice3 n m l =
  let c = natlehchoice n m l in
  (match c with
   | Coq_ii1 a -> Coq_ii1 (natlthtolehp1 n m a)
   | Coq_ii2 b -> Coq_ii2 b)

(** val natgehchoice3 :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natgehchoice3 n m g =
  let c = natgehchoice n m g in
  (match c with
   | Coq_ii1 a -> Coq_ii1 (natgthtogehp1 n m a)
   | Coq_ii2 b -> Coq_ii2 b)

(** val natgthchoice3 :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natgthchoice3 n m g =
  let c = natgehchoice n (add m (S O)) (natgthtogehp1 n m g) in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 b)

(** val natlthchoice3 :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natlthchoice3 n m l =
  let c = natlehchoice (add n (S O)) m (natlthtolehp1 n m l) in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b -> Coq_ii2 b)

(** val natlehchoice4 :
    nat -> nat -> hProptoType -> (hProptoType, nat paths) coprod **)

let natlehchoice4 n m b =
  let c = natlthorgeh n m in
  (match c with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b0 -> Coq_ii2 (isantisymmnatleh n m (natlthsntoleh n m b) b0))

(** val pathsitertoplus : nat -> nat -> nat paths **)

let rec pathsitertoplus n m =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    maponpaths (fun x -> S x) (iteration (fun x -> S x) n0 m) (add n0 m)
      (pathsitertoplus n0 m)

(** val isinclnatplusr : nat -> (nat, nat) isincl **)

let rec isinclnatplusr = function
| O ->
  isofhlevelfhomot (S O) (fun m -> m) (fun m -> add m O) (fun m ->
    pathsinv0 (add m O) m (natplusr0 m)) (isofhlevelfweq (S O) idweq)
| S n0 ->
  isofhlevelfhomot (S O) (fun m -> add (S m) n0) (fun m -> add m (S n0))
    (fun m -> pathsinv0 (add m (S n0)) (add (S m) n0) (natplusnsm m n0))
    (isofhlevelfgf (S O) (fun x -> S x) (fun m -> add m n0) isinclS
      (isinclnatplusr n0))

(** val isinclnatplusl : nat -> (nat, nat) isincl **)

let isinclnatplusl n =
  isofhlevelfhomot (S O) (fun m -> add m n) (add n) (fun m ->
    natpluscomm m n) (isinclnatplusr n)

(** val natplusrcan : nat -> nat -> nat -> nat paths -> nat paths **)

let natplusrcan a b c is =
  invmaponpathsincl (fun m -> add m c) (isinclnatplusr c) a b is

(** val natpluslcan : nat -> nat -> nat -> nat paths -> nat paths **)

let natpluslcan a b c is =
  let is0 = internal_paths_rew (add c a) is (add a c) (natpluscomm c a) in
  let is1 = internal_paths_rew (add c b) is0 (add b c) (natpluscomm c b) in
  natplusrcan a b c is1

(** val iscontrhfibernatplusr :
    nat -> nat -> hProptoType -> (nat, nat) hfiber iscontr **)

let iscontrhfibernatplusr n m is =
  iscontraprop1 (isinclnatplusr n m)
    (let rec f n0 is0 =
       match n0 with
       | O -> let e = natleh0tois0 n is0 in { pr1 = O; pr2 = e }
       | S n1 ->
         let c = natlehchoice2 n (S n1) is0 in
         (match c with
          | Coq_ii1 a ->
            let j = f n1 a in
            let j0 = j.pr1 in
            let e' = j.pr2 in
            { pr1 = (S j0); pr2 =
            (maponpaths (fun x -> S x) (add j0 n) n1 e') }
          | Coq_ii2 b -> { pr1 = O; pr2 = b })
     in f m is)

(** val iscontrhfibernatplusl :
    nat -> nat -> hProptoType -> (nat, nat) hfiber iscontr **)

let iscontrhfibernatplusl n m is =
  iscontraprop1 (isinclnatplusl n m)
    (let rec f n0 is0 =
       match n0 with
       | O ->
         let e = natleh0tois0 n is0 in
         { pr1 = O; pr2 = (internal_paths_rew_r (add n O) n e (natplusr0 n)) }
       | S n1 ->
         let c = natlehchoice2 n (S n1) is0 in
         (match c with
          | Coq_ii1 a ->
            let j = f n1 a in
            let j0 = j.pr1 in
            let e' = j.pr2 in
            { pr1 = (S j0); pr2 =
            (internal_paths_rew (S (add n j0))
              (maponpaths (fun x -> S x) (add n j0) n1 e') (add n (S j0))
              (plus_n_Sm n j0)) }
          | Coq_ii2 b ->
            { pr1 = O; pr2 =
              (internal_paths_rew_r (add n O) n b (natplusr0 n)) })
     in f m is)

(** val neghfibernatplusr :
    nat -> nat -> hProptoType -> (nat, nat) hfiber neg **)

let neghfibernatplusr _ _ _ _ =
  assert false (* absurd case *)

(** val isdecinclnatplusr : nat -> (nat, nat) isdecincl **)

let isdecinclnatplusr n m =
  isdecpropif (isinclnatplusr n m)
    (let c = natlthorgeh m n in
     match c with
     | Coq_ii1 a -> Coq_ii2 (neghfibernatplusr n m a)
     | Coq_ii2 b -> Coq_ii1 (iscontrhfibernatplusr n m b).pr1)

(** val minuseq0 : nat -> nat -> hProptoType -> nat paths **)

let rec minuseq0 n m is =
  match m with
  | O -> internal_paths_rew_r n O Coq_paths_refl (natleh0tois0 n is)
  | S n0 -> (match n with
             | O -> Coq_paths_refl
             | S n1 -> minuseq0 n1 n0 is)

(** val minuseq0' : nat -> nat paths **)

let rec minuseq0' = function
| O -> Coq_paths_refl
| S n0 -> minuseq0' n0

(** val minusgth0 : nat -> nat -> hProptoType -> hProptoType **)

let rec minusgth0 n m is =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 -> (match m with
             | O -> natgthsn0 n0
             | S n1 -> minusgth0 n0 n1 is)

(** val minusgth0inv : nat -> nat -> hProptoType -> hProptoType **)

let rec minusgth0inv n m is =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 -> (match m with
             | O -> natgthsn0 n0
             | S n1 -> minusgth0inv n0 n1 is)

(** val natminuseqn : nat -> nat paths **)

let natminuseqn _ =
  Coq_paths_refl

(** val natminuslehn : nat -> nat -> hProptoType **)

let rec natminuslehn n m =
  match n with
  | O -> isreflnatleh O
  | S n0 ->
    (match m with
     | O -> isreflnatleh (S n0)
     | S n1 ->
       istransnatleh (sub n0 n1) n0 (S n0) (natminuslehn n0 n1) (natlehnsn n0))

(** val natminusgehn : nat -> nat -> hProptoType **)

let natminusgehn =
  natminuslehn

(** val natminuslthn :
    nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natminuslthn n m _ _ =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 ->
    (match m with
     | O -> assert false (* absurd case *)
     | S n1 ->
       natlehlthtrans (sub (S n0) (S n1)) n0 (S n0) (natminuslehn n0 n1)
         (natlthnsn n0))

(** val natminuslthninv : nat -> nat -> hProptoType -> hProptoType **)

let natminuslthninv n m _ =
  match n with
  | O -> assert false (* absurd case *)
  | S _ ->
    (match m with
     | O -> assert false (* absurd case *)
     | S n0 -> natgthsn0 n0)

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

(** val minusplusnmmineq : nat -> nat -> hProptoType **)

let minusplusnmmineq n m =
  let c = natlthorgeh n m in
  (match c with
   | Coq_ii1 a ->
     internal_paths_rew_r (sub n m) O (natgthtogeh m n a)
       (minuseq0 n m (natlthtoleh n m a))
   | Coq_ii2 b ->
     internal_paths_rew_r (add (sub n m) m) n (isreflnatgeh n)
       (minusplusnmm n m b))

(** val plusminusnmm : nat -> nat -> nat paths **)

let plusminusnmm n m =
  let int1 = natgehplusnmm n m in
  natplusrcan (sub (add n m) m) n m
    (internal_paths_rew_r (add (sub (add n m) m) m) (add n m) Coq_paths_refl
      (minusplusnmm (add n m) m int1))

(** val minusminusmmn : nat -> nat -> hProptoType -> nat paths **)

let minusminusmmn n m h =
  natplusrcan (sub m (sub m n)) n (sub m n)
    (internal_paths_rew_r (add (sub m (sub m n)) (sub m n)) m
      (internal_paths_rew_r (add n (sub m n)) (add (sub m n) n)
        (internal_paths_rew_r (add (sub m n) n) m Coq_paths_refl
          (minusplusnmm m n h)) (natpluscomm n (sub m n)))
      (minusplusnmm m (sub m n) (natminusgehn m n)))

(** val natgthtogthm1 : nat -> nat -> hProptoType -> hProptoType **)

let natgthtogthm1 n m is =
  match m with
  | O -> is
  | S n0 ->
    internal_paths_rew_r (sub n0 O) n0
      (natgehgthtrans n (S n0) n0 (natgthtogeh n (S n0) is) (natgthsnn n0))
      (natminuseqn n0)

(** val natlthtolthm1 : nat -> nat -> hProptoType -> hProptoType **)

let natlthtolthm1 n m =
  natgthtogthm1 m n

(** val natlehtolehm1 : nat -> nat -> hProptoType -> hProptoType **)

let natlehtolehm1 n m x =
  natlthtolthm1 n (S m) x

(** val natgehtogehm1 : nat -> nat -> hProptoType -> hProptoType **)

let natgehtogehm1 n m =
  natlehtolehm1 m n

(** val natgthtogehm1 : nat -> nat -> hProptoType -> hProptoType **)

let natgthtogehm1 n m x =
  match n with
  | O -> fromempty (negnatgth0n m x)
  | S n0 ->
    (match m with
     | O -> Obj.magic Coq_paths_refl
     | S _ -> internal_paths_rew_r (sub n0 O) n0 x (natminuseqn n0))

(** val natgehandminusr : nat -> nat -> nat -> hProptoType -> hProptoType **)

let rec natgehandminusr n m k is =
  match n with
  | O -> internal_paths_rew_r m O (isreflnatleh (sub O k)) (nat0gehtois0 m is)
  | S n0 ->
    (match m with
     | O -> natgehn0 (sub (S n0) k)
     | S n1 -> (match k with
                | O -> is
                | S n2 -> natgehandminusr n0 n1 n2 is))

(** val natgehandminusl : nat -> nat -> nat -> hProptoType -> hProptoType **)

let rec natgehandminusl n m k is =
  match n with
  | O -> internal_paths_rew_r m O (isreflnatleh (sub O k)) (nat0gehtois0 m is)
  | S n0 ->
    (match m with
     | O -> natgehn0 (sub (S n0) k)
     | S n1 -> (match k with
                | O -> is
                | S n2 -> natgehandminusl n0 n1 n2 is))

(** val natgehandminusrinv :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let rec natgehandminusrinv n m k is' is =
  match n with
  | O ->
    let is0 = internal_paths_rew k is O (nat0gehtois0 k is') in
    let is1 = internal_paths_rew (sub m O) is0 m (natminuseqn m) in
    internal_paths_rew_r m O (isreflnatleh O) (nat0gehtois0 m is1)
  | S n0 ->
    (match m with
     | O -> natgehn0 (S n0)
     | S n1 ->
       (match k with
        | O ->
          let is0 =
            internal_paths_rew (sub (S n0) O) is (S n0) (natminuseqn (S n0))
          in
          internal_paths_rew (sub (S n1) O) is0 (S n1) (natminuseqn (S n1))
        | S n2 -> natgehandminusrinv n0 n1 n2 is' is))

(** val natlthandminusl :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natlthandminusl n m i is is' =
  match i with
  | O ->
    internal_paths_rew_r (sub n O) n
      (internal_paths_rew_r (sub m O) m is (natminuseqn m)) (natminuseqn n)
  | S n0 ->
    let c = natlthorgeh n (S n0) in
    (match c with
     | Coq_ii1 a ->
       let e = minuseq0 n (S n0) (natlthtoleh n (S n0) a) in
       internal_paths_rew_r (sub n (S n0)) O
         (natlthandplusrinv O (sub m (S n0)) (S n0)
           (internal_paths_rew_r (add O (S n0)) (S n0)
             (internal_paths_rew_r (add (sub m (S n0)) (S n0)) m is'
               (minusplusnmm m (S n0) (natlthtoleh (S n0) m is')))
             (natplusl0 (S n0)))) e
     | Coq_ii2 b ->
       natlthandplusrinv (sub n (S n0)) (sub m (S n0)) (S n0)
         (internal_paths_rew_r (add (sub m (S n0)) (S n0)) m
           (internal_paths_rew_r (add (sub n (S n0)) (S n0)) n is
             (minusplusnmm n (S n0) b))
           (minusplusnmm m (S n0) (natlthtoleh (S n0) m is'))))

(** val natmult0n : nat -> nat paths **)

let natmult0n _ =
  Coq_paths_refl

(** val natmultn0 : nat -> nat paths **)

let rec natmultn0 = function
| O -> Coq_paths_refl
| S n0 ->
  pathscomp0 (add (mul n0 O) O) (mul n0 O) O (natplusr0 (mul n0 O))
    (natmultn0 n0)

(** val multsnm : nat -> nat -> nat paths **)

let multsnm n m =
  natpluscomm (mul n m) m

(** val multnsm : nat -> nat -> nat paths **)

let rec multnsm n m =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    internal_paths_rew (add (add n0 (mul n0 m)) m)
      (internal_paths_rew_r (add (add n0 (mul n0 m)) m)
        (add m (add n0 (mul n0 m)))
        (internal_paths_rew_r (add (S m) (add n0 (mul n0 m)))
          (add (add n0 (mul n0 m)) (S m))
          (maponpaths (fun x -> add x (S m)) (mul n0 (S m))
            (add n0 (mul n0 m)) (multnsm n0 m))
          (natpluscomm (S m) (add n0 (mul n0 m))))
        (natpluscomm (add n0 (mul n0 m)) m)) (add n0 (add (mul n0 m) m))
      (natplusassoc n0 (mul n0 m) m)

(** val natmultcomm : nat -> nat -> nat paths **)

let rec natmultcomm n m =
  match n with
  | O -> pathsinv0 (mul m O) (mul O m) (natmultn0 m)
  | S n0 ->
    internal_paths_rew_r (mul (S n0) m) (add m (mul n0 m))
      (internal_paths_rew_r (mul m (S n0)) (add m (mul m n0))
        (maponpaths (fun x -> add m x) (mul n0 m) (mul m n0)
          (natmultcomm n0 m)) (multnsm m n0)) (multsnm n0 m)

(** val natrdistr : nat -> nat -> nat -> nat paths **)

let rec natrdistr n m k =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    internal_paths_rew_r (add (add (mul n0 k) k) (mul m k))
      (add (mul n0 k) (add k (mul m k)))
      (internal_paths_rew_r (add k (mul m k)) (add (mul m k) k)
        (internal_paths_rew (add (add (mul n0 k) (mul m k)) k)
          (maponpaths (fun x -> add x k) (mul (add n0 m) k)
            (add (mul n0 k) (mul m k)) (natrdistr n0 m k))
          (add (mul n0 k) (add (mul m k) k))
          (natplusassoc (mul n0 k) (mul m k) k)) (natpluscomm k (mul m k)))
      (natplusassoc (mul n0 k) k (mul m k))

(** val natldistr : nat -> nat -> nat -> nat paths **)

let rec natldistr m k n =
  match m with
  | O -> internal_paths_rew_r (mul n O) O Coq_paths_refl (natmultn0 n)
  | S n0 ->
    internal_paths_rew_r (mul n (S (add n0 k))) (add n (mul n (add n0 k)))
      (internal_paths_rew_r (mul n (S n0)) (add n (mul n n0))
        (internal_paths_rew_r (add (add n (mul n n0)) (mul n k))
          (add n (add (mul n n0) (mul n k)))
          (maponpaths (fun x -> add n x) (mul n (add n0 k))
            (add (mul n n0) (mul n k)) (natldistr n0 k n))
          (natplusassoc n (mul n n0) (mul n k))) (multnsm n n0))
      (multnsm n (add n0 k))

(** val natmultassoc : nat -> nat -> nat -> nat paths **)

let rec natmultassoc n m k =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    internal_paths_rew_r (mul (add (mul n0 m) m) k)
      (add (mul (mul n0 m) k) (mul m k))
      (maponpaths (fun x -> add x (mul m k)) (mul (mul n0 m) k)
        (mul n0 (mul m k)) (natmultassoc n0 m k)) (natrdistr (mul n0 m) m k)

(** val natmultl1 : nat -> nat paths **)

let natmultl1 _ =
  Coq_paths_refl

(** val natmultr1 : nat -> nat paths **)

let natmultr1 n =
  internal_paths_rew_r (mul n (S O)) (mul (S O) n) Coq_paths_refl
    (natmultcomm n (S O))

(** val natplusnonzero : nat -> nat -> hProptoType -> hProptoType **)

let natplusnonzero n _ ne =
  match n with
  | O -> ne
  | S _ -> Obj.magic Coq_tt

(** val natneq0andmult :
    nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natneq0andmult n m isn ism =
  match n with
  | O -> fromempty (Obj.magic isn)
  | S n0 -> natplusnonzero (mul n0 m) m ism

(** val natneq0andmultlinv : nat -> nat -> hProptoType -> hProptoType **)

let natneq0andmultlinv n _ r =
  match n with
  | O -> fromempty (Obj.magic r)
  | S n0 -> natneqsx0 n0

(** val natneq0andmultrinv : nat -> nat -> hProptoType -> hProptoType **)

let natneq0andmultrinv n m r =
  match m with
  | O -> fromempty (nat_neq_to_nopath (mul n O) O r (natmultn0 n))
  | S n0 -> natneqsx0 n0

(** val natgthandmultl :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let rec natgthandmultl n m k g g' =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 ->
    (match m with
     | O ->
       internal_paths_rew_r (mul k O) O
         (internal_paths_rew_r (mul k (S n0)) (add k (mul k n0))
           (natgehgthtrans (add k (mul k n0)) k O
             (natgehplusnmn k (mul k n0)) (natneq0togth0 k g)) (multnsm k n0))
         (natmultn0 k)
     | S n1 ->
       internal_paths_rew_r (mul k (S n0)) (add k (mul k n0))
         (internal_paths_rew_r (mul k (S n1)) (add k (mul k n1))
           (natgthandplusl (mul k n0) (mul k n1) k
             (natgthandmultl n0 n1 k g g')) (multnsm k n1)) (multnsm k n0))

(** val natgthandmultr :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natgthandmultr n m k l =
  internal_paths_rew_r (mul n k) (mul k n)
    (internal_paths_rew_r (mul m k) (mul k m) (natgthandmultl n m k l)
      (natmultcomm m k)) (natmultcomm n k)

(** val natgthandmultlinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let rec natgthandmultlinv n m k g =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 ->
    (match m with
     | O -> natgthsn0 n0
     | S n1 ->
       let g0 =
         internal_paths_rew (mul k (S n0)) g (add k (mul k n0)) (multnsm k n0)
       in
       let g1 =
         internal_paths_rew (mul k (S n1)) g0 (add k (mul k n1))
           (multnsm k n1)
       in
       natgthandmultlinv n0 n1 k
         (natgthandpluslinv (mul k n0) (mul k n1) k g1))

(** val natgthandmultrinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natgthandmultrinv n m k g =
  let g0 = internal_paths_rew (mul n k) g (mul k n) (natmultcomm n k) in
  let g1 = internal_paths_rew (mul m k) g0 (mul k m) (natmultcomm m k) in
  natgthandmultlinv n m k g1

(** val natlthandmultl :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natlthandmultl n m k =
  natgthandmultl m n k

(** val natlthandmultr :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natlthandmultr n m k =
  natgthandmultr m n k

(** val natlthandmultlinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlthandmultlinv n m k =
  natgthandmultlinv m n k

(** val natlthandmultrinv :
    nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlthandmultrinv n m k =
  natgthandmultrinv m n k

(** val natlehandmultl : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlehandmultl n m k r =
  negnatgthtoleh (mul k n) (mul k m) (fun t ->
    natlehtonegnatgth n m r (natgthandmultlinv n m k t))

(** val natlehandmultr : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natlehandmultr n m k r =
  negnatgthtoleh (mul n k) (mul m k) (fun t ->
    natlehtonegnatgth n m r (natgthandmultrinv n m k t))

(** val natlehandmultlinv :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natlehandmultlinv n m k r s =
  negnatgthtoleh n m (fun t ->
    natlehtonegnatgth (mul k n) (mul k m) s (natgthandmultl n m k r t))

(** val natlehandmultrinv :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natlehandmultrinv n m k r s =
  negnatgthtoleh n m (fun t ->
    natlehtonegnatgth (mul n k) (mul m k) s (natgthandmultr n m k r t))

(** val natgehandmultl : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natgehandmultl n m k =
  natlehandmultl m n k

(** val natgehandmultr : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natgehandmultr n m k =
  natlehandmultr m n k

(** val natgehandmultlinv :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natgehandmultlinv n m k =
  natlehandmultlinv m n k

(** val natgehandmultrinv :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natgehandmultrinv n m k =
  natlehandmultrinv m n k

(** val natdivrem : nat -> nat -> (nat, nat) dirprod **)

let rec natdivrem n m =
  match n with
  | O -> make_dirprod O O
  | S n0 ->
    let iHn = natdivrem n0 m in
    let c = natlthorgeh (S iHn.pr2) m in
    (match c with
     | Coq_ii1 _ -> make_dirprod iHn.pr1 (S iHn.pr2)
     | Coq_ii2 _ -> make_dirprod (S iHn.pr1) O)

(** val natdiv : nat -> nat -> nat **)

let natdiv n m =
  (natdivrem n m).pr1

(** val natrem : nat -> nat -> nat **)

let natrem n m =
  (natdivrem n m).pr2

(** val lthnatrem : nat -> nat -> hProptoType -> hProptoType **)

let lthnatrem n m is =
  match n with
  | O -> natneq0togth0 m is
  | S n0 ->
    let c = natlthorgeh (S (natdivrem n0 m).pr2) m in
    (match c with
     | Coq_ii1 a -> a
     | Coq_ii2 _ -> natneq0togth0 m is)

(** val natdivremrule : nat -> nat -> hProptoType -> nat paths **)

let rec natdivremrule n m is =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    let c = natlthorgeh (S (natdivrem n0 m).pr2) m in
    (match c with
     | Coq_ii1 _ ->
       maponpaths (fun x -> S x) n0 (add (natrem n0 m) (mul (natdiv n0 m) m))
         (natdivremrule n0 m is)
     | Coq_ii2 _ ->
       let is' = lthnatrem n0 m is in
       let c0 = natgthchoice2 m (natrem n0 m) is' in
       (match c0 with
        | Coq_ii1 _ -> assert false (* absurd case *)
        | Coq_ii2 b ->
          let e'' =
            maponpaths (fun x -> S x) n0
              (add (natrem n0 m) (mul (natdiv n0 m) m))
              (natdivremrule n0 m is)
          in
          let e''0 =
            internal_paths_rew (S (natrem n0 m)) e'' m
              (pathsinv0 m (S (natrem n0 m)) b)
          in
          internal_paths_rew_r (add (mul (natdiv n0 m) m) m)
            (add m (mul (natdiv n0 m) m)) e''0
            (natpluscomm (mul (natdiv n0 m) m) m)))

(** val natlehmultnatdiv : nat -> nat -> hProptoType -> hProptoType **)

let natlehmultnatdiv n m is =
  let e = natdivremrule n m is in
  internal_paths_rew_r n (add (natrem n m) (mul (natdiv n m) m))
    (natlehmplusnm (natrem n m) (mul (natdiv n m) m)) e

(** val natdivremunique :
    nat -> nat -> nat -> nat -> nat -> hProptoType -> hProptoType -> nat
    paths -> (nat paths, nat paths) dirprod **)

let rec natdivremunique m i j i' j' lj lj' e =
  match i with
  | O ->
    let e0 = internal_paths_rew (add j O) e j (natplusr0 j) in
    (match i' with
     | O ->
       let e1 = internal_paths_rew (add j' O) e0 j' (natplusr0 j') in
       { pr1 = Coq_paths_refl; pr2 = e1 }
     | S _ -> assert false (* absurd case *))
  | S n ->
    (match i' with
     | O -> assert false (* absurd case *)
     | S n0 ->
       let e0 =
         internal_paths_rew_r (add (add j (mul n m)) m)
           (add j (add (mul n m) m)) e (natplusassoc j (mul n m) m)
       in
       let e1 =
         internal_paths_rew_r (add (add j' (mul n0 m)) m)
           (add j' (add (mul n0 m) m)) e0 (natplusassoc j' (mul n0 m) m)
       in
       let e' =
         invmaponpathsincl (fun m0 -> add m0 m) (isinclnatplusr m)
           (add j (mul n m)) (add j' (mul n0 m)) e1
       in
       let ee = natdivremunique m n j n0 j' lj lj' e' in
       make_dirprod (maponpaths (fun x -> S x) n n0 ee.pr1) ee.pr2)

(** val natdivremandmultl :
    nat -> nat -> nat -> hProptoType -> hProptoType -> (nat paths, nat paths)
    dirprod **)

let natdivremandmultl n m k ism iskm =
  let ak = natdiv (mul k n) (mul k m) in
  let a = natdiv n m in
  let b = natrem n m in
  let e1 =
    internal_paths_rew_r
      (add (natrem (mul k n) (mul k m))
        (mul (natdiv (mul k n) (mul k m)) (mul k m))) (mul k n)
      (internal_paths_rew_r (mul k m) (mul m k)
        (internal_paths_rew_r (mul a (mul m k)) (mul (mul a m) k)
          (internal_paths_rew_r (add (mul b k) (mul (mul a m) k))
            (mul (add b (mul a m)) k)
            (internal_paths_rew_r (add (natrem n m) (mul (natdiv n m) m)) n
              (natmultcomm k n)
              (pathsinv0 n (add (natrem n m) (mul (natdiv n m) m))
                (natdivremrule n m ism)))
            (pathsinv0 (mul (add b (mul a m)) k)
              (add (mul b k) (mul (mul a m) k)) (natrdistr b (mul a m) k)))
          (pathsinv0 (mul (mul a m) k) (mul a (mul m k)) (natmultassoc a m k)))
        (natmultcomm k m))
      (pathsinv0 (mul k n)
        (add (natrem (mul k n) (mul k m))
          (mul (natdiv (mul k n) (mul k m)) (mul k m)))
        (natdivremrule (mul k n) (mul k m) iskm))
  in
  let l1 = lthnatrem n m ism in
  let l1' = natlthandmultr (natrem n m) m k (natneq0andmultlinv k m iskm) l1
  in
  let l1'0 = internal_paths_rew (mul m k) l1' (mul k m) (natmultcomm m k) in
  let int =
    natdivremunique (mul k m) ak (natrem (mul k n) (mul k m)) a
      (mul (natrem n m) k) (lthnatrem (mul k n) (mul k m) iskm) l1'0 e1
  in
  { pr1 = int.pr1; pr2 =
  (internal_paths_rew_r (mul k b) (mul b k) int.pr2 (natmultcomm k b)) }

(** val natdivandmultl :
    nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths **)

let natdivandmultl n m k ism iskm =
  (natdivremandmultl n m k ism iskm).pr1

(** val natremandmultl :
    nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths **)

let natremandmultl n m k ism iskm =
  (natdivremandmultl n m k ism iskm).pr2

(** val natdivremandmultr :
    nat -> nat -> nat -> hProptoType -> hProptoType -> (nat paths, nat paths)
    dirprod **)

let natdivremandmultr n m k ism ismk =
  internal_paths_rew_r (mul m k) (mul k m)
    (let ismk0 = internal_paths_rew (mul m k) ismk (mul k m) (natmultcomm m k)
     in
     internal_paths_rew_r (mul n k) (mul k n)
       (internal_paths_rew_r (mul (natrem n m) k) (mul k (natrem n m))
         (natdivremandmultl n m k ism ismk0) (natmultcomm (natrem n m) k))
       (natmultcomm n k)) (natmultcomm m k)

(** val natdivandmultr :
    nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths **)

let natdivandmultr n m k ism ismk =
  (natdivremandmultr n m k ism ismk).pr1

(** val natremandmultr :
    nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths **)

let natremandmultr n m k ism ismk =
  (natdivremandmultr n m k ism ismk).pr2

(** val natpower : nat -> nat -> nat **)

let rec natpower n = function
| O -> S O
| S m' -> mul n (natpower n m')

(** val factorial : nat -> nat **)

let rec factorial = function
| O -> S O
| S n' -> mul (S n') (factorial n')

(** val di : nat -> nat -> nat **)

let di i x =
  match natlthorgeh x i with
  | Coq_ii1 _ -> x
  | Coq_ii2 _ -> S x

(** val di_eq1 : nat -> nat -> hProptoType -> nat paths **)

let di_eq1 i x lt =
  let c = natlthorgeh x i in
  (match c with
   | Coq_ii1 _ -> Coq_paths_refl
   | Coq_ii2 b -> fromempty (natgehtonegnatlth x i b lt))

(** val di_eq2 : nat -> nat -> hProptoType -> nat paths **)

let di_eq2 i x lt =
  let c = natlthorgeh x i in
  (match c with
   | Coq_ii1 a -> fromempty (natlthtonegnatgeh x i a lt)
   | Coq_ii2 _ -> Coq_paths_refl)

(** val di_neq_i : nat -> nat -> hProptoType **)

let di_neq_i i x =
  nat_nopath_to_neq i (di i x) (fun _ ->
    let c = natlthorgeh x i in
    (match c with
     | Coq_ii1 a -> isirreflnatlth i a
     | Coq_ii2 b -> negnatgehnsn x b))

(** val natlehdinsn : nat -> nat -> hProptoType **)

let natlehdinsn i n =
  let c = natlthorgeh n i in
  (match c with
   | Coq_ii1 _ -> natlthtoleh n (S n) (natlthnsn n)
   | Coq_ii2 _ -> isreflnatleh (S n))

(** val natgehdinn : nat -> nat -> hProptoType **)

let natgehdinn i n =
  let c = natlthorgeh n i in
  (match c with
   | Coq_ii1 _ -> isreflnatleh n
   | Coq_ii2 _ -> natlthtoleh n (S n) (natlthnsn n))

(** val isincldi : nat -> (nat, nat) isincl **)

let isincldi i y =
  isinclbetweensets (di i) isasetnat isasetnat (fun x x' e ->
    let c = natlthorgeh x i in
    (match c with
     | Coq_ii1 _ ->
       let c0 = natlthorgeh x' i in
       (match c0 with
        | Coq_ii1 _ -> e
        | Coq_ii2 _ -> assert false (* absurd case *))
     | Coq_ii2 _ ->
       let c0 = natlthorgeh x' i in
       (match c0 with
        | Coq_ii1 _ -> assert false (* absurd case *)
        | Coq_ii2 _ -> invmaponpathsS x x' e))) y

(** val neghfiberdi : nat -> (nat, nat) hfiber neg **)

let neghfiberdi i hf =
  let j = hf.pr1 in
  let c = natlthorgeh j i in
  (match c with
   | Coq_ii1 a -> isirreflnatlth j a
   | Coq_ii2 b -> negnatgehnsn j b)

(** val iscontrhfiberdi :
    nat -> nat -> hProptoType -> (nat, nat) hfiber iscontr **)

let iscontrhfiberdi i j _ =
  iscontraprop1 (isincldi i j)
    (let c = natlthorgeh j i in
     match c with
     | Coq_ii1 _ ->
       { pr1 = j; pr2 =
         (let c0 = natlthorgeh j i in
          match c0 with
          | Coq_ii1 _ -> Coq_paths_refl
          | Coq_ii2 _ -> assert false (* absurd case *)) }
     | Coq_ii2 b ->
       let c0 = natgehchoice2 j i b in
       (match c0 with
        | Coq_ii1 _ ->
          (match j with
           | O -> assert false (* absurd case *)
           | S n ->
             { pr1 = n; pr2 =
               (let c1 = natlthorgeh n i in
                match c1 with
                | Coq_ii1 _ -> assert false (* absurd case *)
                | Coq_ii2 _ -> Coq_paths_refl) })
        | Coq_ii2 _ -> assert false (* absurd case *)))

(** val isdecincldi : nat -> (nat, nat) isdecincl **)

let isdecincldi i j =
  isdecpropif (isincldi i j)
    (let c = nat_eq_or_neq i j in
     match c with
     | Coq_ii1 _ -> Coq_ii2 (neghfiberdi i)
     | Coq_ii2 b -> Coq_ii1 (iscontrhfiberdi i j b).pr1)

(** val si : nat -> nat -> nat **)

let si i x =
  match natlthorgeh i x with
  | Coq_ii1 _ -> sub x (S O)
  | Coq_ii2 _ -> x

(** val natleh_neq :
    nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natleh_neq i j le ne =
  let c = natlehchoice i j le in
  (match c with
   | Coq_ii1 a -> a
   | Coq_ii2 _ -> fromempty (isirrefl_natneq i ne))

(** val natminusminus : nat -> nat -> nat -> nat paths **)

let rec natminusminus n i =
  match n with
  | O -> (fun _ -> Coq_paths_refl)
  | S n0 ->
    (match i with
     | O -> (fun _ -> Coq_paths_refl)
     | S n1 -> natminusminus n0 n1)

(** val natltplusS : nat -> nat -> hProptoType **)

let natltplusS n i =
  internal_paths_rew (add i O)
    (internal_paths_rew_r (add (add i O) (S n)) (add i (add O (S n)))
      (natlthandplusl O (add O (S n)) i (Obj.magic Coq_paths_refl))
      (natplusassoc i O (S n))) i (natplusr0 i)

(** val nat_split :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let nat_split n m i p h =
  natlthandminusl i (add m n) n p (natlehlthtrans n i (add n m) h p)

(** val natplusminusle : nat -> nat -> nat -> hProptoType -> nat paths **)

let natplusminusle a b c e =
  let e0 = minusplusnmm b c e in
  internal_paths_rew (add (sub b c) c)
    (internal_paths_rew (add (add a (sub b c)) c)
      (internal_paths_rew_r (sub (add (sub b c) c) c) (sub b c)
        (internal_paths_rew_r (sub (add (add a (sub b c)) c) c)
          (add a (sub b c)) Coq_paths_refl (plusminusnmm (add a (sub b c)) c))
        (plusminusnmm (sub b c) c)) (add a (add (sub b c) c))
      (natplusassoc a (sub b c) c)) b e0

(** val natdiffplusdiff :
    nat -> nat -> nat -> hProptoType -> hProptoType -> nat paths **)

let natdiffplusdiff a b c r s =
  natplusrcan (sub a c) (add (sub a b) (sub b c)) c
    (internal_paths_rew_r (add (add (sub a b) (sub b c)) c)
      (add (sub a b) (add (sub b c) c))
      (internal_paths_rew_r (add (sub b c) c) b
        (internal_paths_rew_r (add (sub a c) c) a
          (pathsinv0 (add (sub a b) b) a (minusplusnmm a b r))
          (minusplusnmm a c (istransnatleh c b a s r))) (minusplusnmm b c s))
      (natplusassoc (sub a b) (sub b c) c))

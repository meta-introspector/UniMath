open NaturalNumbers
open NegativePropositions
open PartA
open PartB
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

let __ = let rec f _ = Obj.repr f in Obj.repr f

type stn = (nat, hProptoType) total2

(** val make_stn : nat -> nat -> hProptoType -> stn **)

let make_stn _ m l =
  { pr1 = m; pr2 = l }

(** val stntonat : nat -> stn -> nat **)

let stntonat _ t =
  t.pr1

(** val stnlt : nat -> stn -> hProptoType **)

let stnlt _ i =
  i.pr2

(** val isinclstntonat : nat -> (stn, nat) isincl **)

let isinclstntonat n y =
  isinclpr1 (fun x -> (natlth x n).pr2) y

(** val stn_ne_iff_neq :
    nat -> stn -> stn -> (stn paths neg, hProptoType) logeq **)

let stn_ne_iff_neq n i j =
  { pr1 = (fun ne ->
    nat_nopath_to_neq (stntonat n i) (stntonat n j) (fun e ->
      ne (subtypePath_prop (fun x -> natlth x n) i j e))); pr2 =
    (fun neq e ->
    nat_neq_to_nopath (stntonat n i) (stntonat n j) neq
      (maponpaths (stntonat n) i j e)) }

(** val stnneq : nat -> stn neqReln **)

let stnneq n i j =
  { pr1 = __; pr2 = { pr1 =
    (propproperty (negProp_to_hProp (natneq (stntonat n i) (stntonat n j))));
    pr2 = (stn_ne_iff_neq n i j) } }

(** val isisolatedinstn : nat -> stn -> stn isisolated **)

let isisolatedinstn n x =
  isisolatedinclb (stntonat n) (isinclstntonat n) x
    (isisolatedn (stntonat n x))

(** val isdeceqstn : nat -> stn isdeceq **)

let isdeceqstn =
  isisolatedinstn

(** val lastelement : nat -> stn **)

let lastelement n =
  { pr1 = n; pr2 = (natgthsnn n) }

(** val firstelement : nat -> stn **)

let firstelement n =
  { pr1 = O; pr2 = (natgthsn0 n) }

(** val lastValue : nat -> (stn -> 'a1) -> 'a1 **)

let lastValue n x =
  x (lastelement n)

(** val dualelement_0_empty : nat -> stn -> nat paths -> empty **)

let dualelement_0_empty _ i _ =
  negnatlthn0 (stntonat O i) (stnlt O i)

(** val dualelement_lt : nat -> nat -> hProptoType -> hProptoType **)

let dualelement_lt i n h =
  internal_paths_rew_r (sub (sub n (S O)) i) (sub n (add (S O) i))
    (natminuslthn n (add (S O) i) h (Obj.magic Coq_paths_refl))
    (natminusminus n (S O) i)

(** val dualelement : nat -> stn -> stn **)

let dualelement n i =
  let c = natchoice0 n in
  (match c with
   | Coq_ii1 a ->
     make_stn n (sub (sub n (S O)) (stntonat n i))
       (fromempty (dualelement_0_empty n i a))
   | Coq_ii2 b ->
     make_stn n (sub (sub n (S O)) (stntonat n i))
       (dualelement_lt (stntonat n i) n b))

(** val stn_left : nat -> nat -> stn -> stn **)

let stn_left m n i =
  { pr1 = i.pr1; pr2 =
    (natlthlehtrans i.pr1 m (add m n) i.pr2 (natlehnplusnm m n)) }

(** val stn_right : nat -> nat -> stn -> stn **)

let stn_right m n i =
  { pr1 = (add m i.pr1); pr2 = (natlthandplusl i.pr1 n m i.pr2) }

(** val stn_left_compute : nat -> nat -> stn -> nat paths **)

let stn_left_compute _ _ _ =
  Coq_paths_refl

(** val stn_right_compute : nat -> nat -> stn -> nat paths **)

let stn_right_compute _ _ _ =
  Coq_paths_refl

(** val stn_left_0 : nat -> stn -> nat paths -> stn paths **)

let stn_left_0 m i e =
  subtypePath_prop (fun x -> natlth x (add m O)) (stn_left m O i)
    (transportf m (add m O) e i) Coq_paths_refl

(** val stn_left' : nat -> nat -> hProptoType -> stn -> stn **)

let stn_left' m n le i =
  make_stn n (stntonat m i) (natlthlehtrans (stntonat m i) m n (stnlt m i) le)

(** val stn_left'' : nat -> nat -> hProptoType -> stn -> stn **)

let stn_left'' m n le i =
  make_stn n (stntonat m i) (istransnatlth (stntonat m i) m n (stnlt m i) le)

(** val stn_left_compare : nat -> nat -> hProptoType -> (stn -> stn) paths **)

let stn_left_compare m n r =
  Obj.magic funextfun (stn_left' m (add m n) r) (stn_left m n) (fun i ->
    Obj.magic subtypePath_prop (fun x -> natlth x (add m n))
      (stn_left' m (add m n) r (Obj.magic i)) (stn_left m n (Obj.magic i))
      Coq_paths_refl)

(** val dni : nat -> stn -> stn -> stn **)

let dni n i x =
  { pr1 = (di (stntonat (S n) i) (stntonat n x)); pr2 =
    (let c = natlthorgeh (stntonat n x) (stntonat (S n) i) in
     match c with
     | Coq_ii1 _ -> natgthtogths n (stntonat n x) x.pr2
     | Coq_ii2 _ -> x.pr2) }

(** val compute_pr1_dni_last : nat -> stn -> nat paths **)

let compute_pr1_dni_last n i =
  let c = natlthorgeh (stntonat n i) n in
  (match c with
   | Coq_ii1 _ -> Coq_paths_refl
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val dni_last : nat -> stn -> nat paths **)

let dni_last n i =
  let i0 = i.pr1 in
  let c = natlthorgeh i0 n in
  (match c with
   | Coq_ii1 _ -> Coq_paths_refl
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val dni_firstelement : nat -> stn -> stn **)

let dni_firstelement _ h =
  { pr1 = (S h.pr1); pr2 = h.pr2 }

(** val dni_lastelement : nat -> stn -> stn **)

let dni_lastelement n h =
  { pr1 = h.pr1; pr2 = (natlthtolths h.pr1 n h.pr2) }

(** val replace_dni_last : nat -> (stn -> stn) paths **)

let replace_dni_last n =
  Obj.magic funextfun (dni n (lastelement n)) (dni_lastelement n) (fun i ->
    Obj.magic subtypePath_prop (fun x -> natlth x (S n))
      (dni n (lastelement n) (Obj.magic i)) (dni_lastelement n (Obj.magic i))
      (compute_pr1_dni_last n (Obj.magic i)))

type stn_compl = stn compl_ne

(** val weqdnicompl : nat -> stn -> (stn, stn_compl) weq **)

let weqdnicompl n i =
  let w = weqdicompl (stntonat (S n) i) in
  let eq = fun j ->
    let c = natlthorgeh j (stntonat (S n) i) in
    (match c with
     | Coq_ii1 a ->
       { pr1 = (natlthtolths j n); pr2 = (fun _ ->
         natlehlthtrans (S j) (stntonat (S n) i) (S n) a i.pr2) }
     | Coq_ii2 _ -> { pr1 = idfun; pr2 = idfun })
  in
  weqcomp
    (weq_subtypes w (fun j -> natlth j n) (fun j -> natlth j.pr1 (S n)) eq)
    weqtotal2comm12

(** val weqdnicoprod_provisional :
    nat -> stn -> ((stn, coq_unit) coprod, stn) weq **)

let weqdnicoprod_provisional n j =
  weqcomp (weqcoprodf (weqdnicompl n j) idweq)
    (weqrecompl_ne j (isdeceqstn (S n) j) (stnneq (S n) j))

(** val weqdnicoprod_map : nat -> stn -> (stn, coq_unit) coprod -> stn **)

let weqdnicoprod_map n j = function
| Coq_ii1 a -> dni n j a
| Coq_ii2 _ -> j

(** val weqdnicoprod_compute :
    nat -> stn -> ((stn, coq_unit) coprod, stn) homot **)

let weqdnicoprod_compute n j = function
| Coq_ii1 a ->
  subtypePath_prop (fun x -> natlth x (S n))
    (pr1weq (weqdnicoprod_provisional n j) (Coq_ii1 a))
    (weqdnicoprod_map n j (Coq_ii1 a)) Coq_paths_refl
| Coq_ii2 _ -> Coq_paths_refl

(** val weqdnicoprod : nat -> stn -> ((stn, coq_unit) coprod, stn) weq **)

let weqdnicoprod n j =
  make_weq (weqdnicoprod_map n j)
    (isweqhomot (pr1weq (weqdnicoprod_provisional n j))
      (weqdnicoprod_map n j) (weqdnicoprod_compute n j)
      (weqproperty (weqdnicoprod_provisional n j)))

(** val weqoverdnicoprod :
    nat -> ((stn, 'a1) total2, ((stn, 'a1) total2, 'a1) coprod) weq **)

let weqoverdnicoprod n =
  weqcomp (weqtotal2overcoprod' (weqdnicoprod n (lastelement n)))
    (weqcoprodf idweq weqtotal2overunit)

(** val negstn0 : stn neg **)

let negstn0 x =
  let a = x.pr1 in let b = x.pr2 in negnatlthn0 a b

(** val weqstn0toempty : (stn, empty) weq **)

let weqstn0toempty =
  weqtoempty negstn0

(** val weqstn1tounit : (stn, coq_unit) weq **)

let weqstn1tounit =
  weqcontrcontr { pr1 = (lastelement O); pr2 = (fun t ->
    let t0 = t.pr1 in
    let l = t.pr2 in
    let e = natlth1tois0 t0 l in
    invmaponpathsincl (stntonat (S O)) (isinclstntonat (S O))
      (make_stn (S O) t0 l) (lastelement O) e) } iscontrunit

(** val isinjstntonat : nat -> hProptoType **)

let isinjstntonat n =
  Obj.magic (fun i j -> subtypePath_prop (fun x -> natlth x n) i j)

(** val weqfromcoprodofstn_invmap : nat -> nat -> stn -> (stn, stn) coprod **)

let weqfromcoprodofstn_invmap n m i =
  let c = natlthorgeh (stntonat (add n m) i) n in
  (match c with
   | Coq_ii1 a -> Coq_ii1 (make_stn n (stntonat (add n m) i) a)
   | Coq_ii2 b ->
     Coq_ii2
       (make_stn m (sub (stntonat (add n m) i) n)
         (nat_split n m i.pr1 i.pr2 b)))

(** val weqfromcoprodofstn_invmap_r0 :
    nat -> stn -> (stn, stn) coprod paths **)

let weqfromcoprodofstn_invmap_r0 n i =
  let c = natlthorgeh (stntonat (add n O) i) n in
  (match c with
   | Coq_ii1 a ->
     maponpaths (fun x -> Coq_ii1 x) (make_stn n (stntonat (add n O) i) a)
       (transportf (add n O) n (natplusr0 n) i)
       (subtypePath_prop (fun x -> natlth x n)
         (make_stn n (stntonat (add n O) i) a)
         (transportf (add n O) n (natplusr0 n) i) Coq_paths_refl)
   | Coq_ii2 b -> fromempty (natgehtonegnatlth (stntonat n i) n b (stnlt n i)))

(** val weqfromcoprodofstn_map : nat -> nat -> (stn, stn) coprod -> stn **)

let weqfromcoprodofstn_map n m = function
| Coq_ii1 a -> stn_left n m a
| Coq_ii2 b -> stn_right n m b

(** val weqfromcoprodofstn_eq1 :
    nat -> nat -> (stn, stn) coprod -> (stn, stn) coprod paths **)

let weqfromcoprodofstn_eq1 n m = function
| Coq_ii1 a ->
  let c = natlthorgeh (stntonat (add n m) (stn_left n m a)) n in
  (match c with
   | Coq_ii1 a0 ->
     maponpaths (fun x0 -> Coq_ii1 x0)
       (make_stn n (stntonat (add n m) (stn_left n m a)) a0) a
       (Obj.magic isinjstntonat n
         (make_stn n (stntonat (add n m) (stn_left n m a)) a0) a
         Coq_paths_refl)
   | Coq_ii2 b -> fromempty (natlthtonegnatgeh (stntonat n a) n (stnlt n a) b))
| Coq_ii2 b ->
  let c = natlthorgeh (stntonat (add n m) (stn_right n m b)) n in
  (match c with
   | Coq_ii1 a ->
     fromempty
       (let tmp =
          natlehlthtrans n (add n (stntonat m b)) n
            (natlehnplusnm n (stntonat m b)) a
        in
        isirrefl_natneq n (natlthtoneq n n tmp))
   | Coq_ii2 b0 ->
     maponpaths (fun x0 -> Coq_ii2 x0)
       (make_stn m (sub (stntonat (add n m) (stn_right n m b)) n)
         (nat_split n m (stn_right n m b).pr1 (stn_right n m b).pr2 b0)) b
       (Obj.magic isinjstntonat m
         (make_stn m (sub (stntonat (add n m) (stn_right n m b)) n)
           (nat_split n m (stn_right n m b).pr1 (stn_right n m b).pr2 b0)) b
         (internal_paths_rew_r (add n b.pr1) (add b.pr1 n)
           (plusminusnmm b.pr1 n) (natpluscomm n b.pr1))))

(** val weqfromcoprodofstn_eq2 : nat -> nat -> stn -> stn paths **)

let weqfromcoprodofstn_eq2 n m x =
  let c = natlthorgeh (stntonat (add n m) x) n in
  (match c with
   | Coq_ii1 a ->
     Obj.magic isinjstntonat (add n m)
       (stn_left n m (make_stn n (stntonat (add n m) x) a)) x Coq_paths_refl
   | Coq_ii2 b ->
     let c0 = natchoice0 m in
     (match c0 with
      | Coq_ii1 _ ->
        fromempty (natlthtonegnatgeh (stntonat n x) n (stnlt n x) b)
      | Coq_ii2 _ ->
        Obj.magic isinjstntonat (add n m)
          (stn_right n m
            (make_stn m (sub (stntonat (add n m) x) n)
              (nat_split n m x.pr1 x.pr2 b))) x
          (internal_paths_rew_r (add n (sub (stntonat (add n m) x) n))
            (add (sub (stntonat (add n m) x) n) n) (minusplusnmm x.pr1 n b)
            (natpluscomm n (sub (stntonat (add n m) x) n)))))

(** val weqfromcoprodofstn : nat -> nat -> ((stn, stn) coprod, stn) weq **)

let weqfromcoprodofstn n m =
  { pr1 = (weqfromcoprodofstn_map n m); pr2 =
    (isweq_iso (weqfromcoprodofstn_map n m) (weqfromcoprodofstn_invmap n m)
      (weqfromcoprodofstn_eq1 n m) (weqfromcoprodofstn_eq2 n m)) }

(** val stnsum : nat -> (stn -> nat) -> nat **)

let rec stnsum n f =
  match n with
  | O -> O
  | S n0 ->
    add (stnsum n0 (fun i -> f (dni n0 (lastelement n0) i)))
      (f (lastelement n0))

(** val stnsum_step : nat -> (stn -> nat) -> nat paths **)

let stnsum_step _ _ =
  Coq_paths_refl

(** val stnsum_eq :
    nat -> (stn -> nat) -> (stn -> nat) -> (stn, nat) homot -> nat paths **)

let rec stnsum_eq n f g h =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    internal_paths_rew_r (stnsum (S n0) f)
      (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
        (f (lastelement n0)))
      (internal_paths_rew_r (stnsum (S n0) g)
        (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) g))
          (g (lastelement n0)))
        (maponpaths (fun i -> add i (f (lastelement n0)))
          (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
          (stnsum n0 (funcomp (dni n0 (lastelement n0)) g))
          (stnsum_eq n0 (funcomp (dni n0 (lastelement n0)) f)
            (funcomp (dni n0 (lastelement n0)) g) (fun x ->
            h (dni n0 (lastelement n0) x)))) (stnsum_step n0 g))
      (stnsum_step n0 f)

(** val transport_stnsum :
    nat -> nat -> nat paths -> (stn -> nat) -> nat paths **)

let transport_stnsum _ _ _ _ =
  Coq_paths_refl

(** val stnsum_left_right : nat -> nat -> (stn -> nat) -> nat paths **)

let rec stnsum_left_right m n f =
  match n with
  | O ->
    internal_paths_rew_r (add (stnsum m (funcomp (stn_left m O) f)) O)
      (stnsum m (funcomp (stn_left m O) f))
      (let e = pathsinv0 (add m O) m (natplusr0 m) in
       internal_paths_rew_r (stnsum (add m O) f)
         (stnsum m (fun i -> f (transportf m (add m O) e i)))
         (stnsum_eq m (fun i -> f (transportf m (add m O) e i))
           (funcomp (stn_left m O) f) (fun i ->
           maponpaths f (transportf m (add m O) e i) (stn_left m O i)
             (pathsinv0 (stn_left m O i) (transportf m (add m O) e i)
               (stn_left_0 m i e)))) (transport_stnsum m (add m O) e f))
      (natplusr0 (stnsum m (funcomp (stn_left m O) f)))
  | S n0 ->
    internal_paths_rew_r (stnsum (S n0) (funcomp (stn_right m (S n0)) f))
      (add
        (stnsum n0
          (funcomp (dni n0 (lastelement n0)) (funcomp (stn_right m (S n0)) f)))
        (funcomp (stn_right m (S n0)) f (lastelement n0)))
      (let e = pathsinv0 (add m (S n0)) (S (add m n0)) (natplusnsm m n0) in
       internal_paths_rew_r (stnsum (add m (S n0)) f)
         (stnsum (S (add m n0)) (fun i ->
           f (transportf (S (add m n0)) (add m (S n0)) e i)))
         (internal_paths_rew_r
           (stnsum (S (add m n0)) (fun i ->
             f (transportf (S (add m n0)) (add m (S n0)) e i)))
           (add
             (stnsum (add m n0)
               (funcomp (dni (add m n0) (lastelement (add m n0))) (fun i ->
                 f (transportf (S (add m n0)) (add m (S n0)) e i))))
             (f
               (transportf (S (add m n0)) (add m (S n0)) e
                 (lastelement (add m n0)))))
           (internal_paths_rew
             (add
               (add (stnsum m (funcomp (stn_left m (S n0)) f))
                 (stnsum n0
                   (funcomp (dni n0 (lastelement n0))
                     (funcomp (stn_right m (S n0)) f))))
               (funcomp (stn_right m (S n0)) f (lastelement n0)))
             (map_on_two_paths add
               (stnsum (add m n0)
                 (funcomp (dni (add m n0) (lastelement (add m n0))) (fun i ->
                   f (transportf (S (add m n0)) (add m (S n0)) e i))))
               (add (stnsum m (funcomp (stn_left m (S n0)) f))
                 (stnsum n0
                   (funcomp (dni n0 (lastelement n0))
                     (funcomp (stn_right m (S n0)) f))))
               (f
                 (transportf (S (add m n0)) (add m (S n0)) e
                   (lastelement (add m n0))))
               (funcomp (stn_right m (S n0)) f (lastelement n0))
               (internal_paths_rew_r
                 (stnsum (add m n0)
                   (funcomp (dni (add m n0) (lastelement (add m n0)))
                     (fun i ->
                     f (transportf (S (add m n0)) (add m (S n0)) e i))))
                 (add
                   (stnsum m
                     (funcomp (stn_left m n0)
                       (funcomp (dni (add m n0) (lastelement (add m n0)))
                         (fun i ->
                         f (transportf (S (add m n0)) (add m (S n0)) e i)))))
                   (stnsum n0
                     (funcomp (stn_right m n0)
                       (funcomp (dni (add m n0) (lastelement (add m n0)))
                         (fun i ->
                         f (transportf (S (add m n0)) (add m (S n0)) e i))))))
                 (map_on_two_paths add
                   (stnsum m
                     (funcomp (stn_left m n0)
                       (funcomp (dni (add m n0) (lastelement (add m n0)))
                         (fun i ->
                         f (transportf (S (add m n0)) (add m (S n0)) e i)))))
                   (stnsum m (funcomp (stn_left m (S n0)) f))
                   (stnsum n0
                     (funcomp (stn_right m n0)
                       (funcomp (dni (add m n0) (lastelement (add m n0)))
                         (fun i ->
                         f (transportf (S (add m n0)) (add m (S n0)) e i)))))
                   (stnsum n0
                     (funcomp (dni n0 (lastelement n0))
                       (funcomp (stn_right m (S n0)) f)))
                   (stnsum_eq m
                     (funcomp (stn_left m n0)
                       (funcomp (dni (add m n0) (lastelement (add m n0)))
                         (fun i ->
                         f (transportf (S (add m n0)) (add m (S n0)) e i))))
                     (funcomp (stn_left m (S n0)) f) (fun i ->
                     maponpaths f
                       (transportf (S (add m n0)) (add m (S n0)) e
                         (dni (add m n0) (lastelement (add m n0))
                           (stn_left m n0 i))) (stn_left m (S n0) i)
                       (subtypePath_prop (fun x -> natlth x (add m (S n0)))
                         (transportf (S (add m n0)) (add m (S n0)) e
                           (dni (add m n0) (lastelement (add m n0))
                             (stn_left m n0 i))) (stn_left m (S n0) i)
                         (internal_paths_rew_r (stn_left m (S n0) i).pr1
                           (stntonat m i)
                           (internal_paths_rew_r
                             (transportf (S (add m n0)) (S (add m n0))
                               Coq_paths_refl
                               (dni (add m n0) (lastelement (add m n0))
                                 (stn_left m n0 i)))
                             (dni (add m n0) (lastelement (add m n0))
                               (stn_left m n0 i))
                             (internal_paths_rew_r
                               (dni (add m n0) (lastelement (add m n0))
                                 (stn_left m n0 i)).pr1
                               (stntonat (add m n0) (stn_left m n0 i))
                               Coq_paths_refl
                               (dni_last (add m n0) (stn_left m n0 i)))
                             (idpath_transportf (S (add m n0))
                               (dni (add m n0) (lastelement (add m n0))
                                 (stn_left m n0 i))))
                           (stn_left_compute m (S n0) i)))))
                   (stnsum_eq n0
                     (funcomp (stn_right m n0)
                       (funcomp (dni (add m n0) (lastelement (add m n0)))
                         (fun i ->
                         f (transportf (S (add m n0)) (add m (S n0)) e i))))
                     (funcomp (dni n0 (lastelement n0))
                       (funcomp (stn_right m (S n0)) f)) (fun i ->
                     maponpaths f
                       (transportf (S (add m n0)) (add m (S n0)) e
                         (dni (add m n0) (lastelement (add m n0))
                           (stn_right m n0 i)))
                       (stn_right m (S n0) (dni n0 (lastelement n0) i))
                       (subtypePath_prop (fun x -> natlth x (add m (S n0)))
                         (transportf (S (add m n0)) (add m (S n0)) e
                           (dni (add m n0) (lastelement (add m n0))
                             (stn_right m n0 i)))
                         (stn_right m (S n0) (dni n0 (lastelement n0) i))
                         (internal_paths_rew_r
                           (stn_right m (S n0) (dni n0 (lastelement n0) i)).pr1
                           (add m
                             (stntonat (S n0) (dni n0 (lastelement n0) i)))
                           (internal_paths_rew_r
                             (transportf (S (add m n0)) (S (add m n0))
                               Coq_paths_refl
                               (dni (add m n0) (lastelement (add m n0))
                                 (stn_right m n0 i)))
                             (dni (add m n0) (lastelement (add m n0))
                               (stn_right m n0 i))
                             (internal_paths_rew_r
                               (dni (add m n0) (lastelement (add m n0))
                                 (stn_right m n0 i)).pr1
                               (stntonat (add m n0) (stn_right m n0 i))
                               (internal_paths_rew_r
                                 (dni n0 (lastelement n0) i).pr1
                                 (stntonat n0 i) Coq_paths_refl
                                 (dni_last n0 i))
                               (dni_last (add m n0) (stn_right m n0 i)))
                             (idpath_transportf (S (add m n0))
                               (dni (add m n0) (lastelement (add m n0))
                                 (stn_right m n0 i))))
                           (stn_right_compute m (S n0)
                             (dni n0 (lastelement n0) i)))))))
                 (stnsum_left_right m n0
                   (funcomp (dni (add m n0) (lastelement (add m n0)))
                     (fun i ->
                     f (transportf (S (add m n0)) (add m (S n0)) e i)))))
               (maponpaths f
                 (transportf (S (add m n0)) (add m (S n0)) e
                   (lastelement (add m n0)))
                 (stn_right m (S n0) (lastelement n0))
                 (subtypePath_prop (fun x -> natlth x (add m (S n0)))
                   (transportf (S (add m n0)) (add m (S n0)) e
                     (lastelement (add m n0)))
                   (stn_right m (S n0) (lastelement n0)) Coq_paths_refl)))
             (add (stnsum m (funcomp (stn_left m (S n0)) f))
               (add
                 (stnsum n0
                   (funcomp (dni n0 (lastelement n0))
                     (funcomp (stn_right m (S n0)) f)))
                 (funcomp (stn_right m (S n0)) f (lastelement n0))))
             (natplusassoc (stnsum m (funcomp (stn_left m (S n0)) f))
               (stnsum n0
                 (funcomp (dni n0 (lastelement n0))
                   (funcomp (stn_right m (S n0)) f)))
               (funcomp (stn_right m (S n0)) f (lastelement n0))))
           (stnsum_step (add m n0) (fun i ->
             f (transportf (S (add m n0)) (add m (S n0)) e i))))
         (transport_stnsum (S (add m n0)) (add m (S n0)) e f))
      (stnsum_step n0 (funcomp (stn_right m (S n0)) f))

(** val stnsum_left_le' :
    nat -> nat -> (stn -> nat) -> hProptoType -> hProptoType **)

let stnsum_left_le' m n f r =
  let s = minusplusnmm n m r in
  let s0 =
    internal_paths_rew (add (sub n m) m) s (add m (sub n m))
      (natpluscomm (sub n m) m)
  in
  internal_paths_rew (add m (sub n m))
    (let k = sub n m in
     fun r0 f0 ->
     internal_paths_rew_r (stn_left' m (add m k) r0) (stn_left m k)
       (internal_paths_rew_r (stnsum (add m k) f0)
         (add (stnsum m (funcomp (stn_left m k) f0))
           (stnsum k (funcomp (stn_right m k) f0)))
         (natlehnplusnm (stnsum m (funcomp (stn_left m k) f0))
           (stnsum k (funcomp (stn_right m k) f0)))
         (stnsum_left_right m k f0)) (stn_left_compare m k r0)) n s0 r f

(** val _c_ : nat -> (stn -> nat) -> (stn, stn) total2 -> hProptoType **)

let _c_ n m ij =
  let i = ij.pr1 in
  let j = ij.pr2 in
  let i0 = i.pr1 in
  let i1 = i.pr2 in
  let j0 = j.pr1 in
  let j1 = j.pr2 in
  let m1 =
    funcomp
      (stn_left'' (stntonat n { pr1 = i0; pr2 = i1 }) n
        (stnlt n { pr1 = i0; pr2 = i1 })) m
  in
  let s = stnsum_left_le' (S i0) n m i1 in
  natlthlehtrans (add (stnsum i0 m1) j0)
    (stnsum (S i0) (funcomp (stn_left' (S i0) n i1) m)) (stnsum n m)
    (match n with
     | O -> assert false (* absurd case *)
     | S n0 ->
       let m2 = funcomp (stn_left'' i0 (S n0) i1) m in
       let t = natlthandplusl j0 (m { pr1 = i0; pr2 = i1 }) (stnsum i0 m2) j1
       in
       natlthlehtrans (add (stnsum i0 m2) j0)
         (add (stnsum i0 m2) (m { pr1 = i0; pr2 = i1 }))
         (stnsum (S i0) (funcomp (stn_left' (S i0) (S n0) i1) m)) t
         (let a = add (stnsum i0 m2) (m { pr1 = i0; pr2 = i1 }) in
          isreflnatleh a)) s

(** val weqstnsum_map : nat -> (stn -> nat) -> (stn, stn) total2 -> stn **)

let weqstnsum_map n m ij =
  make_stn (stnsum n m)
    (add
      (stnsum (stntonat n ij.pr1)
        (funcomp (stn_left'' (stntonat n ij.pr1) n (stnlt n ij.pr1)) m))
      (stntonat (m ij.pr1) ij.pr2)) (_c_ n m ij)

(** val weqstnsum_invmap : nat -> (stn -> nat) -> stn -> (stn, stn) total2 **)

let rec weqstnsum_invmap n m l =
  match n with
  | O -> fromempty (negstn0 l)
  | S n0 ->
    let ls =
      weqfromcoprodofstn_invmap
        (stnsum n0 (funcomp (dni n0 (lastelement n0)) m))
        (m (lastelement n0)) l
    in
    (match ls with
     | Coq_ii1 a ->
       total2_base_map (dni n0 (lastelement n0))
         (weqstnsum_invmap n0 (funcomp (dni n0 (lastelement n0)) m) a)
     | Coq_ii2 b -> { pr1 = (lastelement n0); pr2 = b })

(** val weqstnsum_invmap_step1 :
    nat -> (stn -> nat) -> stn -> (stn, stn) total2 paths **)

let weqstnsum_invmap_step1 n f j =
  internal_paths_rew_r
    (weqfromcoprodofstn_invmap
      (stnsum n (fun x -> f (dni n (lastelement n) x))) (f (lastelement n))
      (weqfromcoprodofstn_map
        (stnsum n (fun x -> f (dni n (lastelement n) x))) (f (lastelement n))
        (Coq_ii1 j))) (Coq_ii1 j) Coq_paths_refl
    (weqfromcoprodofstn_eq1 (stnsum n (fun x -> f (dni n (lastelement n) x)))
      (f (lastelement n)) (Coq_ii1 j))

(** val weqstnsum_invmap_step2 :
    nat -> (stn -> nat) -> stn -> (stn, stn) total2 paths **)

let weqstnsum_invmap_step2 n f k =
  internal_paths_rew_r
    (weqfromcoprodofstn_invmap
      (stnsum n (fun x -> f (dni n (lastelement n) x))) (f (lastelement n))
      (weqfromcoprodofstn_map
        (stnsum n (fun x -> f (dni n (lastelement n) x))) (f (lastelement n))
        (Coq_ii2 k))) (Coq_ii2 k) Coq_paths_refl
    (weqfromcoprodofstn_eq1 (stnsum n (fun x -> f (dni n (lastelement n) x)))
      (f (lastelement n)) (Coq_ii2 k))

(** val weqstnsum1_prelim :
    nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq **)

let rec weqstnsum1_prelim n f =
  match n with
  | O -> weqempty (funcomp (fun t -> t.pr1) negstn0) negstn0
  | S n0 ->
    weqcomp
      (weqcomp (weqoverdnicoprod n0)
        (weqcoprodf1
          (weqstnsum1_prelim n0 (fun i -> f (dni n0 (lastelement n0) i)))))
      (weqfromcoprodofstn (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
        (f (lastelement n0)))

(** val weqstnsum1_step :
    nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq paths **)

let weqstnsum1_step _ _ =
  Coq_paths_refl

(** val weqstnsum1_prelim_eq :
    nat -> (stn -> nat) -> ((stn, stn) total2, stn) homot **)

let rec weqstnsum1_prelim_eq n f =
  match n with
  | O -> (fun ij -> fromempty (negstn0 ij.pr1))
  | S n0 ->
    internal_paths_rew_r (weqstnsum1_prelim (S n0) f)
      (weqcomp
        (weqcomp (weqoverdnicoprod n0)
          (weqcoprodf1
            (weqstnsum1_prelim n0 (fun i -> f (dni n0 (lastelement n0) i)))))
        (weqfromcoprodofstn (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
          (f (lastelement n0)))) (fun ij ->
      internal_paths_rew_r
        (pr1weq
          (weqcomp
            (weqcomp (weqoverdnicoprod n0)
              (weqcoprodf1
                (weqstnsum1_prelim n0 (fun i ->
                  f (dni n0 (lastelement n0) i)))))
            (weqfromcoprodofstn
              (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
              (f (lastelement n0)))) ij)
        (pr1weq
          (weqfromcoprodofstn
            (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
            (f (lastelement n0)))
          (pr1weq
            (weqcomp (weqoverdnicoprod n0)
              (weqcoprodf1
                (weqstnsum1_prelim n0 (fun i ->
                  f (dni n0 (lastelement n0) i))))) ij))
        (internal_paths_rew_r
          (pr1weq
            (weqcomp (weqoverdnicoprod n0)
              (weqcoprodf1
                (weqstnsum1_prelim n0 (fun i ->
                  f (dni n0 (lastelement n0) i))))) ij)
          (pr1weq
            (weqcoprodf1
              (weqstnsum1_prelim n0 (fun i -> f (dni n0 (lastelement n0) i))))
            (pr1weq (weqoverdnicoprod n0) ij))
          (pathscomp0
            (pr1weq
              (weqfromcoprodofstn
                (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                (f (lastelement n0)))
              (coprodf
                (pr1weq
                  (weqstnsum1_prelim n0 (fun i ->
                    f (dni n0 (lastelement n0) i)))) idfun
                (pr1weq (weqoverdnicoprod n0) ij)))
            (pr1weq
              (weqfromcoprodofstn
                (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                (f (lastelement n0)))
              (coprodf
                (weqstnsum_map n0 (fun i -> f (dni n0 (lastelement n0) i)))
                idfun (pr1weq (weqoverdnicoprod n0) ij)))
            (weqstnsum_map (S n0) f ij)
            (maponpaths
              (pr1weq
                (weqfromcoprodofstn
                  (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                  (f (lastelement n0))))
              (coprodf
                (pr1weq
                  (weqstnsum1_prelim n0 (fun i ->
                    f (dni n0 (lastelement n0) i)))) idfun
                (pr1weq (weqoverdnicoprod n0) ij))
              (coprodf
                (weqstnsum_map n0 (fun i -> f (dni n0 (lastelement n0) i)))
                idfun (pr1weq (weqoverdnicoprod n0) ij))
              (homotcoprodfhomot
                (pr1weq
                  (weqstnsum1_prelim n0 (fun i ->
                    f (dni n0 (lastelement n0) i))))
                (weqstnsum_map n0 (fun i -> f (dni n0 (lastelement n0) i)))
                idfun idfun
                (weqstnsum1_prelim_eq n0 (fun i ->
                  f (dni n0 (lastelement n0) i))) (fun _ -> Coq_paths_refl)
                (pr1weq (weqoverdnicoprod n0) ij)))
            (pathsinv0 (weqstnsum_map (S n0) f ij)
              (pr1weq
                (weqfromcoprodofstn
                  (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                  (f (lastelement n0)))
                (coprodf
                  (weqstnsum_map n0 (fun i -> f (dni n0 (lastelement n0) i)))
                  idfun (pr1weq (weqoverdnicoprod n0) ij)))
              (homotweqinv' (weqstnsum_map (S n0) f) (weqoverdnicoprod n0)
                (fun c ->
                pr1weq
                  (weqfromcoprodofstn
                    (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                    (f (lastelement n0)))
                  (coprodf
                    (weqstnsum_map n0 (fun i ->
                      f (dni n0 (lastelement n0) i))) idfun c)) (fun c ->
                match c with
                | Coq_ii1 a ->
                  let j = a.pr1 in
                  let k = a.pr2 in
                  subtypePath_prop (fun x ->
                    natlth x
                      (add
                        (stnsum n0 (fun i -> f (dni n0 (lastelement n0) i)))
                        (f (lastelement n0))))
                    (make_stn (stnsum (S n0) f)
                      (add
                        (stnsum (stntonat (S n0) (dni n0 (lastelement n0) j))
                          (funcomp
                            (stn_left''
                              (stntonat (S n0) (dni n0 (lastelement n0) j))
                              (S n0)
                              (stnlt (S n0) (dni n0 (lastelement n0) j))) f))
                        (stntonat (f (dni n0 (lastelement n0) j)) k))
                      (_c_ (S n0) f { pr1 = (dni n0 (lastelement n0) j);
                        pr2 = k }))
                    (stn_left
                      (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                      (f (lastelement n0))
                      (make_stn
                        (stnsum n0 (fun i -> f (dni n0 (lastelement n0) i)))
                        (add
                          (stnsum (stntonat n0 j)
                            (funcomp
                              (stn_left'' (stntonat n0 j) n0 (stnlt n0 j))
                              (fun i -> f (dni n0 (lastelement n0) i))))
                          (stntonat (f (dni n0 (lastelement n0) j)) k))
                        (_c_ n0 (fun i -> f (dni n0 (lastelement n0) i))
                          { pr1 = j; pr2 = k })))
                    (let k0 = k.pr1 in
                     maponpaths (fun x -> add x k0)
                       (stnsum (di n0 (stntonat n0 j))
                         (funcomp
                           (stn_left'' (di n0 (stntonat n0 j)) (S n0)
                             (match natlthorgeh (stntonat n0 j) n0 with
                              | Coq_ii1 _ ->
                                natgthtogths n0 (stntonat n0 j) j.pr2
                              | Coq_ii2 _ -> j.pr2)) f))
                       (stnsum (stntonat n0 j)
                         (funcomp
                           (stn_left'' (stntonat n0 j) n0 (stnlt n0 j))
                           (fun i -> f (dni n0 (lastelement n0) i))))
                       (let c0 = natlthorgeh j.pr1 n0 in
                        match c0 with
                        | Coq_ii1 a0 ->
                          stnsum_eq j.pr1 (fun x ->
                            f
                              (stn_left'' j.pr1 (S n0)
                                (natgthtogths n0 j.pr1 j.pr2) x)) (fun x ->
                            f
                              (dni n0 (lastelement n0)
                                (stn_left'' j.pr1 n0 (stnlt n0 j) x)))
                            (fun k1 ->
                            maponpaths f
                              (stn_left'' j.pr1 (S n0)
                                (natgthtogths n0 j.pr1 j.pr2) k1)
                              (dni n0 (lastelement n0)
                                (stn_left'' j.pr1 n0 (stnlt n0 j) k1))
                              (subtypePath_prop (fun x -> natlth x (S n0))
                                (stn_left'' j.pr1 (S n0)
                                  (natgthtogths n0 j.pr1 j.pr2) k1)
                                (dni n0 (lastelement n0)
                                  (stn_left'' j.pr1 n0 (stnlt n0 j) k1))
                                (pathsinv0 (di n0 (stntonat j.pr1 k1))
                                  (stntonat j.pr1 k1)
                                  (di_eq1 n0 (stntonat j.pr1 k1)
                                    (istransnatlth (stntonat j.pr1 k1) j.pr1
                                      n0 (stnlt j.pr1 k1) a0)))))
                        | Coq_ii2 b ->
                          fromempty
                            (natlthtonegnatgeh (stntonat n0 j) n0
                              (stnlt n0 j) b)))
                | Coq_ii2 b ->
                  subtypePath_prop (fun x ->
                    natlth x
                      (add
                        (stnsum n0 (fun i -> f (dni n0 (lastelement n0) i)))
                        (f (lastelement n0))))
                    (make_stn (stnsum (S n0) f)
                      (add
                        (stnsum (stntonat (S n0) (lastelement n0))
                          (funcomp
                            (stn_left'' (stntonat (S n0) (lastelement n0)) (S
                              n0) (stnlt (S n0) (lastelement n0))) f))
                        (stntonat (f (lastelement n0)) b))
                      (_c_ (S n0) f { pr1 = (lastelement n0); pr2 = b }))
                    (stn_right
                      (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                      (f (lastelement n0)) b)
                    (let k = b.pr1 in
                     maponpaths (fun x -> add x k)
                       (stnsum n0
                         (funcomp (stn_left'' n0 (S n0) (natgthsnn n0)) f))
                       (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                       (maponpaths (Obj.magic stnsum n0)
                         (funcomp
                           (Obj.magic stn_left'' n0 (S n0) (natgthsnn n0))
                           (Obj.magic f))
                         (funcomp (Obj.magic dni n0 (lastelement n0))
                           (Obj.magic f))
                         (funextfun
                           (funcomp
                             (Obj.magic stn_left'' n0 (S n0) (natgthsnn n0))
                             (Obj.magic f))
                           (funcomp (Obj.magic dni n0 (lastelement n0))
                             (Obj.magic f)) (fun i ->
                           let i0 = (Obj.magic i).pr1 in
                           let i1 = (Obj.magic i).pr2 in
                           maponpaths (Obj.magic f)
                             (stn_left'' n0 (S n0) (natgthsnn n0) { pr1 = i0;
                               pr2 = i1 })
                             (dni n0 (lastelement n0) { pr1 = i0; pr2 = i1 })
                             (subtypePath_prop (fun x -> natlth x (S n0))
                               (stn_left'' n0 (S n0) (natgthsnn n0) { pr1 =
                                 i0; pr2 = i1 })
                               (dni n0 (lastelement n0) { pr1 = i0; pr2 =
                                 i1 })
                               (pathsinv0 (di n0 i0) i0 (di_eq1 n0 i0 i1))))))))
                ij)))
          (weqcomp_to_funcomp_app ij (weqoverdnicoprod n0)
            (weqcoprodf1
              (weqstnsum1_prelim n0 (fun i -> f (dni n0 (lastelement n0) i))))))
        (weqcomp_to_funcomp_app ij
          (weqcomp (weqoverdnicoprod n0)
            (weqcoprodf1
              (weqstnsum1_prelim n0 (fun i -> f (dni n0 (lastelement n0) i)))))
          (weqfromcoprodofstn
            (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
            (f (lastelement n0))))) (weqstnsum1_step n0 f)

(** val weqstnsum1_prelim_eq' :
    nat -> (stn -> nat) -> (stn, (stn, stn) total2) homot **)

let rec weqstnsum1_prelim_eq' n f =
  match n with
  | O -> (fun k -> fromempty (negstn0 k))
  | S n0 ->
    internal_paths_rew_r (weqstnsum1_prelim (S n0) f)
      (weqcomp
        (weqcomp (weqoverdnicoprod n0)
          (weqcoprodf1
            (weqstnsum1_prelim n0 (fun i -> f (dni n0 (lastelement n0) i)))))
        (weqfromcoprodofstn (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
          (f (lastelement n0)))) (fun k ->
      internal_paths_rew_r
        (invweq
          (weqcomp
            (weqcomp (weqoverdnicoprod n0)
              (weqcoprodf1
                (weqstnsum1_prelim n0 (fun i ->
                  f (dni n0 (lastelement n0) i)))))
            (weqfromcoprodofstn
              (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
              (f (lastelement n0)))))
        (weqcomp
          (invweq
            (weqfromcoprodofstn
              (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
              (f (lastelement n0))))
          (invweq
            (weqcomp (weqoverdnicoprod n0)
              (weqcoprodf1
                (weqstnsum1_prelim n0 (fun i ->
                  f (dni n0 (lastelement n0) i)))))))
        (internal_paths_rew_r
          (invweq
            (weqcomp (weqoverdnicoprod n0)
              (weqcoprodf1
                (weqstnsum1_prelim n0 (fun i ->
                  f (dni n0 (lastelement n0) i))))))
          (weqcomp
            (invweq
              (weqcoprodf1
                (weqstnsum1_prelim n0 (fun i ->
                  f (dni n0 (lastelement n0) i)))))
            (invweq (weqoverdnicoprod n0)))
          (internal_paths_rew_r
            (pr1weq
              (weqcomp
                (invweq
                  (weqfromcoprodofstn
                    (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                    (f (lastelement n0))))
                (weqcomp
                  (invweq
                    (weqcoprodf1
                      (weqstnsum1_prelim n0 (fun i ->
                        f (dni n0 (lastelement n0) i)))))
                  (invweq (weqoverdnicoprod n0)))) k)
            (pr1weq
              (weqcomp
                (invweq
                  (weqcoprodf1
                    (weqstnsum1_prelim n0 (fun i ->
                      f (dni n0 (lastelement n0) i)))))
                (invweq (weqoverdnicoprod n0)))
              (pr1weq
                (invweq
                  (weqfromcoprodofstn
                    (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                    (f (lastelement n0)))) k))
            (internal_paths_rew_r
              (pr1weq
                (weqcomp
                  (invweq
                    (weqcoprodf1
                      (weqstnsum1_prelim n0 (fun i ->
                        f (dni n0 (lastelement n0) i)))))
                  (invweq (weqoverdnicoprod n0)))
                (pr1weq
                  (invweq
                    (weqfromcoprodofstn
                      (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                      (f (lastelement n0)))) k))
              (pr1weq (invweq (weqoverdnicoprod n0))
                (pr1weq
                  (invweq
                    (weqcoprodf1
                      (weqstnsum1_prelim n0 (fun i ->
                        f (dni n0 (lastelement n0) i)))))
                  (pr1weq
                    (invweq
                      (weqfromcoprodofstn
                        (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                        (f (lastelement n0)))) k)))
              (internal_paths_rew_r (pr1weq (invweq (weqoverdnicoprod n0)))
                (invmap (weqoverdnicoprod n0))
                (internal_paths_rew_r
                  (pr1weq
                    (invweq
                      (weqcoprodf1
                        (weqstnsum1_prelim n0 (fun i ->
                          f (dni n0 (lastelement n0) i))))))
                  (invmap
                    (weqcoprodf1
                      (weqstnsum1_prelim n0 (fun i ->
                        f (dni n0 (lastelement n0) i)))))
                  (internal_paths_rew_r
                    (pr1weq
                      (invweq
                        (weqfromcoprodofstn
                          (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                          (f (lastelement n0)))))
                    (invmap
                      (weqfromcoprodofstn
                        (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                        (f (lastelement n0))))
                    (pathscomp0
                      (invmap (weqoverdnicoprod n0)
                        (coprodf
                          (pr1weq
                            (invweq
                              (weqstnsum1_prelim n0 (fun i ->
                                f (dni n0 (lastelement n0) i)))))
                          (pr1weq idweq)
                          (invmap
                            (weqfromcoprodofstn
                              (stnsum n0
                                (funcomp (dni n0 (lastelement n0)) f))
                              (f (lastelement n0))) k)))
                      (invmap (weqoverdnicoprod n0)
                        (coprodf
                          (weqstnsum_invmap n0 (fun i ->
                            f (dni n0 (lastelement n0) i))) (pr1weq idweq)
                          (invmap
                            (weqfromcoprodofstn
                              (stnsum n0
                                (funcomp (dni n0 (lastelement n0)) f))
                              (f (lastelement n0))) k)))
                      (weqstnsum_invmap (S n0) f k)
                      (maponpaths (invmap (weqoverdnicoprod n0))
                        (coprodf
                          (pr1weq
                            (invweq
                              (weqstnsum1_prelim n0 (fun i ->
                                f (dni n0 (lastelement n0) i)))))
                          (pr1weq idweq)
                          (invmap
                            (weqfromcoprodofstn
                              (stnsum n0
                                (funcomp (dni n0 (lastelement n0)) f))
                              (f (lastelement n0))) k))
                        (coprodf
                          (weqstnsum_invmap n0 (fun i ->
                            f (dni n0 (lastelement n0) i))) (pr1weq idweq)
                          (invmap
                            (weqfromcoprodofstn
                              (stnsum n0
                                (funcomp (dni n0 (lastelement n0)) f))
                              (f (lastelement n0))) k))
                        (let c =
                           invmap
                             (weqfromcoprodofstn
                               (stnsum n0
                                 (funcomp (dni n0 (lastelement n0)) f))
                               (f (lastelement n0))) k
                         in
                         homotcoprodfhomot
                           (pr1weq
                             (invweq
                               (weqstnsum1_prelim n0 (fun i ->
                                 f (dni n0 (lastelement n0) i)))))
                           (weqstnsum_invmap n0 (fun i ->
                             f (dni n0 (lastelement n0) i))) (pr1weq idweq)
                           (pr1weq idweq)
                           (weqstnsum1_prelim_eq' n0 (fun i ->
                             f (dni n0 (lastelement n0) i)))
                           (homotrefl (pr1weq idweq)) c))
                      (homotweqinv (fun c ->
                        invmap (weqoverdnicoprod n0)
                          (coprodf
                            (weqstnsum_invmap n0 (fun i ->
                              f (dni n0 (lastelement n0) i))) (pr1weq idweq)
                            c))
                        (weqfromcoprodofstn
                          (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                          (f (lastelement n0))) (weqstnsum_invmap (S n0) f)
                        (fun c ->
                        match c with
                        | Coq_ii1 a ->
                          internal_paths_rew_r
                            (weqstnsum_invmap (S n0) f
                              (weqfromcoprodofstn_map
                                (stnsum n0 (fun x ->
                                  f (dni n0 (lastelement n0) x)))
                                (f (lastelement n0)) (Coq_ii1 a)))
                            (total2_base_map (dni n0 (lastelement n0))
                              (weqstnsum_invmap n0
                                (funcomp (dni n0 (lastelement n0)) f) a))
                            Coq_paths_refl (weqstnsum_invmap_step1 n0 f a)
                        | Coq_ii2 b ->
                          internal_paths_rew_r
                            (weqstnsum_invmap (S n0) f
                              (weqfromcoprodofstn_map
                                (stnsum n0 (fun x ->
                                  f (dni n0 (lastelement n0) x)))
                                (f (lastelement n0)) (Coq_ii2 b))) { pr1 =
                            (lastelement n0); pr2 = b } Coq_paths_refl
                            (weqstnsum_invmap_step2 n0 f b)) k))
                    (pr1_invweq
                      (weqfromcoprodofstn
                        (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                        (f (lastelement n0)))))
                  (pr1_invweq
                    (weqcoprodf1
                      (weqstnsum1_prelim n0 (fun i ->
                        f (dni n0 (lastelement n0) i))))))
                (pr1_invweq (weqoverdnicoprod n0)))
              (weqcomp_to_funcomp_app
                (pr1weq
                  (invweq
                    (weqfromcoprodofstn
                      (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                      (f (lastelement n0)))) k)
                (invweq
                  (weqcoprodf1
                    (weqstnsum1_prelim n0 (fun i ->
                      f (dni n0 (lastelement n0) i)))))
                (invweq (weqoverdnicoprod n0))))
            (weqcomp_to_funcomp_app k
              (invweq
                (weqfromcoprodofstn
                  (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                  (f (lastelement n0))))
              (weqcomp
                (invweq
                  (weqcoprodf1
                    (weqstnsum1_prelim n0 (fun i ->
                      f (dni n0 (lastelement n0) i)))))
                (invweq (weqoverdnicoprod n0)))))
          (invweqcomp (weqoverdnicoprod n0)
            (weqcoprodf1
              (weqstnsum1_prelim n0 (fun i -> f (dni n0 (lastelement n0) i))))))
        (invweqcomp
          (weqcomp (weqoverdnicoprod n0)
            (weqcoprodf1
              (weqstnsum1_prelim n0 (fun i -> f (dni n0 (lastelement n0) i)))))
          (weqfromcoprodofstn
            (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
            (f (lastelement n0))))) (weqstnsum1_step n0 f)

(** val weqstnsum1 : nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq **)

let weqstnsum1 n f =
  remakeweqboth (weqstnsum1_prelim n f) (weqstnsum_map n f)
    (weqstnsum_invmap n f) (weqstnsum1_prelim_eq n f)
    (weqstnsum1_prelim_eq' n f)

(** val weqstnsum1_eq' :
    nat -> (stn -> nat) -> (stn -> (stn, stn) total2) paths **)

let weqstnsum1_eq' _ _ =
  Coq_paths_refl

(** val weqstnsum :
    nat -> (stn -> nat) -> (stn -> (stn, 'a1) weq) -> ((stn, 'a1) total2,
    stn) weq **)

let weqstnsum n f w =
  weqcomp (invweq (weqfibtototal w)) (weqstnsum1 n f)

(** val inverse_lexicalEnumeration :
    nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq **)

let inverse_lexicalEnumeration =
  weqstnsum1

(** val ischoicebasestn : nat -> hProptoType **)

let rec ischoicebasestn = function
| O -> ischoicebaseempty2 negstn0
| S n0 ->
  ischoicebaseweqf (weqdnicoprod n0 (lastelement n0))
    (ischoicebasecoprod (ischoicebasestn n0) ischoicebaseunit)

(** val concatenate' :
    nat -> nat -> (stn -> 'a1) -> (stn -> 'a1) -> stn -> 'a1 **)

let concatenate' m n f g i =
  let c = weqfromcoprodofstn_invmap m n i in
  (match c with
   | Coq_ii1 a -> f a
   | Coq_ii2 b -> g b)

(** val flatten' :
    nat -> (stn -> nat) -> (stn -> stn -> 'a1) -> stn -> 'a1 **)

let flatten' n m g =
  funcomp (invmap (weqstnsum1 n m)) (uncurry g)

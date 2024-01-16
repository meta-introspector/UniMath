open DecidablePropositions
open NaturalNumbers
open NegativePropositions
open PartA
open PartB
open PartC
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

(** val stn_eq : nat -> stn -> stn -> nat paths -> stn paths **)

let stn_eq n i i' h =
  subtypePath (fun x -> isasetbool (natgtb n x) Coq_true) i i' h

(** val isinclstntonat : nat -> (stn, nat) isincl **)

let isinclstntonat n y =
  isinclpr1 (fun x -> (natlth x n).pr2) y

(** val stntonat_incl : nat -> (stn, nat) incl **)

let stntonat_incl n =
  make_incl (stntonat n) (isinclstntonat n)

(** val isdecinclstntonat : nat -> (stn, nat) isdecincl **)

let isdecinclstntonat n y =
  isdecinclpr1 (fun x -> isdecpropif (natlth x n).pr2 (isdecrelnatgth n x)) y

(** val neghfiberstntonat :
    nat -> nat -> hProptoType -> (stn, nat) hfiber neg **)

let neghfiberstntonat n m is h =
  let j = h.pr1 in
  let e = h.pr2 in
  let j0 = j.pr1 in
  let is' = j.pr2 in
  let is'0 = internal_paths_rew j0 is' m e in natgehtonegnatlth m n is is'0

(** val iscontrhfiberstntonat :
    nat -> nat -> hProptoType -> (stn, nat) hfiber iscontr **)

let iscontrhfiberstntonat n m is =
  iscontrhfiberofincl (stntonat n) (isinclstntonat n) (make_stn n m is)

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

(** val stnneq_iff_nopath :
    nat -> stn -> stn -> (stn paths neg, hProptoType) logeq **)

let stnneq_iff_nopath n i j =
  negProp_to_iff (stnneq n i j)

(** val stnneq_to_nopath :
    nat -> stn -> stn -> hProptoType -> stn paths neg **)

let stnneq_to_nopath n i j =
  (stn_ne_iff_neq n i j).pr2

(** val isdeceqstn : nat -> stn isdeceq **)

let isdeceqstn =
  isisolatedinstn

(** val stn_eq_or_neq :
    nat -> stn -> stn -> (stn paths, hProptoType) coprod **)

let stn_eq_or_neq n i j =
  let c = nat_eq_or_neq (stntonat n i) (stntonat n j) in
  (match c with
   | Coq_ii1 a -> Coq_ii1 (subtypePath_prop (fun x -> natlth x n) i j a)
   | Coq_ii2 b -> Coq_ii2 b)

(** val weqisolatedstntostn : nat -> (stn isolated, stn) weq **)

let weqisolatedstntostn n =
  weqpr1 (fun x -> iscontraprop1 (isapropisisolated x) (isdeceqstn n x))

(** val isasetstn : nat -> stn isaset **)

let isasetstn n x =
  isasetifdeceq (isdeceqstn n) x

(** val stnset : nat -> hSet **)

let stnset n =
  make_hSet (isasetstn n)

(** val stn_to_nat : nat -> pr1hSet -> pr1hSet **)

let stn_to_nat _ =
  Obj.magic (fun t -> t.pr1)

(** val stnposet : nat -> coq_Poset **)

let stnposet n =
  { pr1 = { pr1 = __; pr2 = (Obj.magic isasetstn n) }; pr2 = { pr1 =
    (fun i j ->
    coq_DecidableProposition_to_hProp
      (natleh_DecidableProposition (stntonat n (Obj.magic i))
        (stntonat n (Obj.magic j)))); pr2 = { pr1 = { pr1 = (fun i j k ->
    istransnatleh (stntonat n (Obj.magic i)) (stntonat n (Obj.magic j))
      (stntonat n (Obj.magic k))); pr2 = (fun i ->
    isreflnatleh (stntonat n (Obj.magic i))) }; pr2 = (fun i j r s ->
    invmaponpathsincl (Obj.magic stntonat n) (isinclstntonat n) i j
      (isantisymmnatleh (stntonat n (Obj.magic i)) (stntonat n (Obj.magic j))
        r s)) } } }

(** val lastelement : nat -> stn **)

let lastelement n =
  { pr1 = n; pr2 = (natgthsnn n) }

(** val lastelement_ge : nat -> stn -> hProptoType **)

let lastelement_ge n i =
  natlthsntoleh (stntonat (S n) i) (stntonat (S n) (lastelement n))
    (stnlt (S n) i)

(** val firstelement : nat -> stn **)

let firstelement n =
  { pr1 = O; pr2 = (natgthsn0 n) }

(** val firstelement_le : nat -> stn -> hProptoType **)

let firstelement_le _ _ =
  Obj.magic Coq_paths_refl

(** val firstValue : nat -> (stn -> 'a1) -> 'a1 **)

let firstValue n x =
  x (firstelement n)

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

(** val stnmtostnn : nat -> nat -> hProptoType -> stn -> stn **)

let stnmtostnn m n isnatleh x =
  let i = x.pr1 in
  let is = x.pr2 in make_stn n i (natlthlehtrans i m n is isnatleh)

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

(** val compute_pr1_dni_first : nat -> stn -> nat paths **)

let compute_pr1_dni_first _ _ =
  Coq_paths_refl

(** val dni_last : nat -> stn -> nat paths **)

let dni_last n i =
  let i0 = i.pr1 in
  let c = natlthorgeh i0 n in
  (match c with
   | Coq_ii1 _ -> Coq_paths_refl
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val dni_first : nat -> stn -> nat paths **)

let dni_first _ _ =
  Coq_paths_refl

(** val dni_firstelement : nat -> stn -> stn **)

let dni_firstelement _ h =
  { pr1 = (S h.pr1); pr2 = h.pr2 }

(** val replace_dni_first : nat -> (stn -> stn) paths **)

let replace_dni_first n =
  Obj.magic funextfun (dni n (firstelement n)) (dni_firstelement n) (fun i ->
    Obj.magic subtypePath_prop (fun x -> natlth x (S n))
      (dni n (firstelement n) (Obj.magic i))
      (dni_firstelement n (Obj.magic i))
      (compute_pr1_dni_first n (Obj.magic i)))

(** val dni_lastelement : nat -> stn -> stn **)

let dni_lastelement n h =
  { pr1 = h.pr1; pr2 = (natlthtolths h.pr1 n h.pr2) }

(** val replace_dni_last : nat -> (stn -> stn) paths **)

let replace_dni_last n =
  Obj.magic funextfun (dni n (lastelement n)) (dni_lastelement n) (fun i ->
    Obj.magic subtypePath_prop (fun x -> natlth x (S n))
      (dni n (lastelement n) (Obj.magic i)) (dni_lastelement n (Obj.magic i))
      (compute_pr1_dni_last n (Obj.magic i)))

(** val dni_lastelement_ord :
    nat -> stn -> stn -> hProptoType -> hProptoType **)

let dni_lastelement_ord _ _ _ e =
  e

(** val pr1_dni_lastelement : nat -> stn -> nat paths **)

let pr1_dni_lastelement _ _ =
  Coq_paths_refl

(** val dni_last_lt : nat -> stn -> hProptoType **)

let dni_last_lt n j =
  let j0 = j.pr1 in
  let j1 = j.pr2 in
  let c = natlthorgeh j0 n in
  (match c with
   | Coq_ii1 _ -> j1
   | Coq_ii2 b -> fromempty (natlthtonegnatgeh j0 n j1 b))

(** val dnicommsq : nat -> stn -> (nat, stn, nat, stn) commsqstr **)

let dnicommsq _ _ _ =
  Coq_paths_refl

(** val dnihfsq : nat -> stn -> (nat, stn, nat, stn) hfsqstr **)

let dnihfsq n i =
  ishfsqweqhfibersgtof' (di (stntonat (S n) i)) (stntonat (S n)) (stntonat n)
    (dni n i) (dnicommsq n i) (fun x ->
    let c = natlthorgeh x n in
    (match c with
     | Coq_ii1 h ->
       let is1 = iscontrhfiberstntonat n x h in
       let is2 =
         iscontrhfiberstntonat (S n) (di (stntonat (S n) i) x)
           (natlehlthtrans (di (stntonat (S n) i) x) (S x) (S n)
             (natlehdinsn (stntonat (S n) i) x) h)
       in
       isweqcontrcontr
         (hfibersgtof' (di (stntonat (S n) i)) (stntonat (S n)) (stntonat n)
           (dni n i) (dnicommsq n i) x) is1 is2
     | Coq_ii2 h ->
       let is1 =
         neghfiberstntonat (S n) (di (stntonat (S n) i) x)
           (let c0 = natlthorgeh x (stntonat (S n) i) in
            match c0 with
            | Coq_ii1 _ ->
              let c1 = natgehchoice2 x n h in
              (match c1 with
               | Coq_ii1 h0 -> h0
               | Coq_ii2 _ -> assert false (* absurd case *))
            | Coq_ii2 _ -> h)
       in
       isweqtoempty2
         (hfibersgtof' (di (stntonat (S n) i)) (stntonat (S n)) (stntonat n)
           (dni n i) (dnicommsq n i) x) is1))

(** val dni_neq_i : nat -> stn -> stn -> hProptoType **)

let dni_neq_i n i j =
  di_neq_i (stntonat (S n) i) (stntonat n j)

(** val weqhfiberdnihfiberdi :
    nat -> stn -> stn -> ((stn, stn) hfiber, (nat, nat) hfiber) weq **)

let weqhfiberdnihfiberdi n i j =
  weqhfibersg'tof (di (stntonat (S n) i)) (stntonat (S n)) (stntonat n)
    (dni n i) (dnihfsq n i) j

(** val neghfiberdni : nat -> stn -> (stn, stn) hfiber neg **)

let neghfiberdni n i =
  negf (pr1weq (weqhfiberdnihfiberdi n i i)) (neghfiberdi (stntonat (S n) i))

(** val iscontrhfiberdni :
    nat -> stn -> stn -> hProptoType -> (stn, stn) hfiber iscontr **)

let iscontrhfiberdni n i j ne =
  iscontrweqb (weqhfiberdnihfiberdi n i j)
    (iscontrhfiberdi (stntonat (S n) i) (stntonat (S n) j) ne)

(** val isdecincldni : nat -> stn -> (stn, stn) isdecincl **)

let isdecincldni n i j =
  let c = stn_eq_or_neq (S n) i j in
  (match c with
   | Coq_ii1 _ -> isdecpropfromneg (neghfiberdni n i)
   | Coq_ii2 b -> isdecpropfromiscontr (iscontrhfiberdni n i j b))

(** val isincldni : nat -> stn -> (stn, stn) isincl **)

let isincldni n i =
  isdecincltoisincl (dni n i) (isdecincldni n i)

(** val sni : nat -> stn -> stn -> stn **)

let sni n i j =
  { pr1 = (si (stntonat n i) (stntonat (S n) j)); pr2 =
    (let c = natlthorgeh (stntonat n i) (stntonat (S n) j) in
     match c with
     | Coq_ii1 _ ->
       let j0 = j.pr1 in
       let j1 = j.pr2 in
       (match j0 with
        | O -> assert false (* absurd case *)
        | S n0 ->
          internal_paths_rew_r (add (S O) n0) (add n0 (S O))
            (internal_paths_rew_r (sub (add n0 (S O)) (S O)) n0 j1
              (plusminusnmm n0 (S O))) (natpluscomm (S O) n0))
     | Coq_ii2 b ->
       let i0 = i.pr1 in
       let i1 = i.pr2 in
       natlehlthtrans (stntonat (S n) j) (stntonat n { pr1 = i0; pr2 = i1 })
         n b i1) }

type stn_compl = stn compl_ne

(** val dnitocompl : nat -> stn -> stn -> stn_compl **)

let dnitocompl n i j =
  { pr1 = (dni n i j); pr2 = (dni_neq_i n i j) }

(** val isweqdnitocompl : nat -> stn -> (stn, stn_compl) isweq **)

let isweqdnitocompl n i jni =
  let w =
    samehfibers (dnitocompl n i) (pr1compl_ne i (stnneq (S n) i))
      (isinclpr1compl_ne i (stnneq (S n) i)) jni
  in
  iscontrweqb w
    (iscontrhfiberdni n i (pr1compl_ne i (stnneq (S n) i) jni) jni.pr2)

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

(** val weqdnicompl_compute : nat -> stn -> stn -> stn paths **)

let weqdnicompl_compute n j i =
  subtypePath_prop (fun x -> natlth x (S n)) (pr1weq (weqdnicompl n j) i).pr1
    (dni n j i) Coq_paths_refl

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

(** val weqoverdnicoprod_eq1 :
    nat -> stn -> 'a1 -> (stn, 'a1) total2 paths **)

let weqoverdnicoprod_eq1 _ _ _ =
  Coq_paths_refl

(** val weqoverdnicoprod_eq1' :
    nat -> (stn, 'a1) total2 -> (stn, 'a1) total2 paths **)

let weqoverdnicoprod_eq1' _ _ =
  Coq_paths_refl

(** val weqoverdnicoprod_eq2 : nat -> 'a1 -> (stn, 'a1) total2 paths **)

let weqoverdnicoprod_eq2 _ _ =
  Coq_paths_refl

(** val weqdnicoprod_invmap : nat -> stn -> stn -> (stn, coq_unit) coprod **)

let weqdnicoprod_invmap n j i =
  let d = isdeceqstn (S n) i j in
  (match d with
   | Coq_ii1 _ -> Coq_ii2 Coq_tt
   | Coq_ii2 _ ->
     Coq_ii1
       (let i0 = i.pr1 in
        let i1 = i.pr2 in
        let j0 = j.pr1 in
        let j1 = j.pr2 in
        let c = (decidabilityProperty (natlth_DecidableProposition i0 j0)).pr1
        in
        (match c with
         | Coq_ii1 a -> { pr1 = i0; pr2 = (natltltSlt i0 j0 n a j1) }
         | Coq_ii2 b ->
           { pr1 = (sub i0 (S O)); pr2 =
             (let c0 = natlehchoice j0 i0 (negnatgthtoleh j0 i0 b) in
              match c0 with
              | Coq_ii1 a ->
                let c1 = natlehchoice4 i0 n i1 in
                (match c1 with
                 | Coq_ii1 a0 ->
                   natlehlthtrans (sub i0 (S O)) i0 n (natminuslehn i0 (S O))
                     a0
                 | Coq_ii2 _ ->
                   natminuslthn i0 (S O)
                     (natlehlthtrans O j0 i0 (natleh0n j0) a) (natlthnsn O))
              | Coq_ii2 _ -> assert false (* absurd case *)) })))

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

(** val iscontrstn1 : stn iscontr **)

let iscontrstn1 =
  iscontrifweqtounit weqstn1tounit

(** val isconnectedstn1 : stn -> stn -> stn paths **)

let isconnectedstn1 i1 i2 =
  invmaponpathsweq weqstn1tounit i1 i2
    (isProofIrrelevantUnit (pr1weq weqstn1tounit i1)
      (pr1weq weqstn1tounit i2))

(** val isinclfromstn1 : (stn -> 'a1) -> 'a1 isaset -> (stn, 'a1) isincl **)

let isinclfromstn1 f is =
  isinclbetweensets f (isasetstn (S O)) is (fun x x' _ ->
    invmaponpathsweq weqstn1tounit x x' Coq_paths_refl)

(** val weqstn2tobool : (stn, bool) weq **)

let weqstn2tobool =
  let f = fun j ->
    match isdeceqnat (stntonat (S (S O)) j) O with
    | Coq_ii1 _ -> Coq_false
    | Coq_ii2 _ -> Coq_true
  in
  let g = fun b ->
    match b with
    | Coq_true -> make_stn (S (S O)) (S O) (Obj.magic Coq_paths_refl)
    | Coq_false -> make_stn (S (S O)) O (Obj.magic Coq_paths_refl)
  in
  { pr1 = f; pr2 =
  (let egf = fun j ->
     let d = isdeceqnat (stntonat (S (S O)) j) O in
     (match d with
      | Coq_ii1 p ->
        invmaponpathsincl (stntonat (S (S O))) (isinclstntonat (S (S O)))
          (g Coq_false) j
          (internal_paths_rew_r (stntonat (S (S O)) j) O Coq_paths_refl p)
      | Coq_ii2 _ ->
        invmaponpathsincl (stntonat (S (S O))) (isinclstntonat (S (S O)))
          (g Coq_true) j
          (let j0 = j.pr1 in
           let l = j.pr2 in
           let l' = natlthtolehsn j0 (S (S O)) l in
           let c = natlehchoice (S j0) (S (S O)) l' in
           (match c with
            | Coq_ii1 _ -> assert false (* absurd case *)
            | Coq_ii2 p -> pathsinv0 j0 (S O) (invmaponpathsS j0 (S O) p))))
   in
   let efg = fun b ->
     match b with
     | Coq_true -> Coq_paths_refl
     | Coq_false -> Coq_paths_refl
   in
   isweq_iso f g egf efg) }

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

(** val pr1_eqweqmap_stn : nat -> nat -> nat paths -> stn -> nat paths **)

let pr1_eqweqmap_stn _ _ _ _ =
  Coq_paths_refl

(** val coprod_stn_assoc :
    nat -> nat -> nat -> (((stn, stn) coprod, stn) coprod, stn) homot **)

let coprod_stn_assoc l m n abc =
  invmaponpathsincl (fun t -> t.pr1) (isinclstntonat (add l (add m n)))
    (pr1weq
      (eqweqmap
        (maponpaths (Obj.magic __) (add (add l m) n) (add l (add m n))
          (natplusassoc l m n)))
      (weqfromcoprodofstn_map (add l m) n
        (coprodf (weqfromcoprodofstn_map l m) (fun x -> x) abc)))
    (weqfromcoprodofstn_map l (add m n)
      (coprodf (fun x -> x) (weqfromcoprodofstn_map m n) (coprodasstor abc)))
    (internal_paths_rew_r
      (pr1weq
        (eqweqmap
          (maponpaths (Obj.magic __) (add (add l m) n) (add l (add m n))
            (natplusassoc l m n)))
        (weqfromcoprodofstn_map (add l m) n
          (coprodf (weqfromcoprodofstn_map l m) (fun x -> x) abc))).pr1
      (weqfromcoprodofstn_map (add l m) n
        (coprodf (weqfromcoprodofstn_map l m) (fun x -> x) abc)).pr1
      (match abc with
       | Coq_ii1 _ -> Coq_paths_refl
       | Coq_ii2 b -> natplusassoc l m b.pr1)
      (pr1_eqweqmap_stn (add (add l m) n) (add l (add m n))
        (natplusassoc l m n)
        (weqfromcoprodofstn_map (add l m) n
          (coprodf (weqfromcoprodofstn_map l m) (fun x -> x) abc))))

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

(** val stnsum_le :
    nat -> (stn -> nat) -> (stn -> nat) -> (stn -> hProptoType) -> hProptoType **)

let rec stnsum_le n f g le =
  match n with
  | O -> Obj.magic Coq_paths_refl
  | S n0 ->
    natlehandplus
      (let rec f0 n1 f1 =
         match n1 with
         | O -> O
         | S n2 ->
           add (f0 n2 (fun i -> f1 (dni n2 (lastelement n2) i)))
             (f1 (lastelement n2))
       in f0 n0 (fun i -> f (dni n0 (lastelement n0) i)))
      (let rec f0 n1 f1 =
         match n1 with
         | O -> O
         | S n2 ->
           add (f0 n2 (fun i -> f1 (dni n2 (lastelement n2) i)))
             (f1 (lastelement n2))
       in f0 n0 (fun i -> g (dni n0 (lastelement n0) i)))
      (f (lastelement n0)) (g (lastelement n0))
      (stnsum_le n0 (fun i -> f (dni n0 (lastelement n0) i)) (fun i ->
        g (dni n0 (lastelement n0) i)) (fun i ->
        le (dni n0 (lastelement n0) i))) (le (lastelement n0))

(** val transport_stn : nat -> nat -> nat paths -> stn -> stn paths **)

let transport_stn m _ _ i =
  subtypePath_prop (fun x -> natlth x m) (transportf m m Coq_paths_refl i)
    (make_stn m i.pr1 (transportf m m Coq_paths_refl i.pr2)) Coq_paths_refl

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

(** val stnsum_left_le : nat -> nat -> (stn -> nat) -> hProptoType **)

let stnsum_left_le m n f =
  internal_paths_rew_r (stnsum (add m n) f)
    (add (stnsum m (funcomp (stn_left m n) f))
      (stnsum n (funcomp (stn_right m n) f)))
    (natlehnplusnm (stnsum m (funcomp (stn_left m n) f))
      (stnsum n (funcomp (stn_right m n) f))) (stnsum_left_right m n f)

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

(** val stnsum_dni : nat -> (stn -> nat) -> stn -> nat paths **)

let stnsum_dni n f j =
  let j0 = j.pr1 in
  let j1 = j.pr2 in
  let e2 =
    internal_paths_rew_r (add j0 (sub n j0)) (add (sub n j0) j0)
      (minusplusnmm n j0 (natlthsntoleh j0 n j1)) (natpluscomm j0 (sub n j0))
  in
  let e = maponpaths (fun x -> S x) (add j0 (sub n j0)) n e2 in
  pathscomp0 (stnsum (S n) f)
    (stnsum (add (S j0) (sub n j0)) (fun i ->
      f (transportf (add (S j0) (sub n j0)) (S n) e i)))
    (add (stnsum n (funcomp (dni n { pr1 = j0; pr2 = j1 }) f))
      (f { pr1 = j0; pr2 = j1 }))
    (transport_stnsum (add (S j0) (sub n j0)) (S n) e f)
    (internal_paths_rew_r
      (stnsum (add (S j0) (sub n j0)) (fun i ->
        f (transportf (add (S j0) (sub n j0)) (S n) e i)))
      (add
        (stnsum (S j0)
          (funcomp (stn_left (S j0) (sub n j0)) (fun i ->
            f (transportf (add (S j0) (sub n j0)) (S n) e i))))
        (stnsum (sub n j0)
          (funcomp (stn_right (S j0) (sub n j0)) (fun i ->
            f (transportf (add (S j0) (sub n j0)) (S n) e i)))))
      (pathsinv0
        (add (stnsum n (fun x -> f (dni n { pr1 = j0; pr2 = j1 } x)))
          (f { pr1 = j0; pr2 = j1 }))
        (add
          (stnsum (S j0) (fun x ->
            f
              (transportf (add (S j0) (sub n j0)) (S n) e
                (stn_left (S j0) (sub n j0) x))))
          (stnsum (sub n j0) (fun x ->
            f
              (transportf (add (S j0) (sub n j0)) (S n) e
                (stn_right (S j0) (sub n j0) x)))))
        (internal_paths_rew_r
          (stnsum n (fun x -> f (dni n { pr1 = j0; pr2 = j1 } x)))
          (stnsum (add j0 (sub n j0)) (fun i ->
            f
              (dni n { pr1 = j0; pr2 = j1 }
                (transportf (add j0 (sub n j0)) n e2 i))))
          (internal_paths_rew_r
            (stnsum (add j0 (sub n j0)) (fun i ->
              f
                (dni n { pr1 = j0; pr2 = j1 }
                  (transportf (add j0 (sub n j0)) n e2 i))))
            (add
              (stnsum j0
                (funcomp (stn_left j0 (sub n j0)) (fun i ->
                  f
                    (dni n { pr1 = j0; pr2 = j1 }
                      (transportf (add j0 (sub n j0)) n e2 i)))))
              (stnsum (sub n j0)
                (funcomp (stn_right j0 (sub n j0)) (fun i ->
                  f
                    (dni n { pr1 = j0; pr2 = j1 }
                      (transportf (add j0 (sub n j0)) n e2 i))))))
            (internal_paths_rew_r
              (stnsum (S j0) (fun x ->
                f
                  (transportf (add (S j0) (sub n j0)) (S n) e
                    (stn_left (S j0) (sub n j0) x))))
              (add
                (stnsum j0
                  (funcomp (dni j0 (lastelement j0)) (fun x ->
                    f
                      (transportf (add (S j0) (sub n j0)) (S n) e
                        (stn_left (S j0) (sub n j0) x)))))
                (f
                  (transportf (add (S j0) (sub n j0)) (S n) e
                    (stn_left (S j0) (sub n j0) (lastelement j0)))))
              (pathsinv0
                (add
                  (add
                    (stnsum j0 (fun x ->
                      f
                        (transportf (add (S j0) (sub n j0)) (S n) e
                          (stn_left (S j0) (sub n j0)
                            (dni j0 (lastelement j0) x)))))
                    (f
                      (transportf (add (S j0) (sub n j0)) (S n) e
                        (stn_left (S j0) (sub n j0) (lastelement j0)))))
                  (stnsum (sub n j0) (fun x ->
                    f
                      (transportf (add (S j0) (sub n j0)) (S n) e
                        (stn_right (S j0) (sub n j0) x)))))
                (add
                  (add
                    (stnsum j0 (fun x ->
                      f
                        (dni n { pr1 = j0; pr2 = j1 }
                          (transportf (add j0 (sub n j0)) n e2
                            (stn_left j0 (sub n j0) x)))))
                    (stnsum (sub n j0) (fun x ->
                      f
                        (dni n { pr1 = j0; pr2 = j1 }
                          (transportf (add j0 (sub n j0)) n e2
                            (stn_right j0 (sub n j0) x))))))
                  (f { pr1 = j0; pr2 = j1 }))
                (internal_paths_rew_r
                  (add
                    (add
                      (stnsum j0 (fun x ->
                        f
                          (transportf (add (S j0) (sub n j0)) (S n) e
                            (stn_left (S j0) (sub n j0)
                              (dni j0 (lastelement j0) x)))))
                      (f
                        (transportf (add (S j0) (sub n j0)) (S n) e
                          (stn_left (S j0) (sub n j0) (lastelement j0)))))
                    (stnsum (sub n j0) (fun x ->
                      f
                        (transportf (add (S j0) (sub n j0)) (S n) e
                          (stn_right (S j0) (sub n j0) x)))))
                  (add
                    (stnsum j0 (fun x ->
                      f
                        (transportf (add (S j0) (sub n j0)) (S n) e
                          (stn_left (S j0) (sub n j0)
                            (dni j0 (lastelement j0) x)))))
                    (add
                      (f
                        (transportf (add (S j0) (sub n j0)) (S n) e
                          (stn_left (S j0) (sub n j0) (lastelement j0))))
                      (stnsum (sub n j0) (fun x ->
                        f
                          (transportf (add (S j0) (sub n j0)) (S n) e
                            (stn_right (S j0) (sub n j0) x))))))
                  (internal_paths_rew_r
                    (add
                      (f
                        (transportf (add (S j0) (sub n j0)) (S n) e
                          (stn_left (S j0) (sub n j0) (lastelement j0))))
                      (stnsum (sub n j0) (fun x ->
                        f
                          (transportf (add (S j0) (sub n j0)) (S n) e
                            (stn_right (S j0) (sub n j0) x)))))
                    (add
                      (stnsum (sub n j0) (fun x ->
                        f
                          (transportf (add (S j0) (sub n j0)) (S n) e
                            (stn_right (S j0) (sub n j0) x))))
                      (f
                        (transportf (add (S j0) (sub n j0)) (S n) e
                          (stn_left (S j0) (sub n j0) (lastelement j0)))))
                    (internal_paths_rew
                      (add
                        (add
                          (stnsum j0 (fun x ->
                            f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_left (S j0) (sub n j0)
                                  (dni j0 (lastelement j0) x)))))
                          (stnsum (sub n j0) (fun x ->
                            f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_right (S j0) (sub n j0) x)))))
                        (f
                          (transportf (add (S j0) (sub n j0)) (S n) e
                            (stn_left (S j0) (sub n j0) (lastelement j0)))))
                      (map_on_two_paths add
                        (add
                          (stnsum j0 (fun x ->
                            f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_left (S j0) (sub n j0)
                                  (dni j0 (lastelement j0) x)))))
                          (stnsum (sub n j0) (fun x ->
                            f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_right (S j0) (sub n j0) x)))))
                        (add
                          (stnsum j0 (fun x ->
                            f
                              (dni n { pr1 = j0; pr2 = j1 }
                                (transportf (add j0 (sub n j0)) n e2
                                  (stn_left j0 (sub n j0) x)))))
                          (stnsum (sub n j0) (fun x ->
                            f
                              (dni n { pr1 = j0; pr2 = j1 }
                                (transportf (add j0 (sub n j0)) n e2
                                  (stn_right j0 (sub n j0) x))))))
                        (f
                          (transportf (add (S j0) (sub n j0)) (S n) e
                            (stn_left (S j0) (sub n j0) (lastelement j0))))
                        (f { pr1 = j0; pr2 = j1 })
                        (map_on_two_paths add
                          (stnsum j0 (fun x ->
                            f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_left (S j0) (sub n j0)
                                  (dni j0 (lastelement j0) x)))))
                          (stnsum j0 (fun x ->
                            f
                              (dni n { pr1 = j0; pr2 = j1 }
                                (transportf (add j0 (sub n j0)) n e2
                                  (stn_left j0 (sub n j0) x)))))
                          (stnsum (sub n j0) (fun x ->
                            f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_right (S j0) (sub n j0) x))))
                          (stnsum (sub n j0) (fun x ->
                            f
                              (dni n { pr1 = j0; pr2 = j1 }
                                (transportf (add j0 (sub n j0)) n e2
                                  (stn_right j0 (sub n j0) x)))))
                          (stnsum_eq j0 (fun x ->
                            f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_left (S j0) (sub n j0)
                                  (dni j0 (lastelement j0) x)))) (fun x ->
                            f
                              (dni n { pr1 = j0; pr2 = j1 }
                                (transportf (add j0 (sub n j0)) n e2
                                  (stn_left j0 (sub n j0) x)))) (fun i ->
                            let i0 = i.pr1 in
                            let i1 = i.pr2 in
                            maponpaths f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_left (S j0) (sub n j0)
                                  (dni j0 (lastelement j0) { pr1 = i0; pr2 =
                                    i1 })))
                              (dni n { pr1 = j0; pr2 = j1 }
                                (transportf (add j0 (sub n j0)) n e2
                                  (stn_left j0 (sub n j0) { pr1 = i0; pr2 =
                                    i1 })))
                              (subtypePath_prop (fun x -> natlth x (S n))
                                (transportf (add (S j0) (sub n j0)) (S n) e
                                  (stn_left (S j0) (sub n j0)
                                    (dni j0 (lastelement j0) { pr1 = i0;
                                      pr2 = i1 })))
                                (dni n { pr1 = j0; pr2 = j1 }
                                  (transportf (add j0 (sub n j0)) n e2
                                    (stn_left j0 (sub n j0) { pr1 = i0; pr2 =
                                      i1 })))
                                (internal_paths_rew_r
                                  (transportf (add (S j0) (sub n j0))
                                    (add (S j0) (sub n j0)) Coq_paths_refl
                                    (stn_left (S j0) (sub n j0)
                                      (dni j0 (lastelement j0) { pr1 = i0;
                                        pr2 = i1 })))
                                  (stn_left (S j0) (sub n j0)
                                    (dni j0 (lastelement j0) { pr1 = i0;
                                      pr2 = i1 }))
                                  (internal_paths_rew_r
                                    (stn_left (S j0) (sub n j0)
                                      (dni j0 (lastelement j0) { pr1 = i0;
                                        pr2 = i1 })).pr1
                                    (stntonat (S j0)
                                      (dni j0 (lastelement j0) { pr1 = i0;
                                        pr2 = i1 }))
                                    (let c = natlthorgeh i0 j0 in
                                     match c with
                                     | Coq_ii1 _ ->
                                       internal_paths_rew_r
                                         (transportf (add j0 (sub n j0)) n e2
                                           (stn_left j0 (sub n j0) { pr1 =
                                             i0; pr2 = i1 }))
                                         (make_stn n
                                           (stn_left j0 (sub n j0) { pr1 =
                                             i0; pr2 = i1 }).pr1
                                           (transportf (add j0 (sub n j0)) n
                                             e2
                                             (stn_left j0 (sub n j0) { pr1 =
                                               i0; pr2 = i1 }).pr2))
                                         (let c0 = natlthorgeh i0 j0 in
                                          match c0 with
                                          | Coq_ii1 _ -> Coq_paths_refl
                                          | Coq_ii2 _ ->
                                            assert false (* absurd case *))
                                         (transport_stn (add j0 (sub n j0)) n
                                           e2
                                           (stn_left j0 (sub n j0) { pr1 =
                                             i0; pr2 = i1 }))
                                     | Coq_ii2 _ ->
                                       internal_paths_rew_r
                                         (transportf (add j0 (sub n j0)) n e2
                                           (stn_left j0 (sub n j0) { pr1 =
                                             i0; pr2 = i1 }))
                                         (make_stn n
                                           (stn_left j0 (sub n j0) { pr1 =
                                             i0; pr2 = i1 }).pr1
                                           (transportf (add j0 (sub n j0)) n
                                             e2
                                             (stn_left j0 (sub n j0) { pr1 =
                                               i0; pr2 = i1 }).pr2))
                                         (let c0 = natlthorgeh i0 j0 in
                                          match c0 with
                                          | Coq_ii1 _ ->
                                            assert false (* absurd case *)
                                          | Coq_ii2 _ -> Coq_paths_refl)
                                         (transport_stn (add j0 (sub n j0)) n
                                           e2
                                           (stn_left j0 (sub n j0) { pr1 =
                                             i0; pr2 = i1 })))
                                    (stn_left_compute (S j0) (sub n j0)
                                      (dni j0 (lastelement j0) { pr1 = i0;
                                        pr2 = i1 })))
                                  (idpath_transportf (add (S j0) (sub n j0))
                                    (stn_left (S j0) (sub n j0)
                                      (dni j0 (lastelement j0) { pr1 = i0;
                                        pr2 = i1 })))))))
                          (stnsum_eq (sub n j0) (fun x ->
                            f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_right (S j0) (sub n j0) x))) (fun x ->
                            f
                              (dni n { pr1 = j0; pr2 = j1 }
                                (transportf (add j0 (sub n j0)) n e2
                                  (stn_right j0 (sub n j0) x)))) (fun i ->
                            let i0 = i.pr1 in
                            let i1 = i.pr2 in
                            maponpaths f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_right (S j0) (sub n j0) { pr1 = i0;
                                  pr2 = i1 }))
                              (dni n { pr1 = j0; pr2 = j1 }
                                (transportf (add j0 (sub n j0)) n e2
                                  (stn_right j0 (sub n j0) { pr1 = i0; pr2 =
                                    i1 })))
                              (internal_paths_rew_r
                                (transportf (add (S j0) (sub n j0)) (S n) e
                                  { pr1 = (add (S j0) i0); pr2 =
                                  (natlthandplusl i0 (sub n j0) (S j0) i1) })
                                (make_stn (S n) (add (S j0) i0)
                                  (transportf (add (S j0) (sub n j0)) (S n) e
                                    (natlthandplusl i0 (sub n j0) (S j0) i1)))
                                (internal_paths_rew_r
                                  (transportf (add j0 (sub n j0)) n e2
                                    { pr1 = (add j0 i0); pr2 =
                                    (natlthandplusl i0 (sub n j0) j0 i1) })
                                  (make_stn n (add j0 i0)
                                    (transportf (add j0 (sub n j0)) n e2
                                      (natlthandplusl i0 (sub n j0) j0 i1)))
                                  (let c = natlthorgeh (add j0 i0) j0 in
                                   match c with
                                   | Coq_ii1 _ ->
                                     assert false (* absurd case *)
                                   | Coq_ii2 _ ->
                                     subtypePath_prop (fun x ->
                                       natlth x (S n))
                                       (make_stn (S n) (S (add j0 i0))
                                         (transportf (S (add j0 (sub n j0)))
                                           (S n) e
                                           (natlthandplusl i0 (sub n j0) j0
                                             i1))) { pr1 = (S (add j0 i0));
                                       pr2 =
                                       (transportf (add j0 (sub n j0)) n e2
                                         (natlthandplusl i0 (sub n j0) j0 i1)) }
                                       Coq_paths_refl)
                                  (transport_stn (add j0 (sub n j0)) n e2
                                    { pr1 = (add j0 i0); pr2 =
                                    (natlthandplusl i0 (sub n j0) j0 i1) }))
                                (transport_stn (add (S j0) (sub n j0)) (S n)
                                  e { pr1 = (add (S j0) i0); pr2 =
                                  (natlthandplusl i0 (sub n j0) (S j0) i1) })))))
                        (maponpaths f
                          (transportf (add (S j0) (sub n j0)) (S n) e
                            (stn_left (S j0) (sub n j0) (lastelement j0)))
                          { pr1 = j0; pr2 = j1 }
                          (internal_paths_rew_r
                            (transportf (add (S j0) (sub n j0)) (S n) e
                              (stn_left (S j0) (sub n j0) (lastelement j0)))
                            (make_stn (S n)
                              (stn_left (S j0) (sub n j0) (lastelement j0)).pr1
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_left (S j0) (sub n j0) (lastelement j0)).pr2))
                            (subtypePath_prop (fun x -> natlth x (S n))
                              (make_stn (S n) j0
                                (transportf (S (add j0 (sub n j0))) (S n) e
                                  (natlthlehtrans j0 (S j0) (S
                                    (add j0 (sub n j0))) (natgthsnn j0)
                                    (natlehnplusnm (S j0) (sub n j0)))))
                              { pr1 = j0; pr2 = j1 } Coq_paths_refl)
                            (transport_stn (add (S j0) (sub n j0)) (S n) e
                              (stn_left (S j0) (sub n j0) (lastelement j0))))))
                      (add
                        (stnsum j0 (fun x ->
                          f
                            (transportf (add (S j0) (sub n j0)) (S n) e
                              (stn_left (S j0) (sub n j0)
                                (dni j0 (lastelement j0) x)))))
                        (add
                          (stnsum (sub n j0) (fun x ->
                            f
                              (transportf (add (S j0) (sub n j0)) (S n) e
                                (stn_right (S j0) (sub n j0) x))))
                          (f
                            (transportf (add (S j0) (sub n j0)) (S n) e
                              (stn_left (S j0) (sub n j0) (lastelement j0))))))
                      (natplusassoc
                        (stnsum j0 (fun x ->
                          f
                            (transportf (add (S j0) (sub n j0)) (S n) e
                              (stn_left (S j0) (sub n j0)
                                (dni j0 (lastelement j0) x)))))
                        (stnsum (sub n j0) (fun x ->
                          f
                            (transportf (add (S j0) (sub n j0)) (S n) e
                              (stn_right (S j0) (sub n j0) x))))
                        (f
                          (transportf (add (S j0) (sub n j0)) (S n) e
                            (stn_left (S j0) (sub n j0) (lastelement j0))))))
                    (natpluscomm
                      (f
                        (transportf (add (S j0) (sub n j0)) (S n) e
                          (stn_left (S j0) (sub n j0) (lastelement j0))))
                      (stnsum (sub n j0) (fun x ->
                        f
                          (transportf (add (S j0) (sub n j0)) (S n) e
                            (stn_right (S j0) (sub n j0) x))))))
                  (natplusassoc
                    (stnsum j0 (fun x ->
                      f
                        (transportf (add (S j0) (sub n j0)) (S n) e
                          (stn_left (S j0) (sub n j0)
                            (dni j0 (lastelement j0) x)))))
                    (f
                      (transportf (add (S j0) (sub n j0)) (S n) e
                        (stn_left (S j0) (sub n j0) (lastelement j0))))
                    (stnsum (sub n j0) (fun x ->
                      f
                        (transportf (add (S j0) (sub n j0)) (S n) e
                          (stn_right (S j0) (sub n j0) x)))))))
              (stnsum_step j0 (fun x ->
                f
                  (transportf (add (S j0) (sub n j0)) (S n) e
                    (stn_left (S j0) (sub n j0) x)))))
            (stnsum_left_right j0 (sub n j0) (fun i ->
              f
                (dni n { pr1 = j0; pr2 = j1 }
                  (transportf (add j0 (sub n j0)) n e2 i)))))
          (transport_stnsum (add j0 (sub n j0)) n e2 (fun x ->
            f (dni n { pr1 = j0; pr2 = j1 } x)))))
      (stnsum_left_right (S j0) (sub n j0) (fun i ->
        f (transportf (add (S j0) (sub n j0)) (S n) e i))))

(** val stnsum_pos : nat -> (stn -> nat) -> stn -> hProptoType **)

let stnsum_pos n f j =
  let m = natlehlthtrans O (stntonat n j) n (natleh0n (stntonat n j)) j.pr2 in
  let l = natlthtolehsn O n m in
  let e =
    internal_paths_rew_r (add (S O) (sub n (S O))) (add (sub n (S O)) (S O))
      (pathsinv0 (add (sub n (S O)) (S O)) n (minusplusnmm n (S O) l))
      (natpluscomm (S O) (sub n (S O)))
  in
  internal_paths_rew_r (stnsum n f)
    (stnsum (S (sub n (S O))) (fun i ->
      f (transportf (S (sub n (S O))) n (pathsinv0 n (S (sub n (S O))) e) i)))
    (internal_paths_rew_r
      (stnsum (S (sub n (S O))) (fun i ->
        f (transportf (S (sub n (S O))) n (pathsinv0 n (S (sub n (S O))) e) i)))
      (add
        (stnsum (sub n (S O))
          (funcomp (dni (sub n (S O)) (transportf n (S (sub n (S O))) e j))
            (fun i ->
            f
              (transportf (S (sub n (S O))) n
                (pathsinv0 n (S (sub n (S O))) e) i))))
        (f
          (transportf (S (sub n (S O))) n (pathsinv0 n (S (sub n (S O))) e)
            (transportf n (S (sub n (S O))) e j))))
      (let s =
         stnsum (sub n (S O)) (fun x ->
           f
             (transportf (S (sub n (S O))) n
               (pathsinv0 n (S (sub n (S O))) e)
               (dni (sub n (S O)) (transportf n (S (sub n (S O))) e j) x)))
       in
       natlehmplusnm s
         (f
           (transportf n n (pathsinv0 n n Coq_paths_refl)
             (transportf n n Coq_paths_refl j))))
      (stnsum_dni (sub n (S O)) (fun i ->
        f (transportf (S (sub n (S O))) n (pathsinv0 n (S (sub n (S O))) e) i))
        (transportf n (S (sub n (S O))) e j)))
    (transport_stnsum (S (sub n (S O))) n (pathsinv0 n (S (sub n (S O))) e) f)

(** val stnsum_pos_0 : nat -> (stn -> nat) -> hProptoType **)

let stnsum_pos_0 n f =
  stnsum_pos (S n) f (firstelement n)

(** val stnsum_1 : nat -> nat paths **)

let rec stnsum_1 = function
| O -> Coq_paths_refl
| S n0 ->
  pathscomp0 (add (stnsum n0 (fun _ -> S O)) (S O))
    (add (S O) (stnsum n0 (fun _ -> S O))) (S n0)
    (natpluscomm (stnsum n0 (fun _ -> S O)) (S O))
    (maponpaths (fun x -> S x) (stnsum n0 (fun _ -> S O)) n0 (stnsum_1 n0))

(** val stnsum_const : nat -> nat -> nat paths **)

let rec stnsum_const m c =
  match m with
  | O -> Coq_paths_refl
  | S n ->
    maponpaths (fun i -> add i c) (stnsum n (fun _ -> c)) (mul n c)
      (stnsum_const n c)

(** val stnsum_last_le : nat -> (stn -> nat) -> hProptoType **)

let stnsum_last_le n f =
  internal_paths_rew_r (stnsum (S n) f)
    (add (stnsum n (funcomp (dni n (lastelement n)) f)) (f (lastelement n)))
    (natlehmplusnm (stnsum n (funcomp (dni n (lastelement n)) f))
      (f (lastelement n))) (stnsum_step n f)

(** val stnsum_first_le : nat -> (stn -> nat) -> hProptoType **)

let rec stnsum_first_le n f =
  match n with
  | O -> isreflnatleh (stnsum (S O) f)
  | S n0 ->
    internal_paths_rew_r (stnsum (S (S n0)) f)
      (add (stnsum (S n0) (funcomp (dni (S n0) (lastelement (S n0))) f))
        (f (lastelement (S n0))))
      (let w =
         stnsum_first_le n0 (funcomp (dni (S n0) (lastelement (S n0))) f)
       in
       istransnatleh (f (firstelement (S n0)))
         (stnsum (S n0) (funcomp (dni (S n0) (lastelement (S n0))) f))
         (add (stnsum (S n0) (funcomp (dni (S n0) (lastelement (S n0))) f))
           (f (lastelement (S n0)))) w
         (natlehnplusnm
           (stnsum (S n0) (funcomp (dni (S n0) (lastelement (S n0))) f))
           (f (lastelement (S n0))))) (stnsum_step (S n0) f)

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

(** val partial_sum_prop_aux :
    nat -> (stn -> nat) -> stn -> stn -> stn -> stn -> hProptoType ->
    hProptoType **)

let partial_sum_prop_aux n m i i' j j' lt =
  let lt0 = natlthtolehsn (stntonat n i) (stntonat n i') lt in
  let ltS =
    natlehlthtrans (S (stntonat n i)) (stntonat n i') n lt0 (stnlt n i')
  in
  natlthlehtrans
    (add
      (stnsum (stntonat n i)
        (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
      (stntonat (m i) j))
    (stnsum (stntonat n i')
      (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
    (add
      (stnsum (stntonat n i')
        (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
      (stntonat (m i') j'))
    (natlthlehtrans
      (add
        (stnsum (stntonat n i)
          (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
        (stntonat (m i) j))
      (stnsum (S (stntonat n i))
        (funcomp (stn_left'' (S (stntonat n i)) n ltS) m))
      (stnsum (stntonat n i')
        (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
      (internal_paths_rew_r
        (stnsum (S (stntonat n i))
          (funcomp (stn_left'' (S (stntonat n i)) n ltS) m))
        (add
          (stnsum (stntonat n i)
            (funcomp (dni (stntonat n i) (lastelement (stntonat n i)))
              (funcomp (stn_left'' (S (stntonat n i)) n ltS) m)))
          (funcomp (stn_left'' (S (stntonat n i)) n ltS) m
            (lastelement (stntonat n i))))
        (natlthandplusl (stntonat (m i) j)
          (funcomp (stn_left'' (S (stntonat n i)) n ltS) m
            (lastelement (stntonat n i)))
          (stnsum (stntonat n i)
            (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
          (stnlt
            (funcomp (stn_left'' (S (stntonat n i)) n ltS) m
              (lastelement (stntonat n i))) j))
        (stnsum_step (stntonat n i)
          (funcomp (stn_left'' (S (stntonat n i)) n ltS) m)))
      (let e =
         stnsum_eq (S (stntonat n i))
           (funcomp (stn_left'' (S (stntonat n i)) n ltS) m)
           (funcomp (stn_left' (S (stntonat n i)) (stntonat n i') lt0)
             (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
           (fun k ->
           maponpaths m (stn_left'' (S (stntonat n i)) n ltS k)
             (stn_left'' (stntonat n i') n (stnlt n i')
               (stn_left' (S (stntonat n i)) (stntonat n i') lt0 k))
             (subtypePath_prop (fun x -> natlth x n)
               (stn_left'' (S (stntonat n i)) n ltS k)
               (stn_left'' (stntonat n i') n (stnlt n i')
                 (stn_left' (S (stntonat n i)) (stntonat n i') lt0 k))
               Coq_paths_refl))
       in
       internal_paths_rew_r
         (stnsum (S (stntonat n i))
           (funcomp (stn_left'' (S (stntonat n i)) n ltS) m))
         (stnsum (S (stntonat n i))
           (funcomp (stn_left' (S (stntonat n i)) (stntonat n i') lt0)
             (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m)))
         (stnsum_left_le' (S (stntonat n i)) (stntonat n i')
           (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m) lt0) e))
    (natlehnplusnm
      (stnsum (stntonat n i')
        (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
      (stntonat (m i') j'))

(** val partial_sum_prop :
    nat -> (stn -> nat) -> nat -> (stn, (stn, nat paths) total2) total2
    isaprop **)

let partial_sum_prop n m l =
  invproofirrelevance (fun t t' ->
    let i = t.pr1 in
    let je = t.pr2 in
    let j = je.pr1 in
    let e = je.pr2 in
    let i' = t'.pr1 in
    let je' = t'.pr2 in
    let j' = je'.pr1 in
    let e' = je'.pr2 in
    let e'' =
      pathscomp0
        (add
          (stnsum (stntonat n i)
            (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
          (stntonat (m i) j)) l
        (add
          (stnsum (stntonat n i')
            (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
          (stntonat (m i') j')) e
        (pathsinv0
          (add
            (stnsum (stntonat n i')
              (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
            (stntonat (m i') j')) l e')
    in
    let p =
      let c = nat_eq_or_neq (stntonat n i) (stntonat n i') in
      (match c with
       | Coq_ii1 a -> subtypePath_prop (fun x -> natlth x n) i i' a
       | Coq_ii2 b ->
         fromempty
           (nat_neq_to_nopath
             (add
               (stnsum (stntonat n i)
                 (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
               (stntonat (m i) j))
             (add
               (stnsum (stntonat n i')
                 (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
               (stntonat (m i') j'))
             (let c0 = natneqchoice (stntonat n i) (stntonat n i') b in
              match c0 with
              | Coq_ii1 a ->
                natgthtoneq
                  (add
                    (stnsum (stntonat n i)
                      (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
                    (stntonat (m i) j))
                  (add
                    (stnsum (stntonat n i')
                      (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
                    (stntonat (m i') j'))
                  (partial_sum_prop_aux n m i' i j' j a)
              | Coq_ii2 b0 ->
                natlthtoneq
                  (add
                    (stnsum (stntonat n i)
                      (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
                    (stntonat (m i) j))
                  (add
                    (stnsum (stntonat n i')
                      (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
                    (stntonat (m i') j'))
                  (partial_sum_prop_aux n m i i' j j' b0)) e''))
    in
    total2_paths_f { pr1 = i; pr2 = { pr1 = j; pr2 = e } } { pr1 = i'; pr2 =
      { pr1 = j'; pr2 = e' } } p
      (total2_paths_f (transportf i i' p { pr1 = j; pr2 = e }) { pr1 = j';
        pr2 = e' }
        (let e''0 =
           pathscomp0
             (add
               (stnsum (stntonat n i)
                 (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
               (stntonat (m i) j)) l
             (add
               (stnsum (stntonat n i)
                 (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
               (stntonat (m i) j')) e
             (pathsinv0
               (add
                 (stnsum (stntonat n i)
                   (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
                 (stntonat (m i) j')) l e')
         in
         subtypePath_prop (fun x -> natlth x (m i)) j j'
           (natpluslcan (stntonat (m i) j) (stntonat (m i) j')
             (stnsum (stntonat n i)
               (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m)) e''0))
        (let x =
           add
             (stnsum (stntonat n i')
               (funcomp (stn_left'' (stntonat n i') n (stnlt n i')) m))
             (stntonat (m i') j')
         in
         let x0 =
           transportf (transportf i i' p { pr1 = j; pr2 = e }).pr1 j'
             (let e''0 =
                pathscomp0
                  (add
                    (stnsum (stntonat n i)
                      (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
                    (stntonat (m i) j)) l
                  (add
                    (stnsum (stntonat n i)
                      (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
                    (stntonat (m i) j')) e
                  (pathsinv0
                    (add
                      (stnsum (stntonat n i)
                        (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
                      (stntonat (m i) j')) l e')
              in
              subtypePath_prop (fun x0 -> natlth x0 (m i)) j j'
                (natpluslcan (stntonat (m i) j) (stntonat (m i) j')
                  (stnsum (stntonat n i)
                    (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m))
                  e''0)) (transportf i i' p { pr1 = j; pr2 = e }).pr2
         in
         (Obj.magic isasetnat x l x0 e').pr1)))

(** val partial_sum_slot_subproof :
    nat -> (stn -> nat) -> nat -> stn -> stn -> nat paths -> nat paths **)

let partial_sum_slot_subproof n m l =
  let m' = funcomp (dni_lastelement n) m in
  (fun i j j0 ->
  pathscomp0
    (add
      (stnsum (stntonat (S n) (dni_lastelement n i))
        (funcomp
          (stn_left'' (stntonat (S n) (dni_lastelement n i)) (S n)
            (stnlt (S n) (dni_lastelement n i))) m))
      (stntonat (m (dni_lastelement n i)) j))
    (add
      (stnsum (stntonat n i)
        (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m'))
      (stntonat (m' i) j)) l
    (maponpaths (fun x -> add x (stntonat (m' i) j))
      (stnsum (stntonat (S n) (dni_lastelement n i))
        (funcomp
          (stn_left'' (stntonat (S n) (dni_lastelement n i)) (S n)
            (stnlt (S n) (dni_lastelement n i))) m))
      (stnsum (stntonat n i)
        (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m'))
      (stnsum_eq (stntonat (S n) (dni_lastelement n i))
        (funcomp
          (stn_left'' (stntonat (S n) (dni_lastelement n i)) (S n)
            (stnlt (S n) (dni_lastelement n i))) m)
        (funcomp (stn_left'' (stntonat n i) n (stnlt n i)) m') (fun r ->
        maponpaths m (stn_left'' i.pr1 (S n) (natlthtolths i.pr1 n i.pr2) r)
          (dni_lastelement n (stn_left'' (stntonat n i) n (stnlt n i) r))
          (subtypePath_prop (fun x -> natlth x (S n))
            (stn_left'' i.pr1 (S n) (natlthtolths i.pr1 n i.pr2) r)
            (dni_lastelement n (stn_left'' (stntonat n i) n (stnlt n i) r))
            Coq_paths_refl)))) j0)

(** val partial_sum_slot :
    nat -> (stn -> nat) -> nat -> hProptoType -> (stn, (stn, nat paths)
    total2) total2 iscontr **)

let rec partial_sum_slot n m l lt =
  match n with
  | O -> fromempty (negnatlthn0 l lt)
  | S n0 ->
    let m' = funcomp (dni_lastelement n0) m in
    let len' = stnsum n0 m' in
    let c = natlthorgeh l len' in
    (match c with
     | Coq_ii1 a ->
       let iH' = partial_sum_slot n0 m' l a in
       let ijJ = iH'.pr1 in
       let i = ijJ.pr1 in
       let jJ = ijJ.pr2 in
       let j = jJ.pr1 in
       let j0 = jJ.pr2 in
       { pr1 = { pr1 = (dni_lastelement n0 i); pr2 = { pr1 = j; pr2 =
       (partial_sum_slot_subproof n0 m l i j j0) } }; pr2 = (fun t ->
       let x' = { pr1 = (dni_lastelement n0 i); pr2 = { pr1 = j; pr2 =
         (partial_sum_slot_subproof n0 m l i j j0) } }
       in
       (Obj.magic partial_sum_prop (S n0) m l t x').pr1) }
     | Coq_ii2 b ->
       let j = sub l len' in
       iscontraprop1 (partial_sum_prop (S n0) m l)
         (let k = minusplusnmm l len' b in
          { pr1 = (lastelement n0); pr2 = { pr1 = { pr1 = j; pr2 =
          (natlthandpluslinv j (m (lastelement n0)) len'
            (internal_paths_rew_r (add len' j) (add j len') lt
              (natpluscomm len' j))) }; pr2 =
          (pathscomp0
            (add
              (stnsum n0 (funcomp (stn_left'' n0 (S n0) (natgthsnn n0)) m)) j)
            (add (stnsum n0 m') j) l
            (maponpaths (fun x -> add x j)
              (stnsum n0 (funcomp (stn_left'' n0 (S n0) (natgthsnn n0)) m))
              (stnsum n0 m')
              (stnsum_eq n0 (funcomp (stn_left'' n0 (S n0) (natgthsnn n0)) m)
                m' (fun i ->
                maponpaths m (stn_left'' n0 (S n0) (natgthsnn n0) i)
                  (dni_lastelement n0 i)
                  (subtypePath_prop (fun x -> natlth x (S n0))
                    (stn_left'' n0 (S n0) (natgthsnn n0) i)
                    (dni_lastelement n0 i) Coq_paths_refl))))
            (internal_paths_rew_r (add (stnsum n0 m') j)
              (add j (stnsum n0 m')) k (natpluscomm (stnsum n0 m') j))) } }))

(** val stn_right_first : nat -> nat -> stn paths **)

let stn_right_first n i =
  subtypePath_prop (fun x -> natlth x (add i (S n)))
    (stn_right i (S n) (firstelement n))
    (make_stn (add i (S n)) i (natltplusS n i)) (natplusr0 i)

(** val nat_rect_step : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 paths **)

let nat_rect_step _ _ _ =
  Coq_paths_refl

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

(** val weqstnsum1_eq :
    nat -> (stn -> nat) -> ((stn, stn) total2 -> stn) paths **)

let weqstnsum1_eq _ _ =
  Coq_paths_refl

(** val weqstnsum1_eq' :
    nat -> (stn -> nat) -> (stn -> (stn, stn) total2) paths **)

let weqstnsum1_eq' _ _ =
  Coq_paths_refl

(** val weqstnsum :
    nat -> (stn -> nat) -> (stn -> (stn, 'a1) weq) -> ((stn, 'a1) total2,
    stn) weq **)

let weqstnsum n f w =
  weqcomp (invweq (weqfibtototal w)) (weqstnsum1 n f)

(** val weqstnsum2 :
    nat -> (stn -> nat) -> ('a1 -> stn) -> (stn -> (stn, ('a1, stn) hfiber)
    weq) -> ('a1, stn) weq **)

let weqstnsum2 n f g w =
  weqcomp (weqtococonusf g) (weqstnsum n f w)

(** val lexicalEnumeration :
    nat -> (stn -> nat) -> (stn, (stn, stn) total2) weq **)

let lexicalEnumeration n m =
  invweq (weqstnsum1 n m)

(** val inverse_lexicalEnumeration :
    nat -> (stn -> nat) -> ((stn, stn) total2, stn) weq **)

let inverse_lexicalEnumeration =
  weqstnsum1

(** val foldleft : 'a1 -> 'a1 binop -> nat -> (stn -> 'a1) -> 'a1 **)

let rec foldleft e m n x =
  match n with
  | O -> e
  | S n0 ->
    m (foldleft e m n0 (funcomp (dni n0 (lastelement n0)) x))
      (x (lastelement n0))

(** val foldright : 'a1 binop -> 'a1 -> nat -> (stn -> 'a1) -> 'a1 **)

let rec foldright m e n x =
  match n with
  | O -> e
  | S n0 ->
    m (x (firstelement n0))
      (foldright m e n0 (funcomp (dni n0 (firstelement n0)) x))

(** val weqfromprodofstn : nat -> nat -> ((stn, stn) dirprod, stn) weq **)

let weqfromprodofstn n m =
  let c = natgthorleh m O in
  (match c with
   | Coq_ii1 a ->
     let i1 = fun i j li lj ->
       natlthlehtrans (add j (mul i m)) (mul (S i) m) (mul n m)
         (internal_paths_rew_r (add j (mul i m)) (add (mul i m) j)
           (natgthandplusl m j (mul i m) lj) (natpluscomm j (mul i m)))
         (natlehandmultr (S i) n m (natgthtogehsn n i li))
     in
     let f = fun ij ->
       let i = ij.pr1 in
       let j = ij.pr2 in
       make_stn (mul n m) (add (stntonat m j) (mul (stntonat n i) m))
         (i1 (stntonat n i) (stntonat m j) i.pr2 j.pr2)
     in
     { pr1 = f; pr2 =
     (let isinf =
        isinclbetweensets f
          (Obj.magic isofhleveldirprod (S (S O)) (isasetstn n) (isasetstn m))
          (isasetstn (mul n m)) (fun ij ij' e ->
          let i = ij.pr1 in
          let j = ij.pr2 in
          let i' = ij'.pr1 in
          let j' = ij'.pr2 in
          let i0 = i.pr1 in
          let li = i.pr2 in
          let i'0 = i'.pr1 in
          let li' = i'.pr2 in
          let j0 = j.pr1 in
          let lj = j.pr2 in
          let j'0 = j'.pr1 in
          let lj' = j'.pr2 in
          let eei =
            (natdivremunique m i0 j0 i'0 j'0 lj lj'
              (maponpaths (stntonat (mul n m))
                (f { pr1 = { pr1 = i0; pr2 = li }; pr2 = { pr1 = j0; pr2 =
                  lj } })
                (f { pr1 = { pr1 = i'0; pr2 = li' }; pr2 = { pr1 = j'0; pr2 =
                  lj' } }) e)).pr1
          in
          let eeis =
            invmaponpathsincl (stntonat n) (isinclstntonat n)
              (make_stn n i0 li) (make_stn n i'0 li') eei
          in
          let eej =
            (natdivremunique m i0 j0 i'0 j'0 lj lj'
              (maponpaths (stntonat (mul n m))
                (f { pr1 = { pr1 = i0; pr2 = li }; pr2 = { pr1 = j0; pr2 =
                  lj } })
                (f { pr1 = { pr1 = i'0; pr2 = li' }; pr2 = { pr1 = j'0; pr2 =
                  lj' } }) e)).pr2
          in
          let eejs =
            invmaponpathsincl (stntonat m) (isinclstntonat m)
              (make_stn m j0 lj) (make_stn m j'0 lj') eej
          in
          pathsdirprod (make_stn n i0 li) (make_stn n i'0 li')
            (make_stn m j0 lj) (make_stn m j'0 lj') eeis eejs)
      in
      fun xnm ->
      iscontraprop1 (isinf xnm)
        (let xnm0 = xnm.pr1 in
         let lxnm = xnm.pr2 in
         let e =
           pathsinv0 (stntonat (mul n m) { pr1 = xnm0; pr2 = lxnm })
             (add (natrem (stntonat (mul n m) { pr1 = xnm0; pr2 = lxnm }) m)
               (mul
                 (natdiv (stntonat (mul n m) { pr1 = xnm0; pr2 = lxnm }) m) m))
             (natdivremrule (stntonat (mul n m) { pr1 = xnm0; pr2 = lxnm }) m
               (natgthtoneq m O a))
         in
         let i = natdiv (stntonat (mul n m) { pr1 = xnm0; pr2 = lxnm }) m in
         let j = natrem (stntonat (mul n m) { pr1 = xnm0; pr2 = lxnm }) m in
         let li =
           natlthandmultrinv (natdiv xnm0 m) n m
             (natlehlthtrans (mul (natdiv xnm0 m) m) xnm0 (mul n m)
               (natlehmultnatdiv xnm0 m (natgthtoneq m O a)) lxnm)
         in
         let lj = lthnatrem xnm0 m (natgthtoneq m O a) in
         { pr1 = (make_dirprod (make_stn n i li) (make_stn m j lj)); pr2 =
         (invmaponpathsincl (stntonat (mul n m)) (isinclstntonat (mul n m))
           (f (make_dirprod (make_stn n i li) (make_stn m j lj))) { pr1 =
           xnm0; pr2 = lxnm } e) })) }
   | Coq_ii2 b ->
     let e = natleh0tois0 m b in
     internal_paths_rew_r m O
       (internal_paths_rew_r (mul n O) O { pr1 = (fun t -> t.pr2); pr2 =
         (isweqtoempty2 (fun t -> t.pr2) (pr1weq weqstn0toempty)) }
         (natmultn0 n)) e)

(** val weqfromdecsubsetofstn :
    nat -> (stn -> bool) -> (nat, ((stn, bool) hfiber, stn) weq) total2 **)

let rec weqfromdecsubsetofstn = function
| O ->
  (fun _ -> { pr1 = O; pr2 =
    (let g = fun _ -> assert false (* absurd case *) in
     weqtoempty2 g (pr1weq weqstn0toempty)) })
| S n0 ->
  let iHn = weqfromdecsubsetofstn n0 in
  (fun f ->
  let g = weqfromcoprodofstn (S O) n0 in
  let fl = fun i -> f (pr1weq g (Coq_ii1 i)) in
  let fh = fun i -> f (pr1weq g (Coq_ii2 i)) in
  let w =
    let int = invweq (weqhfibersgwtog g f Coq_true) in
    let h = fun x ->
      match x with
      | Coq_ii1 _ -> Coq_paths_refl
      | Coq_ii2 _ -> Coq_paths_refl
    in
    weqcomp int
      (weqhfibershomot (fun x -> f (pr1weq g x)) (sumofmaps fl fh) h Coq_true)
  in
  let w' = weqcomp w (invweq (weqhfibersofsumofmaps fl fh Coq_true)) in
  let x0 = (iHn fh).pr1 in
  let w0 = (iHn fh).pr2 in
  let c = boolchoice (fl (lastelement O)) in
  (match c with
   | Coq_ii1 p ->
     { pr1 = (S x0); pr2 =
       (let wi =
          let is =
            iscontraprop1 (isinclfromstn1 fl isasetbool Coq_true)
              (make_hfiber fl Coq_true (lastelement O) p)
          in
          weqcontrcontr is iscontrstn1
        in
        weqcomp (weqcomp w' (weqcoprodf wi w0))
          (weqfromcoprodofstn (S O) (iHn fh).pr1)) }
   | Coq_ii2 _ ->
     { pr1 = x0; pr2 =
       (let g' = fun _ -> assert false (* absurd case *) in
        weqcomp w' (weqcomp (invweq (weqii2withneg g')) w0)) }))

(** val weqfromhfiberfromstn :
    nat -> 'a1 -> 'a1 isisolated -> (stn -> 'a1) -> (nat, ((stn, 'a1) hfiber,
    stn) weq) total2 **)

let weqfromhfiberfromstn n x is f =
  let t = weqfromdecsubsetofstn n (fun i -> eqbx x is (f i)) in
  { pr1 = t.pr1; pr2 = (weqcomp (weqhfibertobhfiber f x is) t.pr2) }

(** val weqfromfunstntostn : nat -> nat -> (stn -> stn, stn) weq **)

let rec weqfromfunstntostn n m =
  match n with
  | O ->
    weqcontrcontr (iscontrfunfromempty2 (pr1weq weqstn0toempty)) iscontrstn1
  | S n0 ->
    let w1 = weqfromcoprodofstn (S O) n0 in
    let w2 = weqbfun w1 in
    let w3 = weqcomp w2 weqfunfromcoprodtoprod in
    let w4 =
      weqcomp w3
        (weqdirprodf (weqfunfromcontr iscontrstn1) (weqfromfunstntostn n0 m))
    in
    weqcomp w4 (weqfromprodofstn m (natpower m n0))

(** val stnprod : nat -> (stn -> nat) -> nat **)

let rec stnprod n f =
  match n with
  | O -> S O
  | S n0 ->
    mul (stnprod n0 (fun i -> f (dni n0 (lastelement n0) i)))
      (f (lastelement n0))

(** val stnprod_step : nat -> (stn -> nat) -> nat paths **)

let stnprod_step _ _ =
  Coq_paths_refl

(** val stnprod_eq :
    nat -> (stn -> nat) -> (stn -> nat) -> (stn, nat) homot -> nat paths **)

let rec stnprod_eq n f g h =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    internal_paths_rew_r (stnprod (S n0) f)
      (mul (stnprod n0 (funcomp (dni n0 (lastelement n0)) f))
        (f (lastelement n0)))
      (internal_paths_rew_r (stnprod (S n0) g)
        (mul (stnprod n0 (funcomp (dni n0 (lastelement n0)) g))
          (g (lastelement n0)))
        (maponpaths (fun i -> mul i (f (lastelement n0)))
          (stnprod n0 (funcomp (dni n0 (lastelement n0)) f))
          (stnprod n0 (funcomp (dni n0 (lastelement n0)) g))
          (stnprod_eq n0 (funcomp (dni n0 (lastelement n0)) f)
            (funcomp (dni n0 (lastelement n0)) g) (fun x ->
            h (dni n0 (lastelement n0) x)))) (stnprod_step n0 g))
      (stnprod_step n0 f)

(** val weqstnprod :
    nat -> (stn -> nat) -> (stn -> (stn, 'a1) weq) -> (stn -> 'a1, stn) weq **)

let rec weqstnprod n f ww =
  match n with
  | O -> weqcontrcontr (iscontrsecoverempty2 negstn0) iscontrstn1
  | S n0 ->
    let w1 = weqdnicoprod n0 (lastelement n0) in
    let w2 = weqonsecbase w1 in
    let w4 = weqcomp w2 weqsecovercoprodtoprod in
    let w5 =
      weqstnprod n0 (fun x -> f (pr1weq w1 (Coq_ii1 x))) (fun i ->
        ww (pr1weq w1 (Coq_ii1 i)))
    in
    let w6 = weqcomp w4 (weqdirprodf w5 weqsecoverunit) in
    let w7 = weqcomp w6 (weqdirprodf idweq (invweq (ww (lastelement n0)))) in
    weqcomp w7
      (weqfromprodofstn (stnprod n0 (fun x -> f (dni n0 (lastelement n0) x)))
        (f (lastelement n0)))

(** val weqweqstnsn :
    nat -> ((stn, stn) weq, (stn, (stn, stn) weq) dirprod) weq **)

let weqweqstnsn n =
  let l = lastelement n in
  weqcomp (weqcutonweq l (fun i -> isdeceqstn (S n) l i))
    (weqdirprodf (weqisolatedstntostn (S n))
      (weqweq
        (invweq
          (weqcomp (weqdnicompl n l) (compl_weq_compl_ne l (stnneq (S n) l))))))

(** val weqfromweqstntostn : nat -> ((stn, stn) weq, stn) weq **)

let rec weqfromweqstntostn = function
| O ->
  weqcontrcontr (iscontraprop1 (isapropweqtoempty2 negstn0) idweq) iscontrstn1
| S n0 ->
  let w1 = weqweqstnsn n0 in
  weqcomp w1
    (weqcomp (weqdirprodf idweq (weqfromweqstntostn n0))
      (weqfromprodofstn (S n0) (factorial n0)))

(** val ischoicebasestn : nat -> hProptoType **)

let rec ischoicebasestn = function
| O -> ischoicebaseempty2 negstn0
| S n0 ->
  ischoicebaseweqf (weqdnicoprod n0 (lastelement n0))
    (ischoicebasecoprod (ischoicebasestn n0) ischoicebaseunit)

(** val negweqstnsn0 : nat -> (stn, stn) weq neg **)

let negweqstnsn0 n =
  let lp = lastelement n in (fun x -> weqstn0toempty.pr1 (x.pr1 lp))

(** val negweqstn0sn : nat -> (stn, stn) weq neg **)

let negweqstn0sn n =
  let lp = lastelement n in (fun x -> weqstn0toempty.pr1 ((invweq x).pr1 lp))

(** val weqcutforstn : nat -> nat -> (stn, stn) weq -> (stn, stn) weq **)

let weqcutforstn n n' w =
  let k = lastelement n in
  weqcomp (weqdnicompl n k)
    (weqcomp
      (weqoncompl_ne w k (stnneq (S n) k) (stnneq (S n') (pr1weq w k)))
      (invweq (weqdnicompl n' (pr1weq w k))))

(** val weqtoeqstn : nat -> nat -> (stn, stn) weq -> nat paths **)

let rec weqtoeqstn n n' x =
  match n with
  | O ->
    (match n' with
     | O -> Coq_paths_refl
     | S n0 -> fromempty (negweqstn0sn n0 x))
  | S n0 ->
    (match n' with
     | O -> fromempty (negweqstnsn0 n0 x)
     | S n1 ->
       maponpaths (fun x0 -> S x0) n0 n1
         (weqtoeqstn n0 n1 (weqcutforstn n0 n1 x)))

(** val eqtoweqstn_subproof :
    nat -> nat -> nat paths -> stn -> hProptoType **)

let eqtoweqstn_subproof n n' h i =
  transportf n n' h (stnlt n i)

(** val eqtoweqstn_subproof0 :
    nat -> nat -> nat paths -> stn -> hProptoType **)

let eqtoweqstn_subproof0 n n' h i =
  transportf n' n (pathsinv0 n n' h) (stnlt n' i)

(** val eqtoweqstn_subproof1 : nat -> nat -> nat paths -> stn -> stn paths **)

let eqtoweqstn_subproof1 n n' h i =
  stn_eq n
    (make_stn n
      (stntonat n'
        (make_stn n' (stntonat n i) (eqtoweqstn_subproof n n' h i)))
      (eqtoweqstn_subproof0 n n' h
        (make_stn n' (stntonat n i) (eqtoweqstn_subproof n n' h i)))) i
    Coq_paths_refl

(** val eqtoweqstn_subproof2 : nat -> nat -> nat paths -> stn -> stn paths **)

let eqtoweqstn_subproof2 n n' h i =
  stn_eq n'
    (make_stn n'
      (stntonat n
        (make_stn n (stntonat n' i) (eqtoweqstn_subproof0 n n' h i)))
      (eqtoweqstn_subproof n n' h
        (make_stn n (stntonat n' i) (eqtoweqstn_subproof0 n n' h i)))) i
    Coq_paths_refl

(** val eqtoweqstn : nat -> nat -> nat paths -> (stn, stn) weq **)

let eqtoweqstn n n' h =
  weq_iso (fun i ->
    make_stn n' (stntonat n i) (eqtoweqstn_subproof n n' h i)) (fun i ->
    make_stn n (stntonat n' i) (eqtoweqstn_subproof0 n n' h i))
    (eqtoweqstn_subproof1 n n' h) (eqtoweqstn_subproof2 n n' h)

(** val stnsdnegweqtoeq : nat -> nat -> (stn, stn) weq dneg -> nat paths **)

let stnsdnegweqtoeq n n' dw =
  eqfromdnegeq isdeceqnat n n' (dnegf (weqtoeqstn n n') dw)

(** val weqforallnatlehn0 :
    (nat -> hProp) -> (nat -> hProptoType -> hProptoType, hProptoType) weq **)

let weqforallnatlehn0 f =
  let lg = { pr1 = (fun f0 -> f0 O (isreflnatleh O)); pr2 = (fun f0 n l ->
    let e = natleh0tois0 n l in internal_paths_rew_r n O f0 e) }
  in
  let is1 = impred (S O) (fun n -> impred (S O) (fun _ -> (f n).pr2)) in
  weqimplimpl lg.pr1 lg.pr2 is1 (f O).pr2

(** val weqforallnatlehnsn' :
    nat -> (nat -> hProp) -> (nat -> hProptoType -> hProptoType, (nat ->
    hProptoType -> hProptoType, hProptoType) dirprod) weq **)

let weqforallnatlehnsn' n' f =
  let lg = { pr1 = (fun f0 ->
    make_dirprod (fun n l -> f0 n (natlehtolehs n n' l))
      (f0 (S n') (isreflnatleh (S n')))); pr2 = (fun d2 n l ->
    let c = natlehchoice2 n (S n') l in
    (match c with
     | Coq_ii1 h -> d2.pr1 n h
     | Coq_ii2 p -> let d3 = d2.pr2 in internal_paths_rew_r n (S n') d3 p)) }
  in
  let is1 = impred (S O) (fun n -> impred (S O) (fun _ -> (f n).pr2)) in
  let is2 =
    isapropdirprod
      (impred (S O) (fun n -> impred (S O) (fun _ -> (f n).pr2)))
      (f (S n')).pr2
  in
  weqimplimpl lg.pr1 lg.pr2 is1 is2

(** val weqexistsnatlehn0 :
    (nat -> hProp) -> (hProptoType, hProptoType) weq **)

let weqexistsnatlehn0 p =
  let lg = { pr1 = (hinhuniv (p O) (fun t2 -> let d2 = t2.pr2 in d2.pr2));
    pr2 = (fun p0 ->
    hinhpr { pr1 = O; pr2 = { pr1 = (isreflnatleh O); pr2 = p0 } }) }
  in
  weqimplimpl lg.pr1 lg.pr2 hexists.pr2 (p O).pr2

(** val weqexistsnatlehnsn' :
    nat -> (nat -> hProp) -> (hProptoType, hProptoType) weq **)

let weqexistsnatlehnsn' n' _ =
  let lg = { pr1 =
    (hinhfun (fun t2 ->
      let n = t2.pr1 in
      let d2 = t2.pr2 in
      let l = d2.pr1 in
      let p = d2.pr2 in
      let c = natlehchoice2 n (S n') l in
      (match c with
       | Coq_ii1 h -> Coq_ii1 (hinhpr { pr1 = n; pr2 = (make_dirprod h p) })
       | Coq_ii2 _ -> Coq_ii2 p))); pr2 =
    (hinhuniv ishinh (fun c ->
      match c with
      | Coq_ii1 i ->
        hinhfun (fun t ->
          let n = t.pr1 in
          let d2 = t.pr2 in
          let l = d2.pr1 in
          let p = d2.pr2 in
          { pr1 = n; pr2 = { pr1 = (natlehtolehs n n' l); pr2 = p } }) i
      | Coq_ii2 h ->
        hinhpr { pr1 = (S n'); pr2 = { pr1 = (isreflnatleh n'); pr2 = h } })) }
  in
  weqimplimpl lg.pr1 lg.pr2 hexists.pr2 hdisj.pr2

(** val isdecbexists :
    nat -> (nat -> 'a1 isdecprop) -> hProptoType isdecprop **)

let isdecbexists n is =
  let p' = fun n' -> make_hProp (isdecproptoisaprop (is n')) in
  let rec f = function
  | O -> isdecpropweqb (Obj.magic weqexistsnatlehn0 p') (is O)
  | S n1 ->
    isdecpropweqb (weqexistsnatlehnsn' n1 p')
      (isdecprophdisj (f n1) (is (S n1)))
  in f n

(** val isdecbforall :
    nat -> (nat -> 'a1 isdecprop) -> (nat -> hProptoType -> 'a1) isdecprop **)

let isdecbforall n is =
  let p' = fun n' -> make_hProp (isdecproptoisaprop (is n')) in
  let rec f = function
  | O -> isdecpropweqb (Obj.magic weqforallnatlehn0 p') (is O)
  | S n1 ->
    isdecpropweqb (Obj.magic weqforallnatlehnsn' n1 p')
      (isdecpropdirprod (f n1) (is (S n1)))
  in f n

(** val negbforalldectototal2neg :
    nat -> (nat -> 'a1 isdecprop) -> (nat -> hProptoType -> 'a1) neg -> (nat,
    (hProptoType, 'a1 neg) dirprod) total2 **)

let negbforalldectototal2neg n is =
  let p' = fun n' -> make_hProp (isdecproptoisaprop (is n')) in
  let rec f n0 nf =
    match n0 with
    | O ->
      let nf0 = negf (pr1weq (invweq (Obj.magic weqforallnatlehn0 p'))) nf in
      { pr1 = O; pr2 = (make_dirprod (isreflnatleh O) nf0) }
    | S n1 ->
      let nf2 =
        negf (pr1weq (invweq (Obj.magic weqforallnatlehnsn' n1 p'))) nf
      in
      let nf3 = fromneganddecy (is (S n1)) nf2 in
      (match nf3 with
       | Coq_ii1 n2 ->
         let int = f n1 n2 in
         let n' = int.pr1 in
         let d2 = int.pr2 in
         let l = d2.pr1 in
         let np = d2.pr2 in
         { pr1 = n'; pr2 = { pr1 = (natlehtolehs n' n1 l); pr2 = np } }
       | Coq_ii2 n2 ->
         { pr1 = (S n1); pr2 = { pr1 = (isreflnatleh (S n1)); pr2 = n2 } })
  in f n

type 'f natdecleast = (nat, ('f, nat -> 'f -> hProptoType) dirprod) total2

(** val isapropnatdecleast :
    (nat -> 'a1 isdecprop) -> 'a1 natdecleast isaprop **)

let isapropnatdecleast is =
  let p = fun n' -> make_hProp (isdecproptoisaprop (is n')) in
  let int1 = fun n ->
    isapropdirprod (p n).pr2
      (impred (S O) (fun t -> impred (S O) (fun _ -> (natleh n t).pr2)))
  in
  let int2 = fun n -> make_hProp (int1 n) in
  isapropsubtype int2 (fun x1 x2 c1 c2 ->
    let e1 = (Obj.magic c1).pr1 in
    let c3 = (Obj.magic c1).pr2 in
    let e2 = (Obj.magic c2).pr1 in
    let c4 = (Obj.magic c2).pr2 in
    let l1 = c3 x2 e2 in let l2 = c4 x1 e1 in isantisymmnatleh x1 x2 l1 l2)

(** val accth : (nat -> 'a1 isdecprop) -> hProptoType -> 'a1 natdecleast **)

let accth is is' =
  Obj.magic hinhuniv (make_hProp (isapropnatdecleast is)) (fun t2 ->
    let n = t2.pr1 in
    let l = t2.pr2 in
    let rec f = function
    | O ->
      hinhuniv (make_hProp (isapropnatdecleast is)) (fun t3 ->
        let is'' = t3.pr2 in
        let d'' = is''.pr2 in
        Obj.magic { pr1 = O; pr2 = { pr1 = d''; pr2 = (fun n' _ ->
          natleh0n n') } })
    | S n1 ->
      hinhuniv (make_hProp (isapropnatdecleast is)) (fun t3 ->
        let n'' = t3.pr1 in
        let is'' = t3.pr2 in
        let j = natlehchoice2 n'' (S n1) is''.pr1 in
        (match j with
         | Coq_ii1 h ->
           f n1 (hinhpr { pr1 = n''; pr2 = (make_dirprod h is''.pr2) })
         | Coq_ii2 p ->
           let is''0 = internal_paths_rew n'' is'' (S n1) p in
           let is''1 = is''0.pr2 in
           let is'0 = isdecbexists n1 is in
           let c = is'0.pr1 in
           (match c with
            | Coq_ii1 h -> f n1 h
            | Coq_ii2 _ ->
              Obj.magic { pr1 = (S n1); pr2 = { pr1 = is''1; pr2 =
                (fun n2 _ ->
                let c0 = natlthorgeh n2 (S n1) in
                (match c0 with
                 | Coq_ii1 _ -> assert false (* absurd case *)
                 | Coq_ii2 h -> h)) } })))
    in f n (hinhpr { pr1 = n; pr2 = (make_dirprod (isreflnatleh n) l) })) is'

(** val dni_lastelement_is_inj :
    nat -> stn -> stn -> stn paths -> stn paths **)

let dni_lastelement_is_inj n i j e =
  Obj.magic isinjstntonat n i j
    (maponpaths (fun t -> t.pr1) { pr1 = i.pr1; pr2 =
      (natlthtolths i.pr1 n i.pr2) } { pr1 = j.pr1; pr2 =
      (natlthtolths j.pr1 n j.pr2) } e)

(** val dni_lastelement_eq : nat -> stn -> hProptoType -> stn paths **)

let dni_lastelement_eq n i ie =
  Obj.magic isinjstntonat (S n) i (dni_lastelement n (make_stn n i.pr1 ie))
    Coq_paths_refl

(** val lastelement_eq : nat -> stn -> nat paths -> stn paths **)

let lastelement_eq n i e =
  Obj.magic isinjstntonat (S n) i { pr1 = n; pr2 = (natgthsnn n) } e

(** val concatenate' :
    nat -> nat -> (stn -> 'a1) -> (stn -> 'a1) -> stn -> 'a1 **)

let concatenate' m n f g i =
  let c = weqfromcoprodofstn_invmap m n i in
  (match c with
   | Coq_ii1 a -> f a
   | Coq_ii2 b -> g b)

(** val concatenate'_r0 :
    nat -> (stn -> 'a1) -> (stn -> 'a1) -> (stn -> 'a1) paths **)

let concatenate'_r0 m f g =
  Obj.magic funextfun (concatenate' m O f g)
    (transportb (add m O) m (natplusr0 m) (Obj.magic f)) (fun i ->
    internal_paths_rew_r (weqfromcoprodofstn_invmap m O (Obj.magic i))
      (Coq_ii1 (transportf (add m O) m (natplusr0 m) (Obj.magic i)))
      (transportb_fun' (add m O) m (Obj.magic f) (natplusr0 m) i)
      (weqfromcoprodofstn_invmap_r0 m (Obj.magic i)))

(** val concatenate'_r0' :
    nat -> (stn -> 'a1) -> (stn -> 'a1) -> stn -> 'a1 paths **)

let concatenate'_r0' m _ _ i =
  internal_paths_rew_r (weqfromcoprodofstn_invmap m O i) (Coq_ii1
    (transportf (add m O) m (natplusr0 m) i)) Coq_paths_refl
    (weqfromcoprodofstn_invmap_r0 m i)

(** val flatten' :
    nat -> (stn -> nat) -> (stn -> stn -> 'a1) -> stn -> 'a1 **)

let flatten' n m g =
  funcomp (invmap (weqstnsum1 n m)) (uncurry g)

(** val stn_predicate :
    nat -> nat -> hProptoType -> hProptoType -> 'a1 -> 'a1 **)

let stn_predicate n k h h' h0 =
  let x = let p = natlth k n in (Obj.magic propproperty p h h').pr1 in
  transportf h h' x h0

type two = stn

(** val two_rec : 'a1 -> 'a1 -> stn -> 'a1 **)

let two_rec a b x =
  let n = x.pr1 in
  (match n with
   | O -> a
   | S n0 -> (match n0 with
              | O -> b
              | S _ -> assert false (* absurd case *)))

(** val two_rec_dep : 'a1 -> 'a1 -> two -> 'a1 **)

let two_rec_dep a b n =
  let n0 = n.pr1 in
  let p = n.pr2 in
  (match n0 with
   | O -> stn_predicate (S (S O)) O (Obj.magic Coq_paths_refl) p a
   | S n1 ->
     (match n1 with
      | O -> stn_predicate (S (S O)) (S O) (Obj.magic Coq_paths_refl) p b
      | S _ -> assert false (* absurd case *)))

type three = stn

(** val three_rec : 'a1 -> 'a1 -> 'a1 -> stn -> 'a1 **)

let three_rec a b c x =
  let n = x.pr1 in
  (match n with
   | O -> a
   | S n0 ->
     (match n0 with
      | O -> b
      | S n1 -> (match n1 with
                 | O -> c
                 | S _ -> assert false (* absurd case *))))

(** val three_rec_dep : 'a1 -> 'a1 -> 'a1 -> three -> 'a1 **)

let three_rec_dep a b c n =
  let n0 = n.pr1 in
  let p = n.pr2 in
  (match n0 with
   | O -> stn_predicate (S (S (S O))) O (Obj.magic Coq_paths_refl) p a
   | S n1 ->
     (match n1 with
      | O -> stn_predicate (S (S (S O))) (S O) (Obj.magic Coq_paths_refl) p b
      | S n2 ->
        (match n2 with
         | O ->
           stn_predicate (S (S (S O))) (S (S O)) (Obj.magic Coq_paths_refl) p
             c
         | S _ -> assert false (* absurd case *))))

type is_stn_increasing = stn -> stn -> hProptoType -> hProptoType

type is_stn_strictly_increasing = stn -> stn -> hProptoType -> hProptoType

(** val is_strincr_impl_incr :
    nat -> (stn -> nat) -> is_stn_strictly_increasing -> is_stn_increasing **)

let is_strincr_impl_incr m f inc i j e =
  let c = natlehchoice (stntonat m i) (stntonat m j) e in
  (match c with
   | Coq_ii1 a -> natlthtoleh (f i) (f j) (inc i j a)
   | Coq_ii2 _ -> isreflnatleh (f i))

(** val is_incr_impl_strincr :
    nat -> (stn -> nat) -> (stn, nat) isincl -> is_stn_increasing ->
    is_stn_strictly_increasing **)

let is_incr_impl_strincr m f _ incr i j e =
  let d = natlthtoleh (stntonat m i) (stntonat m j) e in
  let c = incr i j d in
  let c0 = natlehchoice (f i) (f j) c in
  (match c0 with
   | Coq_ii1 a -> a
   | Coq_ii2 _ -> fromempty (isirreflnatlth (stntonat m i) e))

(** val stnsum_ge1 :
    nat -> (stn -> nat) -> (stn -> hProptoType) -> hProptoType **)

let stnsum_ge1 m f g =
  let g0 = fun _ -> S O in stnsum_le m g0 f g

(** val stnsum_add : nat -> (stn -> nat) -> (stn -> nat) -> nat paths **)

let rec stnsum_add n f g =
  match n with
  | O -> Coq_paths_refl
  | S n0 ->
    internal_paths_rew_r (stnsum (S n0) (fun i -> add (f i) (g i)))
      (add
        (stnsum n0
          (funcomp (dni n0 (lastelement n0)) (fun i -> add (f i) (g i))))
        (add (f (lastelement n0)) (g (lastelement n0))))
      (internal_paths_rew_r (stnsum (S n0) f)
        (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
          (f (lastelement n0)))
        (internal_paths_rew_r (stnsum (S n0) g)
          (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) g))
            (g (lastelement n0)))
          (internal_paths_rew_r
            (stnsum n0 (fun i ->
              add (f (dni n0 (lastelement n0) i))
                (g (dni n0 (lastelement n0) i))))
            (add (stnsum n0 (fun i -> f (dni n0 (lastelement n0) i)))
              (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i))))
            (internal_paths_rew_r
              (add
                (add (stnsum n0 (fun i -> f (dni n0 (lastelement n0) i)))
                  (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i))))
                (add (f (lastelement n0)) (g (lastelement n0))))
              (add (stnsum n0 (fun i -> f (dni n0 (lastelement n0) i)))
                (add (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i)))
                  (add (f (lastelement n0)) (g (lastelement n0)))))
              (internal_paths_rew_r
                (add
                  (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                    (f (lastelement n0)))
                  (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) g))
                    (g (lastelement n0))))
                (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                  (add (f (lastelement n0))
                    (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) g))
                      (g (lastelement n0)))))
                (maponpaths
                  (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) f)))
                  (add (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i)))
                    (add (f (lastelement n0)) (g (lastelement n0))))
                  (add (f (lastelement n0))
                    (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) g))
                      (g (lastelement n0))))
                  (internal_paths_rew_r
                    (add (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i)))
                      (add (f (lastelement n0)) (g (lastelement n0))))
                    (add (add (f (lastelement n0)) (g (lastelement n0)))
                      (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i))))
                    (internal_paths_rew_r
                      (add (add (f (lastelement n0)) (g (lastelement n0)))
                        (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i))))
                      (add (f (lastelement n0))
                        (add (g (lastelement n0))
                          (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i)))))
                      (maponpaths (add (f (lastelement n0)))
                        (add (g (lastelement n0))
                          (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i))))
                        (add
                          (stnsum n0 (funcomp (dni n0 (lastelement n0)) g))
                          (g (lastelement n0)))
                        (internal_paths_rew_r
                          (add (g (lastelement n0))
                            (stnsum n0 (fun i ->
                              g (dni n0 (lastelement n0) i))))
                          (add
                            (stnsum n0 (fun i ->
                              g (dni n0 (lastelement n0) i)))
                            (g (lastelement n0))) Coq_paths_refl
                          (natpluscomm (g (lastelement n0))
                            (stnsum n0 (fun i ->
                              g (dni n0 (lastelement n0) i))))))
                      (natplusassoc (f (lastelement n0)) (g (lastelement n0))
                        (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i)))))
                    (natpluscomm
                      (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i)))
                      (add (f (lastelement n0)) (g (lastelement n0))))))
                (natplusassoc
                  (stnsum n0 (funcomp (dni n0 (lastelement n0)) f))
                  (f (lastelement n0))
                  (add (stnsum n0 (funcomp (dni n0 (lastelement n0)) g))
                    (g (lastelement n0)))))
              (natplusassoc
                (stnsum n0 (fun i -> f (dni n0 (lastelement n0) i)))
                (stnsum n0 (fun i -> g (dni n0 (lastelement n0) i)))
                (add (f (lastelement n0)) (g (lastelement n0)))))
            (stnsum_add n0 (fun i -> f (dni n0 (lastelement n0) i)) (fun i ->
              g (dni n0 (lastelement n0) i)))) (stnsum_step n0 g))
        (stnsum_step n0 f)) (stnsum_step n0 (fun i -> add (f i) (g i)))

(** val stnsum_lt :
    nat -> (stn -> nat) -> (stn -> nat) -> (stn -> hProptoType) -> hProptoType **)

let stnsum_lt m f g x =
  let h = fun i -> add (f i) (S O) in
  let e =
    internal_paths_rew_r (stnsum m (fun i -> add (f i) (S O)))
      (add (stnsum m f) (stnsum m (fun _ -> S O)))
      (internal_paths_rew_r (stnsum m (fun _ -> S O)) m Coq_paths_refl
        (stnsum_1 m)) (stnsum_add m f (fun _ -> S O))
  in
  internal_paths_rew (stnsum m h)
    (stnsum_le m h g (fun i -> natlthtolehp1 (f i) (g i) (x i)))
    (add (stnsum m f) m) e

(** val stnsum_diffs :
    nat -> (stn -> nat) -> is_stn_increasing -> nat paths **)

let rec stnsum_diffs n f e =
  match n with
  | O ->
    pathsinv0 (sub (f (firstelement O)) (f (firstelement O))) O
      (minuseq0' (f (firstelement O)))
  | S n0 ->
    internal_paths_rew_r
      (stnsum (S n0) (fun i ->
        sub (f (dni_firstelement (S n0) i)) (f (dni_lastelement (S n0) i))))
      (add
        (stnsum n0
          (funcomp (dni n0 (lastelement n0)) (fun i ->
            sub (f (dni_firstelement (S n0) i)) (f (dni_lastelement (S n0) i)))))
        (sub (f (dni_firstelement (S n0) (lastelement n0)))
          (f (dni_lastelement (S n0) (lastelement n0)))))
      (internal_paths_rew_r
        (add
          (stnsum n0
            (funcomp (dni n0 (lastelement n0)) (fun i ->
              sub (f (dni_firstelement (S n0) i))
                (f (dni_lastelement (S n0) i)))))
          (sub (f (lastelement (S n0)))
            (f (dni_lastelement (S n0) (lastelement n0)))))
        (add
          (sub (f (lastelement (S n0)))
            (f (dni_lastelement (S n0) (lastelement n0))))
          (stnsum n0
            (funcomp (dni n0 (lastelement n0)) (fun i ->
              sub (f (dni_firstelement (S n0) i))
                (f (dni_lastelement (S n0) i))))))
        (pathscomp0
          (add
            (sub (f (lastelement (S n0)))
              (f (dni_lastelement (S n0) (lastelement n0))))
            (stnsum n0
              (funcomp (dni n0 (lastelement n0)) (fun i ->
                sub (f (dni_firstelement (S n0) i))
                  (f (dni_lastelement (S n0) i))))))
          (add
            (sub (f (lastelement (S n0)))
              (f (dni_lastelement (S n0) (lastelement n0))))
            (sub (f (dni_lastelement (S n0) (lastelement n0)))
              (f (firstelement (S n0)))))
          (sub (f (lastelement (S n0))) (f (firstelement (S n0))))
          (maponpaths
            (add
              (sub (f (lastelement (S n0)))
                (f (dni_lastelement (S n0) (lastelement n0)))))
            (stnsum n0
              (funcomp (dni n0 (lastelement n0)) (fun i ->
                sub (f (dni_firstelement (S n0) i))
                  (f (dni_lastelement (S n0) i)))))
            (sub (f (dni_lastelement (S n0) (lastelement n0)))
              (f (firstelement (S n0))))
            (pathscomp0
              (stnsum n0
                (funcomp (dni n0 (lastelement n0)) (fun i ->
                  sub (f (dni_firstelement (S n0) i))
                    (f (dni_lastelement (S n0) i)))))
              (stnsum n0 (fun i ->
                sub
                  (funcomp (dni_lastelement (S n0)) f (dni_firstelement n0 i))
                  (funcomp (dni_lastelement (S n0)) f (dni_lastelement n0 i))))
              (sub (f (dni_lastelement (S n0) (lastelement n0)))
                (f (firstelement (S n0))))
              (stnsum_eq n0
                (funcomp (dni n0 (lastelement n0)) (fun i ->
                  sub (f (dni_firstelement (S n0) i))
                    (f (dni_lastelement (S n0) i)))) (fun i ->
                sub (f (dni_lastelement (S n0) (dni_firstelement n0 i)))
                  (f (dni_lastelement (S n0) (dni_lastelement n0 i))))
                (fun _ ->
                internal_paths_rew_r (dni n0 (lastelement n0))
                  (dni_lastelement n0) Coq_paths_refl (replace_dni_last n0)))
              (pathscomp0
                (stnsum n0 (fun i ->
                  sub
                    (funcomp (dni_lastelement (S n0)) f
                      (dni_firstelement n0 i))
                    (funcomp (dni_lastelement (S n0)) f
                      (dni_lastelement n0 i))))
                (sub (funcomp (dni_lastelement (S n0)) f (lastelement n0))
                  (funcomp (dni_lastelement (S n0)) f (firstelement n0)))
                (sub (f (dni_lastelement (S n0) (lastelement n0)))
                  (f (firstelement (S n0))))
                (stnsum_diffs n0 (funcomp (dni_lastelement (S n0)) f)
                  (fun i j s ->
                  e (dni_lastelement (S n0) i) (dni_lastelement (S n0) j) s))
                Coq_paths_refl)))
          (pathsinv0 (sub (f (lastelement (S n0))) (f (firstelement (S n0))))
            (add
              (sub (f (lastelement (S n0)))
                (f (dni_lastelement (S n0) (lastelement n0))))
              (sub (f (dni_lastelement (S n0) (lastelement n0)))
                (f (firstelement (S n0)))))
            (natdiffplusdiff (f (lastelement (S n0)))
              (f (dni_lastelement (S n0) (lastelement n0)))
              (f (firstelement (S n0)))
              (e (dni_lastelement (S n0) (lastelement n0))
                (lastelement (S n0))
                (lastelement_ge (S n0)
                  (dni_lastelement (S n0) (lastelement n0))))
              (e (firstelement (S n0))
                (dni_lastelement (S n0) (lastelement n0))
                (firstelement_le (S n0)
                  (dni_lastelement (S n0) (lastelement n0)))))))
        (natpluscomm
          (stnsum n0
            (funcomp (dni n0 (lastelement n0)) (fun i ->
              sub (f (dni_firstelement (S n0) i))
                (f (dni_lastelement (S n0) i)))))
          (sub (f (lastelement (S n0)))
            (f (dni_lastelement (S n0) (lastelement n0))))))
      (stnsum_step n0 (fun i ->
        sub (f (dni_firstelement (S n0) i)) (f (dni_lastelement (S n0) i))))

(** val stn_ord_incl :
    nat -> (stn -> nat) -> is_stn_strictly_increasing -> hProptoType **)

let stn_ord_incl m f strinc =
  let inc = is_strincr_impl_incr (S m) f strinc in
  let d = fun i -> sub (f (dni_firstelement m i)) (f (dni_lastelement m i)) in
  let e = stnsum_diffs m f inc in
  let f0 = fun i ->
    strinc (dni_lastelement m i) (dni_firstelement m i)
      (natlthnsn (stntonat m i))
  in
  let g = fun i ->
    natgthtogehsn (d i) O
      (minusgth0 (f (dni_firstelement m i)) (f (dni_lastelement m i)) (f0 i))
  in
  let h = stnsum_ge1 m d g in
  let h0 =
    internal_paths_rew (stnsum m d) h
      (sub (f (lastelement m)) (f (firstelement m))) e
  in
  let i = Obj.magic inc (firstelement m) (lastelement m) Coq_paths_refl in
  let j = minusplusnmm (f (lastelement m)) (f (firstelement m)) i in
  internal_paths_rew
    (add (sub (f (lastelement m)) (f (firstelement m))) (f (firstelement m)))
    (internal_paths_rew_r
      (add (sub (f (lastelement m)) (f (firstelement m)))
        (f (firstelement m)))
      (add (f (firstelement m))
        (sub (f (lastelement m)) (f (firstelement m))))
      (natgehandplusl (sub (f (lastelement m)) (f (firstelement m))) m
        (f (firstelement m)) h0)
      (natpluscomm (sub (f (lastelement m)) (f (firstelement m)))
        (f (firstelement m)))) (f (lastelement m)) j

(** val stn_ord_inj :
    nat -> (stn, stn) incl -> (stn -> stn -> hProptoType -> hProptoType) ->
    stn -> stn paths **)

let stn_ord_inj n f inc i =
  match n with
  | O -> fromempty (negstn0 i)
  | S n0 ->
    let strincr =
      is_incr_impl_strincr (S n0) (fun x -> stntonat (S n0) (pr1incl f x))
        (isinclcomp f (stntonat_incl (S n0))) inc
    in
    let m =
      isantisymmnatgeh (stntonat (S n0) (pr1incl f (lastelement n0))) n0
        (let n1 =
           stn_ord_incl n0 (fun x -> stntonat (S n0) (pr1incl f x)) strincr
         in
         istransnatgeh (stntonat (S n0) (pr1incl f (lastelement n0)))
           (add (stntonat (S n0) (pr1incl f (firstelement n0))) n0) n0 n1
           (natgehplusnmm (stntonat (S n0) (pr1incl f (firstelement n0))) n0))
        (stnlt (S n0) (pr1incl f (lastelement n0)))
    in
    subtypePath_prop (fun x -> natlth x (S n0)) (pr1incl f i) i
      (let c =
         natgehchoice (stntonat (S n0) (lastelement n0)) (stntonat (S n0) i)
           (lastelement_ge n0 i)
       in
       match c with
       | Coq_ii1 a ->
         maponpaths (stntonat (S n0)) (pr1incl f i)
           (pr1incl f
             (dni n0 (lastelement n0) (make_stn n0 (stntonat (S n0) i) a)))
           (maponpaths (pr1incl f) i
             (dni n0 (lastelement n0) (make_stn n0 (stntonat (S n0) i) a))
             (pathsinv0
               (dni n0 (lastelement n0) (make_stn n0 (stntonat (S n0) i) a))
               i
               (subtypePath_prop (fun x -> natlth x (S n0))
                 (dni n0 (lastelement n0) (make_stn n0 (stntonat (S n0) i) a))
                 i (dni_last n0 (make_stn n0 (stntonat (S n0) i) a)))))
       | Coq_ii2 b ->
         let eq =
           subtypePath_prop (fun m0 -> natlth m0 (S n0)) (lastelement n0) i b
         in
         internal_paths_rew (lastelement n0) m i eq)

(** val stn_ord_bij :
    nat -> (stn, stn) weq -> (stn -> stn -> hProptoType -> hProptoType) ->
    stn -> stn paths **)

let stn_ord_bij n f =
  stn_ord_inj n (weqtoincl f)

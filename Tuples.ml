open NaturalNumbers
open PartA
open Preamble
open Propositions
open StandardFiniteSets
open UnivalenceAxiom

(** val stnweq : nat -> ((stn, coq_unit) coprod, stn) weq **)

let stnweq n =
  weqdnicoprod n (lastelement n)

(** val extend_tuple : nat -> (stn -> 'a1) -> 'a1 -> stn -> 'a1 **)

let extend_tuple n f last i =
  let c = invmap (stnweq n) i in
  (match c with
   | Coq_ii1 a -> f a
   | Coq_ii2 _ -> last)

(** val extend_tuple_dep :
    nat -> (stn -> 'a1) -> 'a1 -> (stn -> 'a2) -> 'a2 -> stn -> 'a2 **)

let extend_tuple_dep n _ _ af alast i =
  let c = invmap (stnweq n) i in
  (match c with
   | Coq_ii1 a -> af a
   | Coq_ii2 _ -> alast)

(** val extend_tuple_dep_const :
    nat -> (stn -> 'a1) -> 'a1 -> (stn -> 'a2) -> 'a2 -> (stn -> 'a2) paths **)

let extend_tuple_dep_const n f last af al =
  Obj.magic funextsec (extend_tuple_dep n f last af al)
    (extend_tuple n af al) (fun _ -> Coq_paths_refl)

(** val extend_tuple_i :
    nat -> (stn -> 'a1) -> 'a1 -> nat -> hProptoType -> hProptoType -> 'a1
    paths **)

let extend_tuple_i n f last i hi1 hi2 =
  maponpaths (fun c -> match c with
                       | Coq_ii1 a -> f a
                       | Coq_ii2 _ -> last)
    (invmap (stnweq n) { pr1 = i; pr2 = hi1 }) (Coq_ii1 (make_stn n i hi2))
    (invmaponpathsweq (weqdnicoprod n (lastelement n))
      (invmap (stnweq n) { pr1 = i; pr2 = hi1 }) (Coq_ii1 (make_stn n i hi2))
      (pathscomp0
        (pr1weq (weqdnicoprod n (lastelement n))
          (invmap (weqdnicoprod n (lastelement n)) { pr1 = i; pr2 = hi1 }))
        { pr1 = i; pr2 = hi1 }
        (pr1weq (weqdnicoprod n (lastelement n)) (Coq_ii1 (make_stn n i hi2)))
        (homotweqinvweq (weqdnicoprod n (lastelement n)) { pr1 = i; pr2 =
          hi1 })
        (stn_eq (S n) { pr1 = i; pr2 = hi1 }
          (pr1weq (weqdnicoprod n (lastelement n)) (Coq_ii1
            (make_stn n i hi2)))
          (pathsinv0 (di (stntonat (S n) (lastelement n)) i) i
            (di_eq1 (stntonat (S n) (lastelement n)) i hi2)))))

(** val extend_tuple_last :
    nat -> (stn -> 'a1) -> 'a1 -> stn -> nat paths -> 'a1 paths **)

let extend_tuple_last n f last i hi =
  maponpaths (fun c -> match c with
                       | Coq_ii1 a -> f a
                       | Coq_ii2 _ -> last) (invmap (stnweq n) i) (Coq_ii2
    Coq_tt)
    (invmaponpathsweq (weqdnicoprod n (lastelement n)) (invmap (stnweq n) i)
      (Coq_ii2 Coq_tt)
      (pathscomp0
        (pr1weq (weqdnicoprod n (lastelement n))
          (invmap (weqdnicoprod n (lastelement n)) i)) i
        (pr1weq (weqdnicoprod n (lastelement n)) (Coq_ii2 Coq_tt))
        (homotweqinvweq (weqdnicoprod n (lastelement n)) i)
        (stn_eq (S n) i
          (pr1weq (weqdnicoprod n (lastelement n)) (Coq_ii2 Coq_tt)) hi)))

(** val extend_tuple_inl : nat -> (stn -> 'a1) -> 'a1 -> stn -> 'a1 paths **)

let extend_tuple_inl n f last i =
  maponpaths (fun c -> match c with
                       | Coq_ii1 a -> f a
                       | Coq_ii2 _ -> last)
    (invmap (stnweq n) (pr1weq (stnweq n) (Coq_ii1 i))) (Coq_ii1 i)
    (homotinvweqweq (stnweq n) (Coq_ii1 i))

(** val extend_tuple_inr : nat -> (stn -> 'a1) -> 'a1 -> 'a1 paths **)

let extend_tuple_inr n f last =
  maponpaths (fun c -> match c with
                       | Coq_ii1 a -> f a
                       | Coq_ii2 _ -> last)
    (invmap (stnweq n) (pr1weq (stnweq n) (Coq_ii2 Coq_tt))) (Coq_ii2 Coq_tt)
    (homotinvweqweq (stnweq n) (Coq_ii2 Coq_tt))

(** val extend_tuple_eq :
    nat -> 'a1 -> (stn -> 'a1) -> (stn -> 'a1) -> (stn -> 'a1 paths) -> 'a1
    paths -> (stn -> 'a1) paths **)

let extend_tuple_eq n last f g hf hlast =
  Obj.magic funextfun (extend_tuple n f last) g (fun i ->
    pathscomp0
      (match invmap (Obj.magic stnweq n) i with
       | Coq_ii1 a -> Obj.magic f a
       | Coq_ii2 _ -> Obj.magic last)
      (Obj.magic g (pr1weq (stnweq n) (invmap (Obj.magic stnweq n) i)))
      (Obj.magic g i)
      (let c = invmap (Obj.magic stnweq n) i in
       match c with
       | Coq_ii1 a -> Obj.magic hf a
       | Coq_ii2 _ -> Obj.magic hlast)
      (maponpaths (Obj.magic g)
        (pr1weq (Obj.magic stnweq n) (invmap (Obj.magic stnweq n) i)) i
        (homotweqinvweq (Obj.magic stnweq n) i)))

open DecidablePropositions
open PartA
open PartB
open PartC
open Preamble
open Propositions
open Sets
open Sets0

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val pr1_issurjective :
    ('a1 -> hProptoType) -> (('a1, 'a2) total2, 'a1) issurjective **)

let pr1_issurjective ne x =
  hinhuniv ishinh (fun p ->
    hinhpr { pr1 = { pr1 = x; pr2 = p }; pr2 = Coq_paths_refl }) (ne x)

(** val eqrel_on_bool : hProp -> pr1hSet eqrel **)

let eqrel_on_bool p =
  let ifb = fun f f0 b -> match b with
                          | Coq_true -> f
                          | Coq_false -> f0 in
  { pr1 = (fun x y ->
  Obj.magic ifb (Obj.magic ifb htrue p y) (Obj.magic ifb p htrue y) x); pr2 =
  { pr1 = { pr1 = (fun x y z a b ->
  match Obj.magic x with
  | Coq_true ->
    (match Obj.magic z with
     | Coq_true -> Obj.magic Coq_tt
     | Coq_false -> (match Obj.magic y with
                     | Coq_true -> b
                     | Coq_false -> a))
  | Coq_false ->
    (match Obj.magic z with
     | Coq_true -> (match Obj.magic y with
                    | Coq_true -> a
                    | Coq_false -> b)
     | Coq_false -> Obj.magic Coq_tt)); pr2 = (fun _ -> Obj.magic Coq_tt) };
  pr2 = (fun _ _ a -> a) } }

(** val eqrel_on_bool_iff :
    hProp -> (pr1hSet setquot paths, hProptoType) logeq **)

let eqrel_on_bool_iff p =
  let e = eqrel_on_bool p in
  { pr1 = (fun q ->
  invmap (weqpathsinsetquot e (Obj.magic Coq_true) (Obj.magic Coq_false)) q);
  pr2 = (fun p0 ->
  iscompsetquotpr e (Obj.magic Coq_true) (Obj.magic Coq_false) p0) }

(** val coq_AxiomOfChoice : hProp **)

let coq_AxiomOfChoice =
  forall_hProp (fun _ -> ischoicebase)

(** val coq_AxiomOfChoice_surj : hProp **)

let coq_AxiomOfChoice_surj =
  forall_hProp (fun _ ->
    forall_hProp (fun _ -> forall_hProp (fun _ -> himpl ishinh)))

(** val coq_AC_impl2 : (hProptoType, hProptoType) logeq **)

let coq_AC_impl2 =
  { pr1 = (fun aC ->
    Obj.magic (fun x _ f surj ->
      squash_to_prop (Obj.magic aC x __ surj) (propproperty ishinh) (fun s ->
        hinhpr { pr1 = (fun y -> hfiberpr1 f y (s y)); pr2 = (fun y ->
          hfiberpr2 f y (s y)) }))); pr2 = (fun aC ->
    Obj.magic (fun x _ ne ->
      hinhuniv ishinh (fun sec -> hinhpr (fun x0 -> (sec.pr1 x0).pr2))
        (Obj.magic aC x __ (fun t -> t.pr1) (pr1_issurjective ne)))) }

(** val coq_SetCovering : hProptoType -> hProptoType **)


(** val coq_AC_to_LEM : hProptoType -> hProptoType **)

let coq_AC_to_LEM aC =
  Obj.magic (fun p ->
    let f = setquotpr (eqrel_on_bool p) in
    let q =
      (Obj.magic coq_AC_impl2).pr1 aC
        (setquotinset (pr1eqrel (eqrel_on_bool p))) __ f
        (issurjsetquotpr (eqrel_on_bool p))
    in
    squash_to_prop q (isapropdec (propproperty p)) (fun sec ->
      let g = sec.pr1 in
      let h = sec.pr2 in
      logeq_dec (Obj.magic eqrel_on_bool_iff p)
        (retract_dec (Obj.magic f) g h isdeceqbool
          (setquotpr (Obj.magic eqrel_on_bool p) Coq_true)
          (setquotpr (Obj.magic eqrel_on_bool p) Coq_false))))

(** val coq_AxiomOfDecidableChoice : hProp **)

let coq_AxiomOfDecidableChoice =
  forall_hProp (fun _ -> himpl ischoicebase)

(** val coq_AC_iff_ADC_and_LEM : hProptoType **)

let coq_AC_iff_ADC_and_LEM =
  Obj.magic { pr1 = (fun aC -> { pr1 = (fun _ i ->
    Obj.magic aC (make_hSet (isasetifdeceq i))); pr2 = (coq_AC_to_LEM aC) });
    pr2 = (fun x0 ->
    let adc = x0.pr1 in
    let lem = x0.pr2 in (fun x -> adc __ (fun x1 y -> lem (eqset x x1 y)))) }

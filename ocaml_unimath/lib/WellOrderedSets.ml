open AxiomOfChoice
open Notations
open OrderedSets
open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Propositions0
open Sets
open Sets0
open Subtypes
open UnivalenceAxiom

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_TotalOrdering : hSet -> hSet **)


(** val coq_TOSubset_set : hSet -> hSet **)

let coq_TOSubset_set x = x
  (* total2_hSet subtype_set (fun s -> *)
  (*   coq_TotalOrdering (carrier_subset x (Obj.magic s))) *)

type coq_TOSubset = pr1hSet

(** val coq_TOSubset_to_subtype : hSet -> coq_TOSubset -> pr1hSet hsubtype **)

let coq_TOSubset_to_subtype _ =
  Obj.magic (fun t -> t.pr1)

(** val coq_TOSrel : hSet -> coq_TOSubset -> pr1hSet hrel **)

let coq_TOSrel _ s =
  (Obj.magic s).pr2.pr1

(** val coq_TOtotal : hSet -> coq_TOSubset -> hProptoType **)

let coq_TOtotal _ s =
  (Obj.magic s).pr2.pr2

(** val coq_TOtot : hSet -> coq_TOSubset -> pr1hSet istotal **)

let coq_TOtot _ s =
  (Obj.magic s).pr2.pr2.pr2

(** val coq_TOanti : hSet -> coq_TOSubset -> pr1hSet isantisymm **)

let coq_TOanti _ s =
  (Obj.magic s).pr2.pr2.pr1.pr2

(** val coq_TOrefl : hSet -> coq_TOSubset -> pr1hSet isrefl **)

let coq_TOrefl _ s =
  (Obj.magic s).pr2.pr2.pr1.pr1.pr2

(** val coq_TOeq_to_refl : hSet -> coq_TOSubset -> hProptoType **)

let coq_TOeq_to_refl x s = x
  (* Obj.magic (fun s0 _ _ -> coq_TOrefl x s s0) *)

(** val coq_TOeq_to_refl_1 : hSet -> coq_TOSubset -> hProptoType **)

let coq_TOeq_to_refl_1 x s =
  Obj.magic (fun s0 _ _ -> coq_TOrefl x s (Obj.magic s0))

(** val coq_TOtrans : hSet -> coq_TOSubset -> pr1hSet istrans **)

let coq_TOtrans _ s =
  let x0 = (Obj.magic s).pr2.pr2 in
  let x1 = x0.pr1 in let x2 = x1.pr1 in x2.pr1

(** val h1'' :
    hSet -> coq_TOSubset -> pr1hSet carrier -> pr1hSet carrier -> pr1hSet
    carrier -> pr1hSet carrier -> hProptoType -> pr1hSet paths -> pr1hSet
    paths -> hProptoType **)

let h1'' _ _ _ _ _ _ le _ _ =
  le

(** val tosub_order_compat :
    hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType -> hProp **)

let tosub_order_compat x s t le =
  forall_hProp (fun s0 ->
    forall_hProp (fun s' ->
      himpl
        (coq_TOSrel x t
          (Obj.magic subtype_inc (coq_TOSubset_to_subtype x s)
            (coq_TOSubset_to_subtype x t) le s0)
          (Obj.magic subtype_inc (coq_TOSubset_to_subtype x s)
            (coq_TOSubset_to_subtype x t) le s'))))

(** val tosub_le : hSet -> coq_TOSubset -> coq_TOSubset -> hProp **)

let tosub_le x s t =
  total2_hProp
    (subtype_containedIn (Obj.magic coq_TOSubset_to_subtype x s)
      (Obj.magic coq_TOSubset_to_subtype x t)) (fun le ->
    tosub_order_compat x s t le)

(** val sub_initial :
    hSet -> pr1hSet hsubtype -> coq_TOSubset -> hProptoType -> hProp **)

let sub_initial _ s _ _ =
  forall_hProp (fun _ ->
    forall_hProp (fun t ->
      forall_hProp (fun _ -> forall_hProp (fun _ -> himpl (s t)))))

(** val same_induced_ordering :
    hSet -> coq_TOSubset -> coq_TOSubset -> pr1hSet hsubtype -> hProptoType
    -> hProptoType -> hProp **)

let same_induced_ordering x s t b bS bT =
  forall_hProp (fun x0 ->
    forall_hProp (fun y ->
      hequiv
        (coq_TOSrel x s
          (Obj.magic subtype_inc b (coq_TOSubset_to_subtype x s) bS x0)
          (Obj.magic subtype_inc b (coq_TOSubset_to_subtype x s) bS y))
        (coq_TOSrel x t
          (Obj.magic subtype_inc b (coq_TOSubset_to_subtype x t) bT x0)
          (Obj.magic subtype_inc b (coq_TOSubset_to_subtype x t) bT y))))

(** val common_initial :
    hSet -> pr1hSet hsubtype -> coq_TOSubset -> coq_TOSubset -> hProp **)

let common_initial x b s t =
  total2_hProp
    (subtype_containedIn (Obj.magic b)
      (Obj.magic coq_TOSubset_to_subtype x s)) (fun bS ->
    total2_hProp
      (subtype_containedIn (Obj.magic b)
        (Obj.magic coq_TOSubset_to_subtype x t)) (fun bT ->
      hconj (sub_initial x b s bS)
        (hconj (sub_initial x b t bT) (same_induced_ordering x s t b bS bT))))

(** val max_common_initial :
    hSet -> coq_TOSubset -> coq_TOSubset -> pr1hSet hsubtype **)

let max_common_initial _ _ _ _ =
  ishinh

(** val max_common_initial_is_max :
    hSet -> coq_TOSubset -> coq_TOSubset -> pr1hSet hsubtype -> hProptoType
    -> hProptoType **)

let max_common_initial_is_max _ _ _ a c =
  Obj.magic (fun _ ax -> hinhpr { pr1 = a; pr2 = { pr1 = ax; pr2 = c } })

(** val max_common_initial_is_sub :
    hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType **)


(** val max_common_initial_is_common_initial :
    hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType **)


(** val tosub_fidelity :
    hSet -> coq_TOSubset -> coq_TOSubset -> hProptoType -> pr1hSet carrier ->
    pr1hSet carrier -> hProptoType **)

let squash_to_hProp q h f =  q f h

let tosub_fidelity x s t le s0 s' =
  Obj.magic { pr1 = ((Obj.magic le).pr2 s0 s'); pr2 = (fun l ->
    squash_to_hProp (coq_TOSrel x s (Obj.magic s0) (Obj.magic s'))
      (coq_TOtot x s (Obj.magic s0) (Obj.magic s')) (fun x0 ->
      match x0 with
      | Coq_ii1 h -> h
      | Coq_ii2 h ->
        Obj.magic coq_TOeq_to_refl x s s0 s'
          (let k = (Obj.magic le).pr2 s' s0 h in
           let k' =
             coq_TOanti x t
               (Obj.magic subtype_inc (coq_TOSubset_to_subtype x s)
                 (coq_TOSubset_to_subtype x t) (Obj.magic le).pr1 s0)
               (Obj.magic subtype_inc (coq_TOSubset_to_subtype x s)
                 (coq_TOSubset_to_subtype x t) (Obj.magic le).pr1 s') l k
           in
           subtypePath_prop (coq_TOSubset_to_subtype x s) s0 s'
             (maponpaths (Obj.magic (fun t0 -> t0.pr1))
               (Obj.magic subtype_inc (coq_TOSubset_to_subtype x s)
                 (coq_TOSubset_to_subtype x t) (Obj.magic le).pr1 s0)
               (Obj.magic subtype_inc (coq_TOSubset_to_subtype x s)
                 (coq_TOSubset_to_subtype x t) (Obj.magic le).pr1 s') k')))) }

(** val coq_TOSubset_plus_point_rel :
    hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> pr1hSet hrel **)

let coq_TOSubset_plus_point_rel x s _ nSz x0 = x
  (* let s0 = (Obj.magic x0).pr1 in *)
  (* let i = (Obj.magic x0).pr2 in *)
  (* (fun x1 -> *)
  (* let t = (Obj.magic x1).pr1 in *)
  (* let j = (Obj.magic x1).pr2 in *)
  (* Obj.magic squash_to_hSet_2' hPropset (fun x2 x3 -> *)
  (*   match x2 with *)
  (*   | Coq_ii1 h -> *)
  (*     (match x3 with *)
  (*      | Coq_ii1 h0 -> *)
  (*        Obj.magic coq_TOSrel x s { pr1 = s0; pr2 = h } { pr1 = t; pr2 = h0 } *)
  (*      | Coq_ii2 _ -> Obj.magic htrue) *)
  (*   | Coq_ii2 _ -> *)
  (*     (match x3 with *)
  (*      | Coq_ii1 _ -> Obj.magic hfalse *)
  (*      | Coq_ii2 _ -> Obj.magic htrue)) { pr1 = (fun x2 x3 x4 -> *)
  (*   match x2 with *)
  (*   | Coq_ii1 h -> *)
  (*     (match x3 with *)
  (*      | Coq_ii1 _ -> *)
  (*        (match x4 with *)
  (*         | Coq_ii1 h0 -> *)
  (*           pathsinv0 *)
  (*             (coq_TOSrel x s (Obj.magic { pr1 = s0; pr2 = h }) *)
  (*               (Obj.magic { pr1 = t; pr2 = h0 })) *)
  (*             (coq_TOSrel x s (Obj.magic { pr1 = s0; pr2 = h }) *)
  (*               (Obj.magic { pr1 = t; pr2 = h0 })) Coq_paths_refl *)
  (*         | Coq_ii2 _ -> Coq_paths_refl) *)
  (*      | Coq_ii2 _ -> *)
  (*        (match x4 with *)
  (*         | Coq_ii1 _ -> fromempty (Obj.magic nSz h) *)
  (*         | Coq_ii2 _ -> Coq_paths_refl)) *)
  (*   | Coq_ii2 _ -> *)
  (*     (match x3 with *)
  (*      | Coq_ii1 h -> *)
  (*        (match x4 with *)
  (*         | Coq_ii1 _ -> fromempty (Obj.magic nSz h) *)
  (*         | Coq_ii2 _ -> Coq_paths_refl) *)
  (*      | Coq_ii2 _ -> Coq_paths_refl)); pr2 = (fun x2 x3 x4 -> *)
  (*   match x2 with *)
  (*   | Coq_ii1 h -> *)
  (*     (match x3 with *)
  (*      | Coq_ii1 h0 -> *)
  (*        (match x4 with *)
  (*         | Coq_ii1 _ -> *)
  (*           pathsinv0 *)
  (*             (coq_TOSrel x s (Obj.magic { pr1 = s0; pr2 = h }) *)
  (*               (Obj.magic { pr1 = t; pr2 = h0 })) *)
  (*             (coq_TOSrel x s (Obj.magic { pr1 = s0; pr2 = h }) *)
  (*               (Obj.magic { pr1 = t; pr2 = h0 })) Coq_paths_refl *)
  (*         | Coq_ii2 _ -> fromempty (Obj.magic nSz h0)) *)
  (*      | Coq_ii2 _ -> *)
  (*        (match x4 with *)
  (*         | Coq_ii1 h0 -> fromempty (Obj.magic nSz h0) *)
  (*         | Coq_ii2 _ -> Coq_paths_refl)) *)
  (*   | Coq_ii2 _ -> *)
  (*     (match x3 with *)
  (*      | Coq_ii1 h -> *)
  (*        (match x4 with *)
  (*         | Coq_ii1 _ -> Coq_paths_refl *)
  (*         | Coq_ii2 _ -> fromempty (Obj.magic nSz h)) *)
  (*      | Coq_ii2 _ -> *)
  (*        (match x4 with *)
  (*         | Coq_ii1 h -> fromempty (Obj.magic nSz h) *)
  (*         | Coq_ii2 _ -> Coq_paths_refl))) } i j) *)

(** val isTotalOrder_TOSubset_plus_point :
    hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType **)

let isTotalOrder_TOSubset_plus_point x s z nSz = x s z nSz 
  (* Obj.magic { pr1 = { pr1 = { pr1 = (fun x1 -> *)
  (*   let w = x1.pr1 in *)
  (*   let ww = x1.pr2 in *)
  (*   (fun x2 -> *)
  (*   let x0 = x2.pr1 in *)
  (*   let wx = x2.pr2 in *)
  (*   (fun x3 -> *)
  (*   let y = x3.pr1 in *)
  (*   let wy = x3.pr2 in *)
  (*   (fun wx0 xy -> *)
  (*   squash_to_hProp *)
  (*     (coq_TOSubset_plus_point_rel x s z nSz *)
  (*       (Obj.magic { pr1 = w; pr2 = ww }) (Obj.magic { pr1 = y; pr2 = wy })) *)
  (*     wy (fun x4 -> *)
  (*     match x4 with *)
  (*     | Coq_ii1 h -> *)
  (*       squash_to_hProp *)
  (*         (coq_TOSubset_plus_point_rel x s z nSz *)
  (*           (Obj.magic { pr1 = w; pr2 = ww }) *)
  (*           (Obj.magic { pr1 = y; pr2 = (hinhpr (Coq_ii1 h)) })) ww *)
  (*         (fun x5 -> *)
  (*         match x5 with *)
  (*         | Coq_ii1 h0 -> *)
  (*           squash_to_hProp *)
  (*             (coq_TOSubset_plus_point_rel x s z nSz *)
  (*               (Obj.magic { pr1 = w; pr2 = (hinhpr (Coq_ii1 h0)) }) *)
  (*               (Obj.magic { pr1 = y; pr2 = (hinhpr (Coq_ii1 h)) })) wx *)
  (*             (fun x6 -> *)
  (*             match x6 with *)
  (*             | Coq_ii1 h2 -> *)
  (*               coq_TOtrans x s (Obj.magic { pr1 = w; pr2 = h0 }) *)
  (*                 (Obj.magic { pr1 = x0; pr2 = h2 }) *)
  (*                 (Obj.magic { pr1 = y; pr2 = h }) wx0 xy *)
  (*             | Coq_ii2 _ -> fromempty (Obj.magic xy)) *)
  (*         | Coq_ii2 _ -> *)
  (*           squash_to_hProp hfalse wx (fun x6 -> *)
  (*             match x6 with *)
  (*             | Coq_ii1 _ -> wx0 *)
  (*             | Coq_ii2 _ -> xy)) *)
  (*     | Coq_ii2 _ -> *)
  (*       squash_to_hProp *)
  (*         (coq_TOSubset_plus_point_rel x s z nSz *)
  (*           (Obj.magic { pr1 = w; pr2 = ww }) *)
  (*           (Obj.magic { pr1 = z; pr2 = wy })) ww (fun _ -> Obj.magic Coq_tt)))))); *)
  (*   pr2 = (fun x0 -> *)
  (*   let x1 = x0.pr1 in *)
  (*   let wx = x0.pr2 in *)
  (*   squash_to_hProp *)
  (*     (coq_TOSubset_plus_point_rel x s z nSz *)
  (*       (Obj.magic { pr1 = x1; pr2 = wx }) (Obj.magic { pr1 = x1; pr2 = wx })) *)
  (*     wx (fun x2 -> *)
  (*     match x2 with *)
  (*     | Coq_ii1 h -> coq_TOrefl x s (Obj.magic { pr1 = x1; pr2 = h }) *)
  (*     | Coq_ii2 _ -> Obj.magic Coq_tt)) }; pr2 = (fun x1 -> *)
  (*   let x0 = x1.pr1 in *)
  (*   let wx = x1.pr2 in *)
  (*   (fun x2 -> *)
  (*   let y = x2.pr1 in *)
  (*   let wy = x2.pr2 in *)
  (*   (fun xy yx -> *)
  (*   eqset_to_path *)
  (*     (carrier_subset x (subtype_plus (coq_TOSubset_to_subtype x s) z)) *)
  (*     (Obj.magic { pr1 = x0; pr2 = wx }) (Obj.magic { pr1 = y; pr2 = wy }) *)
  (*     (squash_to_hProp *)
  (*       (eqset *)
  (*         (carrier_subset x (subtype_plus (coq_TOSubset_to_subtype x s) z)) *)
  (*         (Obj.magic { pr1 = x0; pr2 = wx }) *)
  (*         (Obj.magic { pr1 = y; pr2 = wy })) wx (fun x3 -> *)
  (*       match x3 with *)
  (*       | Coq_ii1 h -> *)
  (*         squash_to_hProp *)
  (*           (eqset *)
  (*             (carrier_subset x *)
  (*               (subtype_plus (coq_TOSubset_to_subtype x s) z)) *)
  (*             (Obj.magic { pr1 = x0; pr2 = (hinhpr (Coq_ii1 h)) }) *)
  (*             (Obj.magic { pr1 = y; pr2 = wy })) wy (fun x4 -> *)
  (*           match x4 with *)
  (*           | Coq_ii1 h0 -> *)
  (*             Obj.magic subtypePath_prop *)
  (*               (subtype_plus (coq_TOSubset_to_subtype x s) z) { pr1 = x0; *)
  (*               pr2 = (hinhpr (Coq_ii1 h)) } { pr1 = y; pr2 = *)
  (*               (hinhpr (Coq_ii1 h0)) } *)
  (*               (maponpaths (Obj.magic (fun t -> t.pr1)) *)
  (*                 (Obj.magic { pr1 = x0; pr2 = h }) *)
  (*                 (Obj.magic { pr1 = y; pr2 = h0 }) *)
  (*                 (coq_TOanti x s (Obj.magic { pr1 = x0; pr2 = h }) *)
  (*                   (Obj.magic { pr1 = y; pr2 = h0 }) xy yx)) *)
  (*           | Coq_ii2 _ -> *)
  (*             Obj.magic subtypePath_prop *)
  (*               (subtype_plus (coq_TOSubset_to_subtype x s) z) { pr1 = x0; *)
  (*               pr2 = (hinhpr (Coq_ii1 h)) } { pr1 = z; pr2 = *)
  (*               (hinhpr (Coq_ii2 Coq_paths_refl)) } (fromempty (Obj.magic yx))) *)
  (*       | Coq_ii2 _ -> *)
  (*         squash_to_hProp *)
  (*           (eqset *)
  (*             (carrier_subset x *)
  (*               (subtype_plus (coq_TOSubset_to_subtype x s) z)) *)
  (*             (Obj.magic { pr1 = z; pr2 = (hinhpr (Coq_ii2 Coq_paths_refl)) }) *)
  (*             (Obj.magic { pr1 = y; pr2 = wy })) wy (fun x4 -> *)
  (*           match x4 with *)
  (*           | Coq_ii1 h -> *)
  (*             Obj.magic subtypePath_prop *)
  (*               (subtype_plus (coq_TOSubset_to_subtype x s) z) { pr1 = z; *)
  (*               pr2 = (hinhpr (Coq_ii2 Coq_paths_refl)) } { pr1 = y; pr2 = *)
  (*               (hinhpr (Coq_ii1 h)) } (fromempty (Obj.magic xy)) *)
  (*           | Coq_ii2 _ -> *)
  (*             Obj.magic subtypePath_prop *)
  (*               (subtype_plus (coq_TOSubset_to_subtype x s) z) { pr1 = z; *)
  (*               pr2 = (hinhpr (Coq_ii2 Coq_paths_refl)) } { pr1 = z; pr2 = *)
  (*               wy } Coq_paths_refl)))))) }; pr2 = (fun x1 -> *)
  (*   let x0 = x1.pr1 in *)
  (*   let wx = x1.pr2 in *)
  (*   (fun x2 -> *)
  (*   let y = x2.pr1 in *)
  (*   let wy = x2.pr2 in *)
  (*   squash_to_hProp hdisj wx (fun x3 -> *)
  (*     match x3 with *)
  (*     | Coq_ii1 h -> *)
  (*       squash_to_hProp hdisj wy (fun x4 -> *)
  (*         match x4 with *)
  (*         | Coq_ii1 h0 -> *)
  (*           hinhfun (fun x5 -> *)
  (*             match x5 with *)
  (*             | Coq_ii1 h2 -> Coq_ii1 h2 *)
  (*             | Coq_ii2 h2 -> Coq_ii2 h2) *)
  (*             (coq_TOtot x s (Obj.magic { pr1 = x0; pr2 = h }) *)
  (*               (Obj.magic { pr1 = y; pr2 = h0 })) *)
  (*         | Coq_ii2 _ -> hinhpr (Coq_ii1 Coq_tt)) *)
  (*     | Coq_ii2 _ -> *)
  (*       squash_to_hProp hdisj wy (fun x4 -> *)
  (*         match x4 with *)
  (*         | Coq_ii1 _ -> hinhpr (Coq_ii2 Coq_tt) *)
  (*         | Coq_ii2 _ -> hinhpr (Coq_ii2 Coq_tt))))) } *)

(** val coq_TOSubset_plus_point :
    hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> coq_TOSubset **)

let coq_TOSubset_plus_point x s z nSz =
  Obj.magic { pr1 = (subtype_plus (coq_TOSubset_to_subtype x s) z); pr2 =
    { pr1 = (coq_TOSubset_plus_point_rel x s z nSz); pr2 =
    (isTotalOrder_TOSubset_plus_point x s z nSz) } }

(** val coq_TOSubset_plus_point_incl :
    hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType **)

let coq_TOSubset_plus_point_incl x s z _ =
  subtype_plus_incl (coq_TOSubset_to_subtype x s) z

(** val coq_TOSubset_plus_point_le :
    hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType **)

let coq_TOSubset_plus_point_le x s z nSz =
  Obj.magic { pr1 = (coq_TOSubset_plus_point_incl x s z nSz); pr2 =
    (fun _ _ le -> le) }

(** val coq_TOSubset_plus_point_initial :
    hSet -> coq_TOSubset -> pr1hSet -> hProptoType -> hProptoType **)

let coq_TOSubset_plus_point_initial x s _ _ =
  Obj.magic (fun _ t _ tt le ->
    squash_to_hProp (coq_TOSubset_to_subtype x s t) tt (fun x0 ->
      match x0 with
      | Coq_ii1 h -> h
      | Coq_ii2 _ -> fromempty le))

(** val hasSmallest : 'a1 hrel -> hProp **)

let hasSmallest _ =
  forall_hProp (fun _ -> himpl ishinh)

(** val isWellOrder : hSet -> pr1hSet hrel -> hProp **)

let isWellOrder x r =
  hconj (isTotalOrder x r) (hasSmallest r)

(** val coq_WellOrdering : hSet -> hSet **)


(** val coq_WOSubset_set : hSet -> hSet **)

let coq_WOSubset_set x = x
  (* total2_hSet subtype_set (fun s -> *)
  (*   coq_WellOrdering (carrier_subset x (Obj.magic s))) *)

type coq_WOSubset = pr1hSet

(** val coq_WOSubset_to_subtype : hSet -> coq_WOSubset -> pr1hSet hsubtype **)

let coq_WOSubset_to_subtype _ =
  Obj.magic (fun t -> t.pr1)

(** val coq_WOSrel : hSet -> coq_WOSubset -> pr1hSet hrel **)

let coq_WOSrel _ s =
  (Obj.magic s).pr2.pr1

(** val coq_WOStotal : hSet -> coq_WOSubset -> hProptoType **)

let coq_WOStotal _ s =
  (Obj.magic s).pr2.pr2.pr1

(** val coq_WOSubset_to_TOSubset : hSet -> coq_WOSubset -> coq_TOSubset **)

let coq_WOSubset_to_TOSubset x s =
  Obj.magic { pr1 = (coq_WOSubset_to_subtype x s); pr2 = { pr1 =
    (coq_WOSrel x s); pr2 = (coq_WOStotal x s) } }

(** val coq_WOSwo : hSet -> coq_WOSubset -> pr1hSet **)

let coq_WOSwo _ s =
  (Obj.magic s).pr2

(** val lt :
    hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet carrier -> hProp **)

let lt _ _ _ _ =
  hneg

(** val coq_WOS_hasSmallest : hSet -> coq_WOSubset -> hProptoType **)

let coq_WOS_hasSmallest _ s =
  (Obj.magic s).pr2.pr2.pr2

(** val wo_lt_to_le :
    hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet carrier -> hProptoType
    -> hProptoType **)

let wo_lt_to_le x s s0 s' lt0 =
  squash_to_hProp (coq_WOSrel x s (Obj.magic s0) (Obj.magic s'))
    (coq_TOtot x (coq_WOSubset_to_TOSubset x s) (Obj.magic s0) (Obj.magic s'))
    (fun x0 ->
    match x0 with
    | Coq_ii1 h -> h
    | Coq_ii2 h -> fromempty (Obj.magic lt0 h))

(** val wosub_le : hSet -> coq_WOSubset hrel **)

let wosub_le x s t =
  total2_hProp
    (subtype_containedIn
      (Obj.magic coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s))
      (Obj.magic coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)))
    (fun le ->
    hconj
      (tosub_order_compat x (coq_WOSubset_to_TOSubset x s)
        (coq_WOSubset_to_TOSubset x t) le)
      (sub_initial x
        (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s))
        (coq_WOSubset_to_TOSubset x t) le))

(** val wosub_le_inc :
    hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> hProptoType **)

let wosub_le_inc _ _ _ =
  Obj.magic (fun t -> t.pr1)

(** val wosub_le_comp :
    hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> hProptoType **)

let wosub_le_comp _ _ _ le =
  (Obj.magic le).pr2.pr1

(** val wosub_le_subi :
    hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> hProptoType **)

let wosub_le_subi _ _ _ le =
  (Obj.magic le).pr2.pr2

(** val wosub_le_isrefl : hSet -> coq_WOSubset isrefl **)

let wosub_le_isrefl _ _ =
  Obj.magic { pr1 = (fun _ xinS -> xinS); pr2 = { pr1 = (fun _ _ le -> le);
    pr2 = (fun _ _ _ ss' _ -> ss') } }

(** val wosub_equal : hSet -> coq_WOSubset hrel **)

let wosub_equal x s t =
  hconj (wosub_le x s t) (wosub_le x t s)

(** val wosub_comparable : hSet -> coq_WOSubset hrel **)

let wosub_comparable _ _ _ =
  hdisj

(** val hasSmallest_WOSubset_plus_point :
    hSet -> coq_WOSubset -> pr1hSet -> hProptoType -> hProptoType **)

let hasSmallest_WOSubset_plus_point x s z nSz = x
  (* Obj.magic (fun lem t ne -> *)
  (*   let s' = coq_TOSubset_plus_point x (coq_WOSubset_to_TOSubset x s) z nSz in *)
  (*   let s'z = *)
  (*     subtype_plus_has_point *)
  (*       (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s)) z *)
  (*   in *)
  (*   let z' = { pr1 = z; pr2 = s'z } in *)
  (*   let j = *)
  (*     coq_TOSubset_plus_point_incl x (coq_WOSubset_to_TOSubset x s) z nSz *)
  (*   in *)
  (*   let jmap = *)
  (*     subtype_inc (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s)) *)
  (*       (coq_TOSubset_to_subtype x s') j *)
  (*   in *)
  (*   let siT = fun s0 -> *)
  (*     t *)
  (*       (subtype_inc *)
  (*         (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s)) *)
  (*         (coq_TOSubset_to_subtype x s') j s0) *)
  (*   in *)
  (*   let h = lem ishinh in *)
  (*   (match h with *)
  (*    | Coq_ii1 a -> *)
  (*      let siTmin = Obj.magic coq_WOS_hasSmallest x s siT a in *)
  (*      squash_to_hProp ishinh siTmin (fun x0 -> *)
  (*        let m = x0.pr1 in *)
  (*        let pr3 = x0.pr2 in *)
  (*        let siTm = pr3.pr1 in *)
  (*        let min = pr3.pr2 in *)
  (*        hinhpr *)
  (*          (let m' = jmap m in *)
  (*           { pr1 = m'; pr2 = { pr1 = siTm; pr2 = (fun x1 -> *)
  (*           let t0 = x1.pr1 in *)
  (*           let s't = x1.pr2 in *)
  (*           (fun tt -> *)
  (*           squash_to_hProp *)
  (*             (coq_TOSrel x s' (Obj.magic m') *)
  (*               (Obj.magic { pr1 = t0; pr2 = s't })) s't (fun x2 -> *)
  (*             match x2 with *)
  (*             | Coq_ii1 h0 -> min { pr1 = t0; pr2 = h0 } tt *)
  (*             | Coq_ii2 _ -> Obj.magic Coq_tt))) } })) *)
  (*    | Coq_ii2 b -> *)
  (*      hinhpr { pr1 = z'; pr2 = { pr1 = *)
  (*        (squash_to_hProp (t z') ne (fun x0 -> *)
  (*          let pr3 = x0.pr1 in *)
  (*          let t0 = pr3.pr1 in *)
  (*          let siTt = pr3.pr2 in *)
  (*          let tt = x0.pr2 in *)
  (*          squash_to_hProp (t z') siTt (fun x1 -> *)
  (*            match x1 with *)
  (*            | Coq_ii1 h0 -> *)
  (*              fromempty *)
  (*                (b (hinhpr { pr1 = { pr1 = t0; pr2 = h0 }; pr2 = tt })) *)
  (*            | Coq_ii2 _ -> tt))); pr2 = (fun x0 -> *)
  (*        let t0 = x0.pr1 in *)
  (*        let s't = x0.pr2 in *)
  (*        (fun tt -> *)
  (*        squash_to_hProp *)
  (*          (coq_TOSrel x s' (Obj.magic z') *)
  (*            (Obj.magic { pr1 = t0; pr2 = s't })) s't (fun x1 -> *)
  (*          match x1 with *)
  (*          | Coq_ii1 h0 -> *)
  (*            fromempty (b (hinhpr { pr1 = { pr1 = t0; pr2 = h0 }; pr2 = tt })) *)
  (*          | Coq_ii2 _ -> coq_TOrefl x s' (Obj.magic { pr1 = z; pr2 = s'z })))) } })) *)

(** val coq_WOSubset_plus_point :
    hSet -> coq_WOSubset -> pr1hSet -> hProptoType -> hProptoType ->
    coq_WOSubset **)

let coq_WOSubset_plus_point x s z nSz lem =
  Obj.magic { pr1 =
    (subtype_plus (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s))
      z); pr2 = { pr1 =
    (coq_TOSrel x
      (coq_TOSubset_plus_point x (coq_WOSubset_to_TOSubset x s) z nSz));
    pr2 = { pr1 =
    (coq_TOtotal x
      (coq_TOSubset_plus_point x (coq_WOSubset_to_TOSubset x s) z nSz));
    pr2 = (Obj.magic hasSmallest_WOSubset_plus_point x s z nSz lem) } } }

(** val wosub_univalence_map :
    hSet -> coq_WOSubset -> coq_WOSubset -> coq_WOSubset paths -> hProptoType **)

let wosub_univalence_map _ _ _ _ =
  let l = { pr1 = (fun _ s -> s); pr2 = { pr1 = (fun _ _ le -> le); pr2 =
    (fun _ _ _ st _ -> st) } }
  in
  Obj.magic make_dirprod l l

(** val wosub_univalence :
    hSet -> coq_WOSubset -> coq_WOSubset -> (coq_WOSubset paths, hProptoType)
    weq **)


(** val wosub_univalence_compute :
    hSet -> coq_WOSubset -> coq_WOSubset -> coq_WOSubset paths -> hProptoType
    paths **)

let wosub_univalence_compute _ _ _ _ =
  Coq_paths_refl

(** val wosub_inc :
    hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> pr1hSet carrier ->
    pr1hSet carrier **)

let wosub_inc x s t le s0 =
  subtype_inc (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s))
    (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t))
    (Obj.magic le).pr1 s0

(** val wosub_fidelity :
    hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> pr1hSet carrier ->
    pr1hSet carrier -> hProptoType **)

let wosub_fidelity x s t le s0 s' =
  let srel = coq_WOSrel x s in
  let stot =
    let x0 = (Obj.magic coq_WOSwo x s).pr2 in let x1 = x0.pr1 in x1.pr2
  in
  Obj.magic { pr1 = (fun l -> Obj.magic wosub_le_comp x s t le s0 s' l);
    pr2 = (fun _ ->
    squash_to_hProp (Obj.magic srel s0 s') (stot s0 s') (fun c ->
      match c with
      | Coq_ii1 a -> a
      | Coq_ii2 _ ->
        let x0 = (Obj.magic s).pr2.pr2 in
        let x1 = x0.pr1 in let x2 = x1.pr1 in let x3 = x2.pr1 in x3.pr2 s0)) }

(** val h1 :
    hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet carrier -> pr1hSet
    carrier -> pr1hSet carrier paths -> hProptoType -> hProptoType **)

let h1 _ _ _ _ _ _ le =
  le

(** val wosub_le_isPartialOrder : hSet -> coq_WOSubset isPartialOrder **)

let wosub_le_isPartialOrder x = x
  (* { pr1 = { pr1 = (fun s t u i j -> *)
  (*   Obj.magic { pr1 = *)
  (*     ((Obj.magic subtype_containment_isPartialOrder).pr1.pr1 *)
  (*       (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s)) *)
  (*       (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)) *)
  (*       (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x u)) *)
  (*       (Obj.magic i).pr1 (Obj.magic j).pr1); pr2 = { pr1 = (fun s0 s' l -> *)
  (*     Obj.magic wosub_le_comp x t u j *)
  (*       (subtype_inc *)
  (*         (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s)) *)
  (*         (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)) *)
  (*         (Obj.magic i).pr1 s0) *)
  (*       (subtype_inc *)
  (*         (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s)) *)
  (*         (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)) *)
  (*         (Obj.magic i).pr1 s') (Obj.magic wosub_le_comp x s t i s0 s' l)); *)
  (*     pr2 = (fun s0 u0 ss uu l -> *)
  (*     let uinT = { pr1 = u0; pr2 = *)
  (*       (Obj.magic wosub_le_subi x t u j s0 u0 ((Obj.magic i).pr1 s0 ss) uu l) } *)
  (*     in *)
  (*     let p = *)
  (*       subtypePath_prop *)
  (*         (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x u)) *)
  (*         (subtype_inc *)
  (*           (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)) *)
  (*           (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x u)) *)
  (*           (Obj.magic j).pr1 uinT) { pr1 = u0; pr2 = uu } Coq_paths_refl *)
  (*     in *)
  (*     let q = *)
  (*       h1 x u *)
  (*         (subtype_inc *)
  (*           (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)) *)
  (*           (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x u)) *)
  (*           (Obj.magic j).pr1 uinT) { pr1 = u0; pr2 = uu } *)
  (*         (subtype_inc *)
  (*           (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)) *)
  (*           (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x u)) *)
  (*           (Obj.magic j).pr1 *)
  (*           (subtype_inc *)
  (*             (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s)) *)
  (*             (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)) *)
  (*             (Obj.magic i).pr1 { pr1 = s0; pr2 = ss })) p l *)
  (*     in *)
  (*     let r = *)
  (*       (Obj.magic wosub_fidelity x t u j uinT *)
  (*         (subtype_inc *)
  (*           (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s)) *)
  (*           (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)) *)
  (*           (Obj.magic i).pr1 { pr1 = s0; pr2 = ss })).pr2 q *)
  (*     in *)
  (*     Obj.magic wosub_le_subi x s t i s0 u0 ss *)
  (*       (Obj.magic wosub_le_subi x t u j s0 u0 ((Obj.magic i).pr1 s0 ss) uu l) *)
  (*       r) } }); pr2 = (wosub_le_isrefl x) }; pr2 = (fun s t i j -> *)
  (*   invmap (Obj.magic wosub_univalence x s t) { pr1 = i; pr2 = j }) } *)

(** val coq_WosubPoset : hSet -> coq_Poset **)

let coq_WosubPoset x =
  { pr1 = (coq_WOSubset_set x); pr2 = { pr1 = (fun s t -> wosub_le x s t);
    pr2 = (wosub_le_isPartialOrder x) } }

(** val wosub_le_smaller : hSet -> coq_WOSubset -> coq_WOSubset -> hProp **)

let wosub_le_smaller x s t =
  hconj (wosub_le x s t) ishinh

(** val upto : hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet hsubtype **)

let upto x s s0 x0 =
  total2_hProp (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s) x0)
    (fun h -> lt x s { pr1 = x0; pr2 = h } s0)

(** val upto_eqn :
    hSet -> coq_WOSubset -> coq_WOSubset -> pr1hSet -> hProptoType ->
    hProptoType -> hProptoType -> pr1hSet hsubtype paths **)

let upto_eqn x s t x0 sx tx sT = x
  (* invmap *)
  (*   (Obj.magic hsubtype_univalence (upto x s { pr1 = x0; pr2 = sx }) *)
  (*     (upto x t { pr1 = x0; pr2 = tx })) (fun y -> { pr1 = (fun x1 -> *)
  (*   let sy = x1.pr1 in *)
  (*   let lt0 = x1.pr2 in *)
  (*   { pr1 = ((Obj.magic sT).pr1 y sy); pr2 = *)
  (*   (negf (fun le' -> *)
  (*     (Obj.magic wosub_fidelity x s t sT { pr1 = x0; pr2 = sx } { pr1 = y; *)
  (*       pr2 = sy }).pr2 *)
  (*       (h1'' x (coq_WOSubset_to_TOSubset x t) { pr1 = x0; pr2 = tx } *)
  (*         (wosub_inc x s t sT { pr1 = x0; pr2 = sx }) { pr1 = y; pr2 = *)
  (*         ((Obj.magic sT).pr1 y sy) } *)
  (*         (wosub_inc x s t sT { pr1 = y; pr2 = sy }) le' Coq_paths_refl *)
  (*         Coq_paths_refl)) lt0) }); pr2 = (fun x1 -> *)
  (*   let ty = x1.pr1 in *)
  (*   let lt0 = x1.pr2 in *)
  (*   let q = Obj.magic wosub_le_subi x s t sT x0 y sx ty in *)
  (*   let sy = *)
  (*     q *)
  (*       (wo_lt_to_le x t { pr1 = y; pr2 = ty } { pr1 = x0; pr2 = *)
  (*         ((Obj.magic sT).pr1 x0 sx) } lt0) *)
  (*   in *)
  (*   { pr1 = sy; pr2 = *)
  (*   (negf (fun le' -> *)
  (*     h1'' x (coq_WOSubset_to_TOSubset x t) *)
  (*       (subtype_inc *)
  (*         (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s)) *)
  (*         (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)) *)
  (*         (Obj.magic sT).pr1 { pr1 = x0; pr2 = sx }) { pr1 = x0; pr2 = *)
  (*       ((Obj.magic sT).pr1 x0 sx) } *)
  (*       (subtype_inc *)
  (*         (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x s)) *)
  (*         (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x t)) *)
  (*         (Obj.magic sT).pr1 { pr1 = y; pr2 = sy }) { pr1 = y; pr2 = ty } *)
  (*       (Obj.magic wosub_le_comp x s t sT { pr1 = x0; pr2 = sx } { pr1 = y; *)
  (*         pr2 = sy } le') Coq_paths_refl Coq_paths_refl) (Obj.magic lt0)) }) }) *)

(** val isInterval :
    hSet -> pr1hSet hsubtype -> coq_WOSubset -> hProptoType -> hProptoType ->
    hProptoType -> hProptoType -> hProptoType **)

let isInterval x s t le lem ini ne = x
  (* let min = coq_WOS_hasSmallest x t in *)
  (* let u = fun _ -> hneg in *)
  (* let neU = *)
  (*   squash_to_hProp ishinh ne (fun x0 -> *)
  (*     let x1 = x0.pr1 in *)
  (*     let pr3 = x0.pr2 in *)
  (*     let tx = pr3.pr1 in *)
  (*     let nSx = pr3.pr2 in hinhpr { pr1 = { pr1 = x1; pr2 = tx }; pr2 = nSx }) *)
  (* in *)
  (* let minU = Obj.magic min u neU in *)
  (* squash_to_hProp ishinh minU (fun x0 -> *)
  (*   let u0 = x0.pr1 in *)
  (*   let pr3 = x0.pr2 in *)
  (*   let uu = pr3.pr1 in *)
  (*   let minu = pr3.pr2 in *)
  (*   hinhpr { pr1 = u0; pr2 = (fun y -> { pr1 = (fun sy -> { pr1 = *)
  (*     (Obj.magic le y sy); pr2 = (fun ules -> *)
  (*     uu (Obj.magic ini y u0.pr1 sy u0.pr2 ules)) }); pr2 = (fun yltu -> *)
  (*     let yinT = yltu.pr1 in *)
  (*     let yltu0 = yltu.pr2 in *)
  (*     proof_by_contradiction (s y) lem *)
  (*       (Obj.magic (fun bc -> yltu0 (minu { pr1 = y; pr2 = yinT } bc)))) }) }) *)

(** val is_wosubset_chain : hSet -> ('a1 -> coq_WOSubset) -> hProp **)

let is_wosubset_chain x s =
  forall_hProp (fun i ->
    forall_hProp (fun j -> wosub_comparable x (s i) (s j)))

(** val common_index :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> 'a1 -> pr1hSet ->
    hProptoType **)

let common_index x s chain i x0 = x
  (* let x1 = (Obj.magic x0).pr1 in *)
  (* let xinU = (Obj.magic x0).pr2 in *)
  (* squash_to_hProp ishinh xinU (fun x2 -> *)
  (*   let k = x2.pr1 in *)
  (*   let xinSk = x2.pr2 in *)
  (*   squash_to_hProp ishinh (Obj.magic chain i k) (fun c -> *)
  (*     hinhpr *)
  (*       (match c with *)
  (*        | Coq_ii1 a -> { pr1 = k; pr2 = { pr1 = a; pr2 = xinSk } } *)
  (*        | Coq_ii2 b -> *)
  (*          { pr1 = i; pr2 = { pr1 = (wosub_le_isrefl x (s i)); pr2 = *)
  (*            (b.pr1 x1 xinSk) } }))) *)

(** val common_index2 :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet ->
    hProptoType **)

let common_index2 _ _ chain x y = x
  (* let x0 = (Obj.magic x).pr1 in *)
  (* let j = (Obj.magic x).pr2 in *)
  (* let y0 = (Obj.magic y).pr1 in *)
  (* let k = (Obj.magic y).pr2 in *)
  (* squash_to_hProp ishinh j (fun x1 -> *)
  (*   let j0 = x1.pr1 in *)
  (*   let s = x1.pr2 in *)
  (*   squash_to_hProp ishinh k (fun x2 -> *)
  (*     let k0 = x2.pr1 in *)
  (*     let t = x2.pr2 in *)
  (*     squash_to_hProp ishinh (Obj.magic chain j0 k0) (fun x3 -> *)
  (*       match x3 with *)
  (*       | Coq_ii1 h -> *)
  (*         hinhpr { pr1 = k0; pr2 = { pr1 = (h.pr1 x0 s); pr2 = t } } *)
  (*       | Coq_ii2 h -> *)
  (*         hinhpr { pr1 = j0; pr2 = { pr1 = s; pr2 = (h.pr1 y0 t) } }))) *)

(** val common_index3 :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet ->
    pr1hSet -> hProptoType **)

let common_index3 _ _ chain x y z = x
  (* let x0 = (Obj.magic x).pr1 in *)
  (* let j = (Obj.magic x).pr2 in *)
  (* let y0 = (Obj.magic y).pr1 in *)
  (* let k = (Obj.magic y).pr2 in *)
  (* let z0 = (Obj.magic z).pr1 in *)
  (* let l = (Obj.magic z).pr2 in *)
  (* squash_to_hProp ishinh j (fun x1 -> *)
  (*   let j0 = x1.pr1 in *)
  (*   let s = x1.pr2 in *)
  (*   squash_to_hProp ishinh k (fun x2 -> *)
  (*     let k0 = x2.pr1 in *)
  (*     let t = x2.pr2 in *)
  (*     squash_to_hProp ishinh l (fun x3 -> *)
  (*       let l0 = x3.pr1 in *)
  (*       let u = x3.pr2 in *)
  (*       squash_to_hProp ishinh (Obj.magic chain j0 k0) (fun x4 -> *)
  (*         match x4 with *)
  (*         | Coq_ii1 h -> *)
  (*           squash_to_hProp ishinh (Obj.magic chain k0 l0) (fun x5 -> *)
  (*             match x5 with *)
  (*             | Coq_ii1 h0 -> *)
  (*               hinhpr { pr1 = l0; pr2 = { pr1 = (h0.pr1 x0 (h.pr1 x0 s)); *)
  (*                 pr2 = { pr1 = (h0.pr1 y0 t); pr2 = u } } } *)
  (*             | Coq_ii2 h0 -> *)
  (*               hinhpr { pr1 = k0; pr2 = { pr1 = (h.pr1 x0 s); pr2 = { pr1 = *)
  (*                 t; pr2 = (h0.pr1 z0 u) } } }) *)
  (*         | Coq_ii2 h -> *)
  (*           squash_to_hProp ishinh (Obj.magic chain j0 l0) (fun x5 -> *)
  (*             match x5 with *)
  (*             | Coq_ii1 h0 -> *)
  (*               hinhpr { pr1 = l0; pr2 = { pr1 = (h0.pr1 x0 s); pr2 = { pr1 = *)
  (*                 (h0.pr1 y0 (h.pr1 y0 t)); pr2 = u } } } *)
  (*             | Coq_ii2 h0 -> *)
  (*               hinhpr { pr1 = j0; pr2 = { pr1 = s; pr2 = { pr1 = *)
  (*                 (h.pr1 y0 t); pr2 = (h0.pr1 z0 u) } } }))))) *)

(** val chain_union_prelim_eq0 :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet -> 'a1
    -> 'a1 -> hProptoType -> hProptoType -> hProptoType -> hProptoType ->
    hProp paths **)


(** val chain_union_rel :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet hrel **)

let chain_union_rel x s chain x0 y = x
  (* Obj.magic squash_to_hSet hPropset (fun x1 -> *)
  (*   let i = x1.pr1 in *)
  (*   let pr3 = x1.pr2 in *)
  (*   let s0 = pr3.pr1 in *)
  (*   let t = pr3.pr2 in *)
  (*   Obj.magic coq_WOSrel x (s i) { pr1 = (Obj.magic x0).pr1; pr2 = s0 } *)
  (*     { pr1 = (Obj.magic y).pr1; pr2 = t }) (fun i j -> *)
  (*   chain_union_prelim_eq0 x s chain (Obj.magic x0).pr1 (Obj.magic y).pr1 *)
  (*     i.pr1 j.pr1 i.pr2.pr1 j.pr2.pr1 i.pr2.pr2 j.pr2.pr2) *)
  (*   (common_index2 x s chain x0 y) *)

(** val chain_union_rel_eqn :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet -> pr1hSet -> 'a1
    -> hProptoType -> hProptoType -> hProp paths **)

let chain_union_rel_eqn _ _ _ _ _ _ _ _ =
  Coq_paths_refl

(** val chain_union_rel_istrans :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet istrans **)

let chain_union_rel_istrans x s chain x0 y z l m = x
  (* squash_to_hProp (chain_union_rel x s chain x0 z) *)
  (*   (common_index3 x s chain x0 y z) (fun x1 -> *)
  (*   let i = x1.pr1 in *)
  (*   let pr3 = x1.pr2 in *)
  (*   let r = pr3.pr1 in *)
  (*   let pr4 = pr3.pr2 in *)
  (*   let s0 = pr4.pr1 in *)
  (*   let t = pr4.pr2 in *)
  (*   let p = chain_union_rel_eqn x s chain x0 y i r s0 in *)
  (*   let q = chain_union_rel_eqn x s chain y z i s0 t in *)
  (*   let e = chain_union_rel_eqn x s chain x0 z i r t in *)
  (*   let l0 = *)
  (*     internal_paths_rew (chain_union_rel x s chain x0 y) l *)
  (*       (coq_WOSrel x (s i) (Obj.magic { pr1 = (Obj.magic x0).pr1; pr2 = r }) *)
  (*         (Obj.magic { pr1 = (Obj.magic y).pr1; pr2 = s0 })) p *)
  (*   in *)
  (*   let m0 = *)
  (*     internal_paths_rew (chain_union_rel x s chain y z) m *)
  (*       (coq_WOSrel x (s i) (Obj.magic { pr1 = (Obj.magic y).pr1; pr2 = s0 }) *)
  (*         (Obj.magic { pr1 = (Obj.magic z).pr1; pr2 = t })) q *)
  (*   in *)
  (*   internal_paths_rew_r (chain_union_rel x s chain x0 z) *)
  (*     (coq_WOSrel x (s i) (Obj.magic { pr1 = (Obj.magic x0).pr1; pr2 = r }) *)
  (*       (Obj.magic { pr1 = (Obj.magic z).pr1; pr2 = t })) *)
  (*     (let x2 = (Obj.magic s i).pr2.pr2 in *)
  (*      let x3 = x2.pr1 in *)
  (*      let x4 = x3.pr1 in *)
  (*      let x5 = x4.pr1 in *)
  (*      x5.pr1 { pr1 = (Obj.magic x0).pr1; pr2 = r } { pr1 = *)
  (*        (Obj.magic y).pr1; pr2 = s0 } { pr1 = (Obj.magic z).pr1; pr2 = t } *)
  (*        l0 m0) e) *)

(** val chain_union_rel_isrefl :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet isrefl **)

let chain_union_rel_isrefl x s chain x0 =
  squash_to_hProp (chain_union_rel x s chain x0 x0) (Obj.magic x0).pr2
    (fun x1 ->
    let i = x1.pr1 in
    let r = x1.pr2 in
    let p = chain_union_rel_eqn x s chain x0 x0 i r r in
    internal_paths_rew_r (chain_union_rel x s chain x0 x0)
      (coq_WOSrel x (s i) (Obj.magic { pr1 = (Obj.magic x0).pr1; pr2 = r })
        (Obj.magic { pr1 = (Obj.magic x0).pr1; pr2 = r }))
      (let x2 = (Obj.magic s i).pr2.pr2 in
       let x3 = x2.pr1 in
       let x4 = x3.pr1 in
       let x5 = x4.pr1 in x5.pr2 { pr1 = (Obj.magic x0).pr1; pr2 = r }) p)

(** val chain_union_rel_isantisymm :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet isantisymm **)

let chain_union_rel_isantisymm x s chain x0 y l m =
  Obj.magic squash_to_hProp
    (eqset
      (carrier_subset x
        (subtype_union (fun i ->
          coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s i))))) x0
      y) (common_index2 x s chain x0 y) (fun x1 ->
    let i = x1.pr1 in
    let pr3 = x1.pr2 in
    let r = pr3.pr1 in
    let s0 = pr3.pr2 in
    Obj.magic subtypePath_prop
      (subtype_union (fun i0 ->
        coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s i0)))) x0 y
      (let p = chain_union_rel_eqn x s chain x0 y i r s0 in
       let l0 =
         internal_paths_rew (chain_union_rel x s chain x0 y) l
           (coq_WOSrel x (s i)
             (Obj.magic { pr1 = (Obj.magic x0).pr1; pr2 = r })
             (Obj.magic { pr1 = (Obj.magic y).pr1; pr2 = s0 })) p
       in
       let q = chain_union_rel_eqn x s chain y x0 i s0 r in
       let m0 =
         internal_paths_rew (chain_union_rel x s chain y x0) m
           (coq_WOSrel x (s i)
             (Obj.magic { pr1 = (Obj.magic y).pr1; pr2 = s0 })
             (Obj.magic { pr1 = (Obj.magic x0).pr1; pr2 = r })) q
       in
       let anti =
         let x2 = (Obj.magic s i).pr2.pr2 in
         let x3 = x2.pr1 in let x4 = x3.pr1 in x4.pr2
       in
       let b =
         anti { pr1 = (Obj.magic x0).pr1; pr2 = r } { pr1 =
           (Obj.magic y).pr1; pr2 = s0 } l0 m0
       in
       maponpaths (fun t -> t.pr1) { pr1 = (Obj.magic x0).pr1; pr2 = r }
         { pr1 = (Obj.magic y).pr1; pr2 = s0 } b))

(** val chain_union_rel_istotal :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> pr1hSet istotal **)

let chain_union_rel_istotal x s chain x0 y = x
  (* squash_to_hProp hdisj (common_index2 x s chain x0 y) (fun x1 -> *)
  (*   let i = x1.pr1 in *)
  (*   let pr3 = x1.pr2 in *)
  (*   let r = pr3.pr1 in *)
  (*   let s0 = pr3.pr2 in *)
  (*   let p = chain_union_rel_eqn x s chain x0 y i r s0 in *)
  (*   internal_paths_rew_r (chain_union_rel x s chain x0 y) *)
  (*     (coq_WOSrel x (s i) (Obj.magic { pr1 = (Obj.magic x0).pr1; pr2 = r }) *)
  (*       (Obj.magic { pr1 = (Obj.magic y).pr1; pr2 = s0 })) *)
  (*     (let p0 = chain_union_rel_eqn x s chain y x0 i s0 r in *)
  (*      internal_paths_rew_r (chain_union_rel x s chain y x0) *)
  (*        (coq_WOSrel x (s i) *)
  (*          (Obj.magic { pr1 = (Obj.magic y).pr1; pr2 = s0 }) *)
  (*          (Obj.magic { pr1 = (Obj.magic x0).pr1; pr2 = r })) *)
  (*        (let x2 = (Obj.magic s i).pr2.pr2 in *)
  (*         let x3 = x2.pr1 in *)
  (*         x3.pr2 { pr1 = (Obj.magic x0).pr1; pr2 = r } { pr1 = *)
  (*           (Obj.magic y).pr1; pr2 = s0 }) p0) p) *)

(** val chain_union_rel_isTotalOrder :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> hProptoType **)

let chain_union_rel_isTotalOrder x s chain = x
  (* Obj.magic { pr1 = { pr1 = { pr1 = (chain_union_rel_istrans x s chain); *)
  (*   pr2 = (chain_union_rel_isrefl x s chain) }; pr2 = *)
  (*   (chain_union_rel_isantisymm x s chain) }; pr2 = *)
  (*   (chain_union_rel_istotal x s chain) } *)

(** val chain_union_TOSubset :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> coq_TOSubset **)

let chain_union_TOSubset x s schain = x
  (* Obj.magic { pr1 = *)
  (*   (subtype_union (fun x0 -> *)
  (*     coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s x0)))); pr2 = *)
  (*   { pr1 = (chain_union_rel x s schain); pr2 = { pr1 = { pr1 = { pr1 = *)
  (*   (chain_union_rel_istrans x s schain); pr2 = *)
  (*   (chain_union_rel_isrefl x s schain) }; pr2 = *)
  (*   (chain_union_rel_isantisymm x s schain) }; pr2 = *)
  (*   (chain_union_rel_istotal x s schain) } } } *)

(** val chain_union_tosub_le :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> 'a1 -> hProptoType **)

let chain_union_tosub_le x s schain i =
  Obj.magic { pr1 =
    (subtype_union_containedIn x (fun x0 ->
      coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s x0))) i);
    pr2 = (fun s0 s' j ->
    let u =
      subtype_inc
        (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s i)))
        (fun _ -> ishinh)
        (Obj.magic (fun _ j0 -> hinhpr { pr1 = i; pr2 = j0 })) s0
    in
    let u' =
      subtype_inc
        (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s i)))
        (fun _ -> ishinh)
        (Obj.magic (fun _ j0 -> hinhpr { pr1 = i; pr2 = j0 })) s'
    in
    let q =
      chain_union_rel_eqn x s schain (Obj.magic u) (Obj.magic u') i s0.pr2
        s'.pr2
    in
    internal_paths_rew_r
      (chain_union_rel x s schain (Obj.magic u) (Obj.magic u'))
      (coq_WOSrel x (s i) (Obj.magic { pr1 = u.pr1; pr2 = s0.pr2 })
        (Obj.magic { pr1 = u'.pr1; pr2 = s'.pr2 })) j q) }

(** val chain_union_rel_initial :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> 'a1 -> hProptoType **)

let chain_union_rel_initial x s schain i = x
  (* Obj.magic (fun s0 t le -> *)
  (*   squash_to_hProp *)
  (*     (subtype_isIn *)
  (*       (coq_TOSubset_to_subtype x (chain_union_TOSubset x s schain)) t *)
  (*       (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s i)))) *)
  (*     (common_index x s schain i (Obj.magic t)) (fun x0 -> *)
  (*     let j = x0.pr1 in *)
  (*     let pr3 = x0.pr2 in *)
  (*     let pr4 = pr3.pr1 in *)
  (*     let ij = pr4.pr1 in *)
  (*     let pr5 = pr4.pr2 in *)
  (*     let ini = pr5.pr2 in *)
  (*     let tinSj = pr3.pr2 in *)
  (*     let t' = { pr1 = t.pr1; pr2 = tinSj } in *)
  (*     ini s0.pr1 t'.pr1 s0.pr2 t'.pr2 *)
  (*       ((Obj.magic tosub_fidelity x (coq_WOSubset_to_TOSubset x (s j)) *)
  (*          (chain_union_TOSubset x s schain) *)
  (*          (chain_union_tosub_le x s schain j) t' *)
  (*          (subtype_inc *)
  (*            (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s i))) *)
  (*            (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s j))) *)
  (*            ij s0)).pr2 le))) *)

(** val chain_union_rel_hasSmallest :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> hProptoType **)

let chain_union_rel_hasSmallest x s chain = x
  (* Obj.magic (fun t t' -> *)
  (*   squash_to_hProp ishinh t' (fun x0 -> *)
  (*     let pr3 = x0.pr1 in *)
  (*     let x1 = pr3.pr1 in *)
  (*     let i = pr3.pr2 in *)
  (*     let xinT = x0.pr2 in *)
  (*     squash_to_hProp ishinh i (fun x2 -> *)
  (*       let j = x2.pr1 in *)
  (*       let xinSj = x2.pr2 in *)
  (*       let t'0 = fun s0 -> *)
  (*         t *)
  (*           (subtype_inc *)
  (*             (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s j))) *)
  (*             (subtype_union (fun x3 -> *)
  (*               coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s x3)))) *)
  (*             (subtype_union_containedIn x (fun x3 -> *)
  (*               coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s x3))) *)
  (*               j) s0) *)
  (*       in *)
  (*       let t'1 = hinhpr { pr1 = { pr1 = x1; pr2 = xinSj }; pr2 = xinT } in *)
  (*       let min = Obj.magic coq_WOS_hasSmallest x (s j) t'0 t'1 in *)
  (*       squash_to_hProp ishinh min (fun x3 -> *)
  (*         let t0 = x3.pr1 in *)
  (*         let pr4 = x3.pr2 in *)
  (*         let t0inT' = pr4.pr1 in *)
  (*         let t0min = pr4.pr2 in *)
  (*         let t0' = *)
  (*           subtype_inc *)
  (*             (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s j))) *)
  (*             (subtype_union (fun x4 -> *)
  (*               coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s x4)))) *)
  (*             (subtype_union_containedIn x (fun x4 -> *)
  (*               coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s x4))) *)
  (*               j) t0 *)
  (*         in *)
  (*         hinhpr { pr1 = t0'; pr2 = { pr1 = t0inT'; pr2 = (fun t1 tinT -> *)
  (*           hdisj_impl_2 *)
  (*             (chain_union_rel x s chain (Obj.magic t1) (Obj.magic t0')) *)
  (*             (chain_union_rel x s chain (Obj.magic t0') (Obj.magic t1)) *)
  (*             (chain_union_rel_istotal x s chain (Obj.magic t1) *)
  (*               (Obj.magic t0')) (fun tle -> *)
  (*             let q = Obj.magic chain_union_rel_initial x s chain j t0 t1 tle *)
  (*             in *)
  (*             let t'2 = { pr1 = t1.pr1; pr2 = q } in *)
  (*             let e = *)
  (*               subtypePath_prop *)
  (*                 (subtype_union (fun x4 -> *)
  (*                   coq_TOSubset_to_subtype x *)
  (*                     (coq_WOSubset_to_TOSubset x (s x4)))) *)
  (*                 (subtype_inc *)
  (*                   (coq_TOSubset_to_subtype x *)
  (*                     (coq_WOSubset_to_TOSubset x (s j))) *)
  (*                   (subtype_union (fun x4 -> *)
  (*                     coq_TOSubset_to_subtype x *)
  (*                       (coq_WOSubset_to_TOSubset x (s x4)))) *)
  (*                   (subtype_union_containedIn x (fun x4 -> *)
  (*                     coq_TOSubset_to_subtype x *)
  (*                       (coq_WOSubset_to_TOSubset x (s x4))) j) t'2) t1 *)
  (*                 Coq_paths_refl *)
  (*             in *)
  (*             internal_paths_rew *)
  (*               (subtype_inc *)
  (*                 (coq_TOSubset_to_subtype x *)
  (*                   (coq_WOSubset_to_TOSubset x (s j))) *)
  (*                 (subtype_union (fun x4 -> *)
  (*                   coq_TOSubset_to_subtype x *)
  (*                     (coq_WOSubset_to_TOSubset x (s x4)))) *)
  (*                 (subtype_union_containedIn x (fun x4 -> *)
  (*                   coq_TOSubset_to_subtype x *)
  (*                     (coq_WOSubset_to_TOSubset x (s x4))) j) t'2) *)
  (*               ((Obj.magic chain_union_tosub_le x s chain j).pr2 t0 t'2 *)
  (*                 (t0min t'2 *)
  (*                   (internal_paths_rew_r *)
  (*                     (subtype_inc *)
  (*                       (coq_TOSubset_to_subtype x *)
  (*                         (coq_WOSubset_to_TOSubset x (s j))) *)
  (*                       (subtype_union (fun x4 -> *)
  (*                         coq_TOSubset_to_subtype x *)
  (*                           (coq_WOSubset_to_TOSubset x (s x4)))) *)
  (*                       (subtype_union_containedIn x (fun x4 -> *)
  (*                         coq_TOSubset_to_subtype x *)
  (*                           (coq_WOSubset_to_TOSubset x (s x4))) j) t'2) t1 *)
  (*                     tinT e))) t1 e)) } })))) *)

(** val chain_union_WOSubset :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> coq_WOSubset **)

let chain_union_WOSubset x s schain = x
  (* Obj.magic { pr1 = *)
  (*   (coq_TOSubset_to_subtype x (chain_union_TOSubset x s schain)); pr2 = *)
  (*   { pr1 = (chain_union_rel x s schain); pr2 = { pr1 = { pr1 = { pr1 = *)
  (*   { pr1 = (chain_union_rel_istrans x s schain); pr2 = *)
  (*   (chain_union_rel_isrefl x s schain) }; pr2 = *)
  (*   (chain_union_rel_isantisymm x s schain) }; pr2 = *)
  (*   (chain_union_rel_istotal x s schain) }; pr2 = *)
  (*   (chain_union_rel_hasSmallest x s schain) } } } *)

(** val chain_union_le :
    hSet -> ('a1 -> coq_WOSubset) -> hProptoType -> hProptoType **)

let chain_union_le x s schain =
  Obj.magic (fun i -> { pr1 =
    (subtype_union_containedIn x (fun x0 ->
      coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s x0))) i);
    pr2 = { pr1 = (Obj.magic chain_union_tosub_le x s schain i).pr2; pr2 =
    (fun s0 t ss tt ->
    Obj.magic chain_union_rel_initial x s schain i { pr1 = s0; pr2 = ss }
      { pr1 = t; pr2 = tt }) } })

(** val proper_subtypes_set : hSet **)

let proper_subtypes_set =
  total2_hSet subtype_set (fun _ -> hProp_to_hSet ishinh)

(** val upto' : hSet -> coq_WOSubset -> pr1hSet carrier -> pr1hSet **)

let upto' x c c0 =
  Obj.magic { pr1 = (upto x c c0); pr2 =
    (hinhpr { pr1 = c0.pr1; pr2 = (fun n ->
      let n0 = n.pr1 in
      n.pr2
        (Obj.magic coq_TOeq_to_refl x (coq_WOSubset_to_TOSubset x c) c0
          { pr1 = c0.pr1; pr2 = n0 }
          (subtypePath_prop
            (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x c)) c0
            { pr1 = c0.pr1; pr2 = n0 } Coq_paths_refl))) }) }

(** val choice_fun : hSet -> hSet **)

let choice_fun x =
  forall_hSet (fun _ -> total2_hSet x (fun _ -> hProp_to_hSet hneg))

(** val coq_AC_to_choice_fun : hSet -> hProptoType **)

let coq_AC_to_choice_fun x = x
  (* Obj.magic (fun ac -> *)
  (*   squash_to_hProp ishinh (ac proper_subtypes_set __ (fun t -> t.pr2)) hinhpr) *)

(** val is_guided_WOSubset : hSet -> pr1hSet -> coq_WOSubset -> hProp **)

let is_guided_WOSubset x g c =
  forall_hProp (fun c0 -> eqset x c0.pr1 (Obj.magic g (upto' x c c0)).pr1)

(** val upto'_eqn :
    hSet -> pr1hSet -> coq_WOSubset -> coq_WOSubset -> hProptoType -> pr1hSet
    carrier -> pr1hSet carrier -> pr1hSet paths -> pr1hSet paths **)

let upto'_eqn _ _ _ _ _ _ _ _ =
  Coq_paths_refl

type coq_Guided_WOSubset = (coq_WOSubset, hProptoType) total2

(** val guidedFamily :
    hSet -> pr1hSet -> coq_Guided_WOSubset -> coq_WOSubset **)

let guidedFamily _ _ t =
  t.pr1

(** val guided_WOSubset_total :
    hSet -> pr1hSet -> hProptoType -> hProptoType **)

let guided_WOSubset_total x g lem = x
  (* Obj.magic (fun x0 -> *)
  (*   let c = x0.pr1 in *)
  (*   let gC = x0.pr2 in *)
  (*   (fun x1 -> *)
  (*   let d = x1.pr1 in *)
  (*   let gD = x1.pr2 in *)
  (*   let w = *)
  (*     max_common_initial x (coq_WOSubset_to_TOSubset x c) *)
  (*       (coq_WOSubset_to_TOSubset x d) *)
  (*   in *)
  (*   let q = *)
  (*     max_common_initial_is_common_initial x (coq_WOSubset_to_TOSubset x c) *)
  (*       (coq_WOSubset_to_TOSubset x d) *)
  (*   in *)
  (*   let wC = (Obj.magic q).pr1 in *)
  (*   let pr3 = (Obj.magic q).pr2 in *)
  (*   let wD = pr3.pr1 in *)
  (*   let pr4 = pr3.pr2 in *)
  (*   let wCi = pr4.pr1 in *)
  (*   let pr5 = pr4.pr2 in *)
  (*   let wDi = pr5.pr1 in *)
  (*   let wCD = pr5.pr2 in *)
  (*   let e = *)
  (*     proof_by_contradiction hdisj lem *)
  (*       (Obj.magic (fun h -> *)
  (*         let k = *)
  (*           fromnegcoprod_prop *)
  (*             (subtype_equal w *)
  (*               (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x c))) *)
  (*             (subtype_equal w *)
  (*               (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x d))) h *)
  (*         in *)
  (*         let nc = (Obj.magic k).pr1 in *)
  (*         let nd = (Obj.magic k).pr2 in *)
  (*         let nCW = *)
  (*           subtype_notEqual_containedIn w *)
  (*             (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x c)) wC *)
  (*             (subtype_notEqual_from_negEqual w *)
  (*               (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x c)) *)
  (*               lem nc) *)
  (*         in *)
  (*         let nDW = *)
  (*           subtype_notEqual_containedIn w *)
  (*             (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x d)) wD *)
  (*             (subtype_notEqual_from_negEqual w *)
  (*               (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x d)) *)
  (*               lem nd) *)
  (*         in *)
  (*         let p = isInterval x w c wC lem wCi nCW in *)
  (*         let q0 = isInterval x w d wD lem wDi nDW in *)
  (*         squash_to_hProp hfalse p (fun x2 -> *)
  (*           let c0 = x2.pr1 in *)
  (*           let cE = x2.pr2 in *)
  (*           squash_to_hProp hfalse q0 (fun x3 -> *)
  (*             let d0 = x3.pr1 in *)
  (*             let dE = x3.pr2 in *)
  (*             let ce = invmap (hsubtype_univalence w (upto x c c0)) cE in *)
  (*             let de = invmap (hsubtype_univalence w (upto x d d0)) dE in *)
  (*             let p0 = gC c0 in *)
  (*             let q1 = gD d0 in *)
  (*             let cd1 = *)
  (*               pathscomp0 c0.pr1 (Obj.magic g (upto' x c c0)).pr1 d0.pr1 p0 *)
  (*                 (pathscomp0 (Obj.magic g (upto' x c c0)).pr1 *)
  (*                   (Obj.magic g (upto' x d d0)).pr1 d0.pr1 Coq_paths_refl *)
  (*                   (pathsinv0 d0.pr1 (Obj.magic g (upto' x d d0)).pr1 q1)) *)
  (*             in *)
  (*             let w' = subtype_plus w c0.pr1 in *)
  (*             let j = subtype_plus_incl w c0.pr1 in *)
  (*             let w'c = subtype_plus_has_point w c0.pr1 in *)
  (*             let w'd = transportf c0.pr1 d0.pr1 cd1 w'c in *)
  (*             let ci = *)
  (*               let w'C = *)
  (*                 subtype_plus_in w c0.pr1 *)
  (*                   (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x c)) *)
  (*                   wC c0.pr2 *)
  (*               in *)
  (*               let w'D = *)
  (*                 subtype_plus_in w c0.pr1 *)
  (*                   (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x d)) *)
  (*                   wD (transportb c0.pr1 d0.pr1 cd1 d0.pr2) *)
  (*               in *)
  (*               { pr1 = w'C; pr2 = { pr1 = w'D; pr2 = *)
  (*               (let cmax = fun v _ -> *)
  (*                  let v0 = v.pr1 in *)
  (*                  let w'v = v.pr2 in *)
  (*                  squash_to_hProp *)
  (*                    (coq_WOSrel x c *)
  (*                      (Obj.magic subtype_inc w' *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = v0; *)
  (*                        pr2 = w'v }) (Obj.magic c0)) w'v (fun x4 -> *)
  (*                    match x4 with *)
  (*                    | Coq_ii1 h0 -> *)
  (*                      let l = (Obj.magic cE v0).pr1 h0 in *)
  (*                      let q2 = *)
  (*                        tot_nge_to_le *)
  (*                          (carrier_subset x *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x c))) *)
  (*                          (coq_TOSrel x (coq_WOSubset_to_TOSubset x c)) *)
  (*                          (coq_TOtot x (coq_WOSubset_to_TOSubset x c)) *)
  (*                          (Obj.magic c0) *)
  (*                          (Obj.magic { pr1 = v0; pr2 = l.pr1 }) l.pr2 *)
  (*                      in *)
  (*                      h1'' x (coq_WOSubset_to_TOSubset x c) { pr1 = v0; *)
  (*                        pr2 = l.pr1 } *)
  (*                        (subtype_inc w' *)
  (*                          (coq_TOSubset_to_subtype x *)
  (*                            (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = v0; *)
  (*                          pr2 = w'v }) c0 c0 q2 Coq_paths_refl Coq_paths_refl *)
  (*                    | Coq_ii2 p1 -> *)
  (*                      Obj.magic coq_TOeq_to_refl x *)
  (*                        (coq_WOSubset_to_TOSubset x c) *)
  (*                        (subtype_inc w' *)
  (*                          (coq_TOSubset_to_subtype x *)
  (*                            (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = v0; *)
  (*                          pr2 = w'v }) c0 *)
  (*                        (subtypePath_prop *)
  (*                          (coq_TOSubset_to_subtype x *)
  (*                            (coq_WOSubset_to_TOSubset x c)) *)
  (*                          (subtype_inc w' *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                            v0; pr2 = w'v }) c0 (pathsinv0 c0.pr1 v0 p1))) *)
  (*                in *)
  (*                let cmax' = fun w0 _ -> *)
  (*                  let v = w0.pr1 in *)
  (*                  let wv = w0.pr2 in *)
  (*                  let l = (Obj.magic cE v).pr1 wv in *)
  (*                  let q2 = *)
  (*                    tot_nge_to_le *)
  (*                      (carrier_subset x *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x c))) *)
  (*                      (coq_TOSrel x (coq_WOSubset_to_TOSubset x c)) *)
  (*                      (coq_TOtot x (coq_WOSubset_to_TOSubset x c)) *)
  (*                      (Obj.magic c0) (Obj.magic { pr1 = v; pr2 = l.pr1 }) *)
  (*                      l.pr2 *)
  (*                  in *)
  (*                  let x4 = fun x4 y -> *)
  (*                    (tot_nle_iff_gt *)
  (*                      (carrier_subset x *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x c))) *)
  (*                      (coq_TOSrel x (coq_WOSubset_to_TOSubset x c)) *)
  (*                      (Obj.magic c).pr2.pr2.pr1 x4 y).pr2 *)
  (*                  in *)
  (*                  Obj.magic x4 c0 *)
  (*                    (subtype_inc w' *)
  (*                      (coq_TOSubset_to_subtype x *)
  (*                        (coq_WOSubset_to_TOSubset x c)) w'C *)
  (*                      (subtype_inc w w' j { pr1 = v; pr2 = wv })) { pr1 = *)
  (*                    (h1'' x (coq_WOSubset_to_TOSubset x c) { pr1 = v; pr2 = *)
  (*                      l.pr1 } *)
  (*                      (subtype_inc w' *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x c)) w'C *)
  (*                        (subtype_inc w w' j { pr1 = v; pr2 = wv })) c0 c0 q2 *)
  (*                      Coq_paths_refl Coq_paths_refl); pr2 = (fun e -> *)
  (*                    let e' = *)
  (*                      maponpaths (fun t -> t.pr1) *)
  (*                        (subtype_inc w' *)
  (*                          (coq_TOSubset_to_subtype x *)
  (*                            (coq_WOSubset_to_TOSubset x c)) w'C *)
  (*                          (subtype_inc w w' j { pr1 = v; pr2 = wv })) c0 e *)
  (*                    in *)
  (*                    let l' = l.pr2 in *)
  (*                    Obj.magic l' *)
  (*                      (Obj.magic coq_TOeq_to_refl_1 x *)
  (*                        (coq_WOSubset_to_TOSubset x c) c0 { pr1 = v; pr2 = *)
  (*                        l.pr1 } (pathsinv0 v c0.pr1 e'))) } *)
  (*                in *)
  (*                let dmax = fun v _ -> *)
  (*                  let v0 = v.pr1 in *)
  (*                  let w'v = v.pr2 in *)
  (*                  squash_to_hProp *)
  (*                    (coq_WOSrel x d *)
  (*                      (Obj.magic subtype_inc w' *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = v0; *)
  (*                        pr2 = w'v }) (Obj.magic d0)) w'v (fun x4 -> *)
  (*                    match x4 with *)
  (*                    | Coq_ii1 h0 -> *)
  (*                      let l = (Obj.magic dE v0).pr1 h0 in *)
  (*                      let q2 = *)
  (*                        tot_nge_to_le *)
  (*                          (carrier_subset x *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x d))) *)
  (*                          (coq_TOSrel x (coq_WOSubset_to_TOSubset x d)) *)
  (*                          (coq_TOtot x (coq_WOSubset_to_TOSubset x d)) *)
  (*                          (Obj.magic d0) *)
  (*                          (Obj.magic { pr1 = v0; pr2 = l.pr1 }) l.pr2 *)
  (*                      in *)
  (*                      h1'' x (coq_WOSubset_to_TOSubset x d) { pr1 = v0; *)
  (*                        pr2 = l.pr1 } *)
  (*                        (subtype_inc w' *)
  (*                          (coq_TOSubset_to_subtype x *)
  (*                            (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = v0; *)
  (*                          pr2 = w'v }) d0 d0 q2 Coq_paths_refl Coq_paths_refl *)
  (*                    | Coq_ii2 p1 -> *)
  (*                      Obj.magic coq_TOeq_to_refl x *)
  (*                        (coq_WOSubset_to_TOSubset x d) *)
  (*                        (subtype_inc w' *)
  (*                          (coq_TOSubset_to_subtype x *)
  (*                            (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = v0; *)
  (*                          pr2 = w'v }) d0 *)
  (*                        (subtypePath_prop *)
  (*                          (coq_TOSubset_to_subtype x *)
  (*                            (coq_WOSubset_to_TOSubset x d)) *)
  (*                          (subtype_inc w' *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                            v0; pr2 = w'v }) d0 *)
  (*                          (pathscomp0 v0 c0.pr1 d0.pr1 *)
  (*                            (pathsinv0 c0.pr1 v0 p1) cd1))) *)
  (*                in *)
  (*                let dmax' = fun w0 _ -> *)
  (*                  let v = w0.pr1 in *)
  (*                  let wv = w0.pr2 in *)
  (*                  let l = (Obj.magic dE v).pr1 wv in *)
  (*                  let q2 = *)
  (*                    tot_nge_to_le *)
  (*                      (carrier_subset x *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x d))) *)
  (*                      (coq_TOSrel x (coq_WOSubset_to_TOSubset x d)) *)
  (*                      (coq_TOtot x (coq_WOSubset_to_TOSubset x d)) *)
  (*                      (Obj.magic d0) (Obj.magic { pr1 = v; pr2 = l.pr1 }) *)
  (*                      l.pr2 *)
  (*                  in *)
  (*                  let x4 = fun x4 y -> *)
  (*                    (tot_nle_iff_gt *)
  (*                      (carrier_subset x *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x d))) *)
  (*                      (coq_TOSrel x (coq_WOSubset_to_TOSubset x d)) *)
  (*                      (Obj.magic d).pr2.pr2.pr1 x4 y).pr2 *)
  (*                  in *)
  (*                  Obj.magic x4 d0 *)
  (*                    (subtype_inc w' *)
  (*                      (coq_TOSubset_to_subtype x *)
  (*                        (coq_WOSubset_to_TOSubset x d)) w'D *)
  (*                      (subtype_inc w w' j { pr1 = v; pr2 = wv })) { pr1 = *)
  (*                    (h1'' x (coq_WOSubset_to_TOSubset x d) { pr1 = v; pr2 = *)
  (*                      l.pr1 } *)
  (*                      (subtype_inc w' *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x d)) w'D *)
  (*                        (subtype_inc w w' j { pr1 = v; pr2 = wv })) d0 d0 q2 *)
  (*                      Coq_paths_refl Coq_paths_refl); pr2 = (fun e -> *)
  (*                    let e' = *)
  (*                      maponpaths (fun t -> t.pr1) *)
  (*                        (subtype_inc w' *)
  (*                          (coq_TOSubset_to_subtype x *)
  (*                            (coq_WOSubset_to_TOSubset x d)) w'D *)
  (*                          (subtype_inc w w' j { pr1 = v; pr2 = wv })) d0 e *)
  (*                    in *)
  (*                    let l' = l.pr2 in *)
  (*                    Obj.magic l' *)
  (*                      (Obj.magic coq_TOeq_to_refl_1 x *)
  (*                        (coq_WOSubset_to_TOSubset x d) d0 { pr1 = v; pr2 = *)
  (*                        l.pr1 } (pathsinv0 v d0.pr1 e'))) } *)
  (*                in *)
  (*                { pr1 = (fun w'0 c' w'w' cc' le -> *)
  (*                squash_to_hProp (w' c') w'w' (fun b -> *)
  (*                  match b with *)
  (*                  | Coq_ii1 a -> *)
  (*                    hinhpr (Coq_ii1 *)
  (*                      (Obj.magic wCi w'0 c' a cc' *)
  (*                        (h1'' x (coq_WOSubset_to_TOSubset x c) { pr1 = c'; *)
  (*                          pr2 = cc' } { pr1 = c'; pr2 = cc' } { pr1 = w'0; *)
  (*                          pr2 = (Obj.magic w'C w'0 w'w') } { pr1 = w'0; *)
  (*                          pr2 = (Obj.magic wC w'0 a) } le Coq_paths_refl *)
  (*                          Coq_paths_refl))) *)
  (*                  | Coq_ii2 _ -> *)
  (*                    let h0 = Obj.magic lem (eqset x c0.pr1 c') in *)
  (*                    (match h0 with *)
  (*                     | Coq_ii1 _ -> w'c *)
  (*                     | Coq_ii2 b0 -> *)
  (*                       Obj.magic j c' *)
  (*                         (internal_paths_rew_r w (upto x c c0) { pr1 = cc'; *)
  (*                           pr2 = (fun le' -> *)
  (*                           b0 *)
  (*                             (let e = *)
  (*                                coq_TOanti x (coq_WOSubset_to_TOSubset x c) *)
  (*                                  (Obj.magic c0) *)
  (*                                  (Obj.magic { pr1 = c'; pr2 = cc' }) le' *)
  (*                                  (h1'' x (coq_WOSubset_to_TOSubset x c) *)
  (*                                    { pr1 = c'; pr2 = cc' } { pr1 = c'; *)
  (*                                    pr2 = cc' } { pr1 = c0.pr1; pr2 = *)
  (*                                    (Obj.magic w'C c0.pr1 w'w') } c0 le *)
  (*                                    Coq_paths_refl Coq_paths_refl) *)
  (*                              in *)
  (*                              maponpaths (Obj.magic (fun t -> t.pr1)) *)
  (*                                (Obj.magic c0) *)
  (*                                (Obj.magic { pr1 = c'; pr2 = cc' }) e)) } ce)))); *)
  (*                pr2 = { pr1 = (fun w'0 d' w'w' dd' le -> *)
  (*                squash_to_hProp (w' d') w'w' (fun b -> *)
  (*                  match b with *)
  (*                  | Coq_ii1 a -> *)
  (*                    hinhpr (Coq_ii1 *)
  (*                      (Obj.magic wDi w'0 d' a dd' *)
  (*                        (h1'' x (coq_WOSubset_to_TOSubset x d) { pr1 = d'; *)
  (*                          pr2 = dd' } { pr1 = d'; pr2 = dd' } { pr1 = w'0; *)
  (*                          pr2 = (Obj.magic w'D w'0 w'w') } { pr1 = w'0; *)
  (*                          pr2 = (Obj.magic wD w'0 a) } le Coq_paths_refl *)
  (*                          Coq_paths_refl))) *)
  (*                  | Coq_ii2 _ -> *)
  (*                    let h0 = Obj.magic lem (eqset x d0.pr1 d') in *)
  (*                    (match h0 with *)
  (*                     | Coq_ii1 _ -> w'd *)
  (*                     | Coq_ii2 b0 -> *)
  (*                       Obj.magic j d' *)
  (*                         (internal_paths_rew_r w (upto x d d0) { pr1 = dd'; *)
  (*                           pr2 = (fun le' -> *)
  (*                           b0 *)
  (*                             (let e = *)
  (*                                coq_TOanti x (coq_WOSubset_to_TOSubset x d) *)
  (*                                  (Obj.magic d0) *)
  (*                                  (Obj.magic { pr1 = d'; pr2 = dd' }) le' *)
  (*                                  (h1'' x (coq_WOSubset_to_TOSubset x d) *)
  (*                                    { pr1 = d'; pr2 = dd' } { pr1 = d'; *)
  (*                                    pr2 = dd' } { pr1 = c0.pr1; pr2 = *)
  (*                                    (Obj.magic w'D c0.pr1 w'w') } d0 le *)
  (*                                    Coq_paths_refl cd1) *)
  (*                              in *)
  (*                              maponpaths (Obj.magic (fun t -> t.pr1)) *)
  (*                                (Obj.magic d0) *)
  (*                                (Obj.magic { pr1 = d'; pr2 = dd' }) e)) } de)))); *)
  (*                pr2 = (fun x4 -> *)
  (*                let v = x4.pr1 in *)
  (*                let w'v = x4.pr2 in *)
  (*                (fun x5 -> *)
  (*                let w0 = x5.pr1 in *)
  (*                let w'w = x5.pr2 in *)
  (*                squash_to_hProp *)
  (*                  (hequiv *)
  (*                    (coq_TOSrel x (coq_WOSubset_to_TOSubset x c) *)
  (*                      (Obj.magic subtype_inc w' *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = v; *)
  (*                        pr2 = w'v }) *)
  (*                      (Obj.magic subtype_inc w' *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = w0; *)
  (*                        pr2 = w'w })) *)
  (*                    (coq_TOSrel x (coq_WOSubset_to_TOSubset x d) *)
  (*                      (Obj.magic subtype_inc w' *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = v; *)
  (*                        pr2 = w'v }) *)
  (*                      (Obj.magic subtype_inc w' *)
  (*                        (coq_TOSubset_to_subtype x *)
  (*                          (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = w0; *)
  (*                        pr2 = w'w }))) w'v (fun x6 -> *)
  (*                  match x6 with *)
  (*                  | Coq_ii1 h0 -> *)
  (*                    squash_to_hProp *)
  (*                      (hequiv *)
  (*                        (coq_TOSrel x (coq_WOSubset_to_TOSubset x c) *)
  (*                          (Obj.magic subtype_inc w' *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = v; *)
  (*                            pr2 = w'v }) *)
  (*                          (Obj.magic subtype_inc w' *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                            w0; pr2 = w'w })) *)
  (*                        (coq_TOSrel x (coq_WOSubset_to_TOSubset x d) *)
  (*                          (Obj.magic subtype_inc w' *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = v; *)
  (*                            pr2 = w'v }) *)
  (*                          (Obj.magic subtype_inc w' *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                            w0; pr2 = w'w }))) w'w (fun x7 -> *)
  (*                      match x7 with *)
  (*                      | Coq_ii1 h2 -> *)
  (*                        wCD { pr1 = v; pr2 = h0 } { pr1 = w0; pr2 = h2 } *)
  (*                      | Coq_ii2 _ -> *)
  (*                        logeq_if_both_true *)
  (*                          (coq_TOSrel x (coq_WOSubset_to_TOSubset x c) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                              v; pr2 = w'v }) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                              c0.pr1; pr2 = w'w })) *)
  (*                          (coq_TOSrel x (coq_WOSubset_to_TOSubset x d) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                              v; pr2 = w'v }) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                              c0.pr1; pr2 = w'w })) *)
  (*                          (cmax { pr1 = v; pr2 = w'v } w'w) *)
  (*                          (dmax { pr1 = v; pr2 = w'v } w'w)) *)
  (*                  | Coq_ii2 _ -> *)
  (*                    squash_to_hProp *)
  (*                      (hequiv *)
  (*                        (coq_TOSrel x (coq_WOSubset_to_TOSubset x c) *)
  (*                          (Obj.magic subtype_inc w' *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                            c0.pr1; pr2 = w'v }) *)
  (*                          (Obj.magic subtype_inc w' *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                            w0; pr2 = w'w })) *)
  (*                        (coq_TOSrel x (coq_WOSubset_to_TOSubset x d) *)
  (*                          (Obj.magic subtype_inc w' *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                            c0.pr1; pr2 = w'v }) *)
  (*                          (Obj.magic subtype_inc w' *)
  (*                            (coq_TOSubset_to_subtype x *)
  (*                              (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                            w0; pr2 = w'w }))) w'w (fun x7 -> *)
  (*                      match x7 with *)
  (*                      | Coq_ii1 h0 -> *)
  (*                        logeq_if_both_false *)
  (*                          (coq_TOSrel x (coq_WOSubset_to_TOSubset x c) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                              c0.pr1; pr2 = w'v }) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                              w0; pr2 = w'w })) *)
  (*                          (coq_TOSrel x (coq_WOSubset_to_TOSubset x d) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                              c0.pr1; pr2 = w'v }) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                              w0; pr2 = w'w })) *)
  (*                          (cmax' { pr1 = w0; pr2 = h0 } w'v) *)
  (*                          (dmax' { pr1 = w0; pr2 = h0 } w'd) *)
  (*                      | Coq_ii2 _ -> *)
  (*                        logeq_if_both_true *)
  (*                          (coq_TOSrel x (coq_WOSubset_to_TOSubset x c) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                              c0.pr1; pr2 = w'v }) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                              c0.pr1; pr2 = w'w })) *)
  (*                          (coq_TOSrel x (coq_WOSubset_to_TOSubset x d) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                              c0.pr1; pr2 = w'v }) *)
  (*                            (Obj.magic subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                              c0.pr1; pr2 = w'w })) *)
  (*                          (Obj.magic coq_TOeq_to_refl_1 x *)
  (*                            (coq_WOSubset_to_TOSubset x c) *)
  (*                            (subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                              c0.pr1; pr2 = w'v }) *)
  (*                            (subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x c)) w'C { pr1 = *)
  (*                              c0.pr1; pr2 = w'w }) *)
  (*                            (pathsinv0 *)
  (*                              (subtype_inc w' *)
  (*                                (coq_TOSubset_to_subtype x *)
  (*                                  (coq_WOSubset_to_TOSubset x c)) w'C *)
  (*                                { pr1 = c0.pr1; pr2 = w'w }).pr1 *)
  (*                              (subtype_inc w' *)
  (*                                (coq_TOSubset_to_subtype x *)
  (*                                  (coq_WOSubset_to_TOSubset x c)) w'C *)
  (*                                { pr1 = c0.pr1; pr2 = w'v }).pr1 *)
  (*                              Coq_paths_refl)) *)
  (*                          (Obj.magic coq_TOeq_to_refl_1 x *)
  (*                            (coq_WOSubset_to_TOSubset x d) *)
  (*                            (subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                              c0.pr1; pr2 = w'v }) *)
  (*                            (subtype_inc w' *)
  (*                              (coq_TOSubset_to_subtype x *)
  (*                                (coq_WOSubset_to_TOSubset x d)) w'D { pr1 = *)
  (*                              c0.pr1; pr2 = w'w }) *)
  (*                            (pathsinv0 *)
  (*                              (subtype_inc w' *)
  (*                                (coq_TOSubset_to_subtype x *)
  (*                                  (coq_WOSubset_to_TOSubset x d)) w'D *)
  (*                                { pr1 = c0.pr1; pr2 = w'w }).pr1 *)
  (*                              (subtype_inc w' *)
  (*                                (coq_TOSubset_to_subtype x *)
  (*                                  (coq_WOSubset_to_TOSubset x d)) w'D *)
  (*                                { pr1 = c0.pr1; pr2 = w'v }).pr1 *)
  (*                              Coq_paths_refl)))))) } }) } } *)
  (*             in *)
  (*             let k0 = *)
  (*               max_common_initial_is_max x (coq_WOSubset_to_TOSubset x c) *)
  (*                 (coq_WOSubset_to_TOSubset x d) w' (Obj.magic ci) *)
  (*             in *)
  (*             let wc = Obj.magic k0 c0.pr1 w'c in *)
  (*             let l = (Obj.magic cE c0.pr1).pr1 wc in *)
  (*             let cc = l.pr1 in *)
  (*             l.pr2 *)
  (*               (transportf c0 { pr1 = c0.pr1; pr2 = cc } *)
  (*                 (subtypePath_prop (coq_WOSubset_to_subtype x c) c0 { pr1 = *)
  (*                   c0.pr1; pr2 = cc } Coq_paths_refl) *)
  (*                 (coq_TOrefl x (coq_WOSubset_to_TOSubset x c) (Obj.magic c0))))))) *)
  (*   in *)
  (*   squash_to_hProp hdisj e (fun e0 -> *)
  (*     hinhpr *)
  (*       (match e0 with *)
  (*        | Coq_ii1 _ -> *)
  (*          Coq_ii1 { pr1 = wD; pr2 = { pr1 = (fun x2 y le -> *)
  (*            (Obj.magic wCD x2 y).pr1 *)
  (*              (h1'' x (coq_WOSubset_to_TOSubset x c) x2 *)
  (*                (subtype_inc *)
  (*                  (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x c)) *)
  (*                  (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x c)) *)
  (*                  wC x2) y *)
  (*                (subtype_inc *)
  (*                  (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x c)) *)
  (*                  (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x c)) *)
  (*                  wC y) le Coq_paths_refl Coq_paths_refl)); pr2 = wDi } } *)
  (*        | Coq_ii2 _ -> *)
  (*          Coq_ii2 { pr1 = wC; pr2 = { pr1 = (fun x2 y le -> *)
  (*            (Obj.magic wCD x2 y).pr2 *)
  (*              (h1'' x (coq_WOSubset_to_TOSubset x d) x2 *)
  (*                (subtype_inc *)
  (*                  (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x d)) *)
  (*                  (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x d)) *)
  (*                  wD x2) y *)
  (*                (subtype_inc *)
  (*                  (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x d)) *)
  (*                  (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x d)) *)
  (*                  wD y) le Coq_paths_refl Coq_paths_refl)); pr2 = wCi } })))) *)

(** val coq_ZermeloWellOrdering : hSet -> hProptoType **)

let coq_ZermeloWellOrdering x = x
  (* Obj.magic (fun ac -> *)
  (*   let lem = coq_AC_to_LEM ac in *)
  (*   squash_to_hProp ishinh (Obj.magic coq_AC_to_choice_fun x ac) (fun g -> *)
  (*     let schain = guided_WOSubset_total x g lem in *)
  (*     let w = chain_union_WOSubset x (guidedFamily x g) schain in *)
  (*     hinhpr (Obj.magic w).pr2)) *)

type coq_WellOrderedSet = (hSet, pr1hSet) total2

(** val coq_WellOrderedSet_to_hSet : coq_WellOrderedSet -> hSet **)

let coq_WellOrderedSet_to_hSet t =
  t.pr1

(** val coq_WOrel : coq_WellOrderedSet -> pr1hSet hrel **)

let coq_WOrel x =
  (Obj.magic x).pr2.pr1

(** val coq_WOlt : coq_WellOrderedSet -> pr1hSet -> pr1hSet -> hProp **)

let coq_WOlt _ _ _ =
  hneg

(** val isaprop_theSmallest :
    hSet -> pr1hSet hrel -> hProptoType -> pr1hSet hsubtype -> pr1hSet isaprop **)

let isaprop_theSmallest x r total s =
  let pr3 = (Obj.magic total).pr1 in
  let anti = pr3.pr2 in
  let tot = (Obj.magic total).pr2 in
  invproofirrelevance (fun s0 t ->
    subtypePath_prop (fun x0 ->
      hconj (s x0) (forall_hProp (fun t0 -> himpl (r x0 t0)))) s0 t
      (let x0 = s0.pr1 in
       let i = s0.pr2 in
       let y = t.pr1 in
       let j = t.pr2 in
       let i0 = (Obj.magic i).pr1 in
       let i1 = (Obj.magic i).pr2 in
       let j0 = (Obj.magic j).pr1 in
       let j1 = (Obj.magic j).pr2 in
       Obj.magic squash_to_hProp (eqset x x0 y) (tot x0 y) (fun x1 ->
         match x1 with
         | Coq_ii1 h -> anti x0 y h (j1 x0 i0)
         | Coq_ii2 h -> anti x0 y (i1 y j0) h)))

(** val coq_WO_isTotalOrder : coq_WellOrderedSet -> hProptoType **)

let coq_WO_isTotalOrder x =
  (Obj.magic x).pr2.pr2.pr1

(** val coq_WO_isrefl : coq_WellOrderedSet -> pr1hSet isrefl **)

let coq_WO_isrefl x =
  (Obj.magic coq_WO_isTotalOrder x).pr1.pr1.pr2

(** val coq_WO_istrans : coq_WellOrderedSet -> pr1hSet istrans **)

let coq_WO_istrans x =
  (Obj.magic coq_WO_isTotalOrder x).pr1.pr1.pr1

(** val coq_WO_istotal : coq_WellOrderedSet -> pr1hSet istotal **)

let coq_WO_istotal x =
  (Obj.magic coq_WO_isTotalOrder x).pr2

(** val coq_WO_isantisymm : coq_WellOrderedSet -> pr1hSet isantisymm **)

let coq_WO_isantisymm x =
  (Obj.magic coq_WO_isTotalOrder x).pr1.pr2

(** val coq_WO_hasSmallest : coq_WellOrderedSet -> hProptoType **)

let coq_WO_hasSmallest x =
  (Obj.magic x).pr2.pr2.pr2

(** val coq_WOlt_istrans : coq_WellOrderedSet -> pr1hSet istrans **)

let coq_WOlt_istrans x x0 y z h2 h3 = x
  (* Obj.magic (fun h4 -> *)
  (*   squash_to_hProp { pr1 = __; pr2 = isapropempty } (coq_WO_istotal x y z) *)
  (*     (fun x1 -> *)
  (*     match x1 with *)
  (*     | Coq_ii1 h -> Obj.magic h2 (coq_WO_istrans x y z x0 h h4) *)
  (*     | Coq_ii2 h -> Obj.magic h3 h)) *)

(** val coq_WOlt_isirrefl : coq_WellOrderedSet -> pr1hSet isirrefl **)

let coq_WOlt_isirrefl x x0 h =
  Obj.magic h (coq_WO_isrefl x x0)

(** val coq_WOlt'_subproof :
    coq_WellOrderedSet -> pr1hSet -> pr1hSet -> (hProptoType, pr1hSet paths
    neg) dirprod isaprop **)

let coq_WOlt'_subproof x x0 y =
  isapropdirprod (propproperty (coq_WOrel x x0 y)) isapropneg

(** val coq_WOlt' : coq_WellOrderedSet -> pr1hSet -> pr1hSet -> hProp **)

let coq_WOlt' x x0 y =
  { pr1 = __; pr2 = (coq_WOlt'_subproof x x0 y) }

(** val coq_WOlt'_to_WOlt :
    coq_WellOrderedSet -> pr1hSet -> pr1hSet -> hProptoType -> hProptoType **)

let coq_WOlt'_to_WOlt x x0 y x1 =
  let h2 = (Obj.magic x1).pr1 in
  let h3 = (Obj.magic x1).pr2 in
  Obj.magic (fun h4 -> h3 (coq_WO_isantisymm x x0 y h2 h4))

(** val coq_WOlt_to_WOlt' :
    coq_WellOrderedSet -> pr1hSet isdeceq -> pr1hSet -> pr1hSet ->
    hProptoType -> hProptoType **)

let coq_WOlt_to_WOlt' x hX x0 y _ = x
  (* squash_to_hProp (coq_WOlt' x x0 y) (coq_WO_istotal x x0 y) (fun x1 -> *)
  (*   match x1 with *)
  (*   | Coq_ii1 h -> *)
  (*     let d = hX x0 y in *)
  (*     (match d with *)
  (*      | Coq_ii1 _ -> assert false (\* absurd case *\) *)
  (*      | Coq_ii2 b -> Obj.magic { pr1 = h; pr2 = b }) *)
  (*   | Coq_ii2 _ -> assert false (\* absurd case *\)) *)

(** val coq_WOlt_trich :
    coq_WellOrderedSet -> pr1hSet isdeceq -> pr1hSet -> pr1hSet -> hProptoType **)

let coq_WOlt_trich x hX x0 y = x
  (* let d = hX x0 y in *)
  (* (match d with *)
  (*  | Coq_ii1 a -> hinhpr (Coq_ii2 (hinhpr (Coq_ii1 a))) *)
  (*  | Coq_ii2 b -> *)
  (*    squash_to_hProp hdisj (coq_WO_istotal x x0 y) (fun x1 -> *)
  (*      match x1 with *)
  (*      | Coq_ii1 h -> *)
  (*        hinhpr (Coq_ii2 *)
  (*          (hinhpr (Coq_ii2 *)
  (*            (coq_WOlt'_to_WOlt x x0 y (Obj.magic { pr1 = h; pr2 = b }))))) *)
  (*      | Coq_ii2 h -> *)
  (*        hinhpr (Coq_ii1 *)
  (*          (coq_WOlt'_to_WOlt x y x0 *)
  (*            (Obj.magic { pr1 = h; pr2 = (fun h0 -> b (pathsinv0 y x0 h0)) }))))) *)

(** val theSmallest : coq_WellOrderedSet -> pr1hSet hsubtype -> hProp **)

let theSmallest x s =
  himpl
    (make_hProp
      (isaprop_theSmallest (coq_WellOrderedSet_to_hSet x) (coq_WOrel x)
        (coq_WO_isTotalOrder x) s))

(** val coq_WO_theSmallest :
    coq_WellOrderedSet -> pr1hSet hsubtype -> hProptoType **)

let coq_WO_theSmallest x s = x
  (* Obj.magic (fun ne -> *)
  (*   squash_to_hProp *)
  (*     (make_hProp *)
  (*       (isaprop_theSmallest (coq_WellOrderedSet_to_hSet x) (coq_WOrel x) *)
  (*         (coq_WO_isTotalOrder x) s)) (Obj.magic coq_WO_hasSmallest x s ne) *)
  (*     (fun c -> c)) *)

(** val coq_WO_theUniqueSmallest :
    coq_WellOrderedSet -> pr1hSet hsubtype -> hProptoType **)

let coq_WO_theUniqueSmallest x s =
  Obj.magic (fun ne ->
    iscontraprop1
      (isaprop_theSmallest (coq_WellOrderedSet_to_hSet x) (coq_WOrel x)
        (coq_WO_isTotalOrder x) s) (Obj.magic coq_WO_theSmallest x s ne))

type iswofun =
  ((pr1hSet, pr1hSet) iscomprelrelfun, pr1hSet -> pr1hSet -> hProptoType ->
  hProptoType) dirprod

(** val isaprop_iswofun :
    coq_WellOrderedSet -> coq_WellOrderedSet -> (pr1hSet -> pr1hSet) ->
    iswofun isaprop **)

let isaprop_iswofun _ y f =
  Obj.magic (fun h ->
    Obj.magic isapropdirprod
      (impred_isaprop (fun t ->
        impred_isaprop (fun t0 ->
          impred_isaprop (fun _ -> propproperty (coq_WOrel y (f t) (f t0))))))
      (impred_isaprop (fun _ ->
        impred_isaprop (fun _ -> impred_isaprop (fun _ -> isapropishinh)))) h)

type wofun = (pr1hSet -> pr1hSet, iswofun) total2

(** val pr1wofun :
    coq_WellOrderedSet -> coq_WellOrderedSet -> wofun -> pr1hSet -> pr1hSet **)

let pr1wofun _ _ t =
  t.pr1

(** val wofun_eq :
    coq_WellOrderedSet -> coq_WellOrderedSet -> wofun -> wofun -> (pr1hSet ->
    pr1hSet) paths -> wofun paths **)

let wofun_eq x y f g heq =
  subtypePath (fun h -> isaprop_iswofun x y h) f g heq

(** val iswofun_idfun : coq_WellOrderedSet -> iswofun **)

let iswofun_idfun _ =
  { pr1 = (fun _ _ x0 -> x0); pr2 = (fun _ y hxy ->
    hinhpr { pr1 = y; pr2 = { pr1 = hxy; pr2 =
      (pathsinv0 y (idfun y) Coq_paths_refl) } }) }

(** val iswofun_funcomp :
    coq_WellOrderedSet -> coq_WellOrderedSet -> coq_WellOrderedSet -> wofun
    -> wofun -> iswofun **)

let iswofun_funcomp _ _ _ f g = g
  (* let f0 = f.pr1 in *)
  (* let pr3 = f.pr2 in *)
  (* let h1f = pr3.pr1 in *)
  (* let h2f = pr3.pr2 in *)
  (* let pr4 = g.pr2 in *)
  (* let h1g = pr4.pr1 in *)
  (* let h2g = pr4.pr2 in *)
  (* { pr1 = (fun x y hxy -> h1g (f0 x) (f0 y) (h1f x y hxy)); pr2 = *)
  (* (fun x z hf -> *)
  (* squash_to_hProp ishinh (h2g (f0 x) z hf) (fun x0 -> *)
  (*   let y = x0.pr1 in *)
  (*   let pr5 = x0.pr2 in *)
  (*   let h1y = pr5.pr1 in *)
  (*   let h2y = pr5.pr2 in *)
  (*   squash_to_hProp ishinh (h2f x y h1y) (fun x1 -> *)
  (*     let x' = x1.pr1 in *)
  (*     let pr6 = x1.pr2 in *)
  (*     let h1x' = pr6.pr1 in *)
  (*     let h2x' = pr6.pr2 in *)
  (*     hinhpr { pr1 = x'; pr2 = *)
  (*       (internal_paths_rew_r (f0 x') y { pr1 = h1x'; pr2 = h2y } h2x') }))) } *)

(** val empty_woset_subproof : pr1hSet **)

let empty_woset_subproof = false
  (* Obj.magic { pr1 = { pr1 = { pr1 = { pr1 = (fun _ -> assert false *)
  (*   (\* absurd case *\)); pr2 = (fun _ -> assert false (\* absurd case *\)) }; *)
  (*   pr2 = (fun _ -> assert false (\* absurd case *\)) }; pr2 = (fun _ -> *)
  (*   assert false (\* absurd case *\)) }; pr2 = (fun _ t' -> *)
  (*   squash_to_hProp ishinh t' (fun _ -> assert false (\* absurd case *\))) } *)

(** val empty_woset : coq_WellOrderedSet **)

let empty_woset =
  { pr1 = { pr1 = __; pr2 = (Obj.magic isasetempty) }; pr2 =
    (Obj.magic { pr1 = (fun _ -> assert false (* absurd case *)); pr2 =
      empty_woset_subproof }) }

(** val unit_woset_subproof : pr1hSet -> pr1hSet -> hProptoType isaprop **)

let unit_woset_subproof x y =
  isapropifcontr (Obj.magic isapropunit x y)

(** val unit_woset : coq_WellOrderedSet **)

let unit_woset = 1
  (* { pr1 = { pr1 = __; pr2 = (Obj.magic isasetunit) }; pr2 = *)
  (*   (Obj.magic { pr1 = (fun x y -> { pr1 = __; pr2 = *)
  (*     (unit_woset_subproof x y) }); pr2 = { pr1 = { pr1 = { pr1 = { pr1 = *)
  (*     (fun _ _ _ _ x -> x); pr2 = (fun _ -> Coq_paths_refl) }; pr2 = *)
  (*     (fun _ _ x _ -> x) }; pr2 = (fun _ _ _ h2 -> *)
  (*     h2 (Coq_ii1 (pathsinv0 Coq_tt Coq_tt Coq_paths_refl))) }; pr2 = *)
  (*     (fun _ t' -> *)
  (*     squash_to_hProp ishinh t' (fun x -> *)
  (*       let h = x.pr2 in *)
  (*       hinhpr { pr1 = Coq_tt; pr2 = { pr1 = h; pr2 = (fun _ _ -> *)
  (*         Coq_paths_refl) } })) } }) } *)

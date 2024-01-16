open PartA
open PartB
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom
open WellOrderedSets

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val contr_to_pr1contr :
    ('a1 -> hProp) -> ('a1, hProptoType) total2 -> ('a1, hProptoType) total2
    paths iscontr -> 'a1 paths iscontr **)

let contr_to_pr1contr p t c =p
  (* Obj.magic isofhlevelweqf O (total2_paths_hProp_equiv p t t) c *)

(** val pr1contr_to_contr :
    ('a1 -> hProp) -> ('a1, hProptoType) total2 -> 'a1 paths iscontr -> ('a1,
    hProptoType) total2 paths iscontr **)

let pr1contr_to_contr p t c =p
  (* Obj.magic isofhlevelweqb O (total2_paths_hProp_equiv p t t) c *)

(** val substructure_univalence :
    ('a1 -> 'a1 -> ('a1 paths, 'a2) weq) -> ('a1 -> hProp) -> ('a1,
    hProptoType) total2 -> ('a1, hProptoType) total2 -> (('a1, hProptoType)
    total2 paths, 'a2) weq **)

let substructure_univalence u q a b = u
  (* weqcomp (total2_paths_hProp_equiv q a b) (u a.pr1 b.pr1) *)

type coq_PointedGraph = (hSet, (pr1hSet hrel, pr1hSet) total2) total2

type isaroot = pr1hSet -> hProptoType

(** val isaprop_isaroot :
    hSet -> pr1hSet hrel -> pr1hSet -> isaroot isaprop **)

let isaprop_isaroot _ e r =
  impred (S O) (fun t -> propproperty (e r t))

type isTRR = (pr1hSet isrefl, (pr1hSet istrans, isaroot) dirprod) dirprod

(** val isaprop_isTRR : hSet -> pr1hSet hrel -> pr1hSet -> isTRR isaprop **)

let isaprop_isTRR v e r =
  isapropdirprod (isaprop_isrefl v e)
    (isapropdirprod (isaprop_istrans v e) (isaprop_isaroot v e r))

type coq_TRRGraphData = (pr1hSet hrel, (pr1hSet, isTRR) total2) total2

(** val isaset_TRRGraphData : hSet -> coq_TRRGraphData isaset **)

let isaset_TRRGraphData v =
  Obj.magic isofhleveltotal2 (S (S O)) (isaset_hrel v) (fun x ->
    isofhleveltotal2 (S (S O)) (Obj.magic setproperty v) (fun x0 ->
      hlevelntosn (S O) (isaprop_isTRR v x x0)))

type coq_TRRGraph = (hSet, coq_TRRGraphData) total2

(** val coq_TRRG_edgerel : coq_TRRGraph -> pr1hSet hrel **)

let coq_TRRG_edgerel g =
  g.pr2.pr1

(** val coq_TRRG_root : coq_TRRGraph -> pr1hSet **)

let coq_TRRG_root g =
  g.pr2.pr2.pr1

(** val coq_TRRG_transitivity : coq_TRRGraph -> pr1hSet istrans **)

let coq_TRRG_transitivity g =
  g.pr2.pr2.pr2.pr2.pr1

(** val selfedge : coq_TRRGraph -> pr1hSet -> hProptoType **)

let selfedge g x =
  g.pr2.pr2.pr2.pr1 x

type isTRRGhomo =
  (pr1hSet -> pr1hSet -> (hProptoType, hProptoType) logeq, pr1hSet paths)
  dirprod

(** val isaprop_isTRRGhomo :
    coq_TRRGraph -> coq_TRRGraph -> (pr1hSet -> pr1hSet) -> isTRRGhomo isaprop **)

let isaprop_isTRRGhomo g h f =
  isapropdirprod
    (impred (S O) (fun t ->
      impred (S O) (fun t0 ->
        isapropdirprod
          (impred (S O) (fun _ ->
            propproperty (coq_TRRG_edgerel h (f t) (f t0))))
          (impred (S O) (fun _ -> propproperty (coq_TRRG_edgerel g t t0))))))
    (setproperty h.pr1 (f (coq_TRRG_root g)) (coq_TRRG_root h))

(** val coq_TRRGhomo_frompath :
    hSet -> hSet -> coq_TRRGraphData -> coq_TRRGraphData -> hSet paths ->
    coq_TRRGraphData paths -> isTRRGhomo **)

let coq_TRRGhomo_frompath x _ g h _ q =
  { pr1 = (fun _ _ ->
    let q0 =
      internal_paths_rew (transportf x x Coq_paths_refl g) q g
        (idpath_transportf x g)
    in
    { pr1 = (internal_paths_rew_r g h (fun p -> p) q0); pr2 =
    (internal_paths_rew_r g h (fun p -> p) q0) }); pr2 = Coq_paths_refl }

(** val helper :
    hSet -> (pr1hSet -> pr1hSet -> hProp) -> (pr1hSet -> pr1hSet -> hProp) ->
    pr1hSet -> pr1hSet -> isTRR -> isTRR -> (pr1hSet -> pr1hSet -> hProp)
    paths -> pr1hSet paths -> (pr1hSet, isTRR) total2 paths **)

let helper x e _ r r' isE isE' _ _UU03c3_ =
  internal_paths_rew_r (transportf e e Coq_paths_refl { pr1 = r; pr2 = isE })
    { pr1 = r; pr2 = isE }
    (let x0 = fun x0 y -> (total2_paths_equiv x0 y).pr2 in
     let x1 = fun x1 y y0 -> (x0 x1 y y0).pr1 in
     let x2 = { pr1 = r; pr2 = isE } in
     let y = { pr1 = r'; pr2 = isE' } in
     let y0 = { pr1 = _UU03c3_; pr2 =
       (let x3 = transportf r r' _UU03c3_ isE in
        (Obj.magic isaprop_isTRR x e r' x3 isE').pr1) }
     in
     (x1 x2 y y0).pr1) (idpath_transportf e { pr1 = r; pr2 = isE })

(** val coq_TRRGhomo_topath :
    hSet -> hSet -> coq_TRRGraphData -> coq_TRRGraphData -> hSet paths ->
    isTRRGhomo -> coq_TRRGraphData paths **)


type coq_TRRGraphiso = ((pr1hSet, pr1hSet) weq, isTRRGhomo) total2

(** val id_TRRGraphiso : coq_TRRGraph -> coq_TRRGraphiso **)

let id_TRRGraphiso _ =
  { pr1 = idweq; pr2 = { pr1 = (fun _ _ -> isrefl_logeq); pr2 =
    Coq_paths_refl } }

(** val coq_TRRGraph_univalence_map :
    coq_TRRGraph -> coq_TRRGraph -> coq_TRRGraph paths -> coq_TRRGraphiso **)

let coq_TRRGraph_univalence_map g _ _ =
  id_TRRGraphiso g

(** val coq_TRRGraph_univalence_weq1 :
    coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths, (hSet,
    coq_TRRGraphData) coq_PathPair) weq **)

let coq_TRRGraph_univalence_weq1 =
  total2_paths_equiv

(** val coq_TRRGraph_univalence_weq2 :
    coq_TRRGraph -> coq_TRRGraph -> ((hSet, coq_TRRGraphData) coq_PathPair,
    coq_TRRGraphiso) weq **)

let coq_TRRGraph_univalence_weq2 g h = g h
  (* weqbandf (hSet_univalence g.pr1 h.pr1) (fun p -> *)
  (*   weqimplimpl (fun q -> coq_TRRGhomo_frompath g.pr1 h.pr1 g.pr2 h.pr2 p q) *)
  (*     (fun q -> coq_TRRGhomo_topath g.pr1 h.pr1 g.pr2 h.pr2 p q) *)
  (*     (isaset_TRRGraphData h.pr1 (transportf g.pr1 h.pr1 p g.pr2) h.pr2) *)
  (*     (isaprop_isTRRGhomo g h (pr1weq (hSet_univalence_map g.pr1 h.pr1 p)))) *)

(** val coq_TRRGraph_univalence_weq2_idpath :
    coq_TRRGraph -> coq_TRRGraphiso paths **)

let coq_TRRGraph_univalence_weq2_idpath g = g
  (* let x = fun x y -> (total2_paths_equiv x y).pr2 in *)
  (* let x0 = fun x0 y y0 -> (x x0 y y0).pr1 in *)
  (* let x1 = *)
  (*   pr1weq (coq_TRRGraph_univalence_weq2 g g) { pr1 = Coq_paths_refl; pr2 = *)
  (*     Coq_paths_refl } *)
  (* in *)
  (* let y = id_TRRGraphiso g in *)
  (* let y0 = { pr1 = Coq_paths_refl; pr2 = *)
  (*   (let f = pr1weq (id_TRRGraphiso g).pr1 in *)
  (*    let x2 = *)
  (*      transportf *)
  (*        (pr1weq (coq_TRRGraph_univalence_weq2 g g) { pr1 = Coq_paths_refl; *)
  (*          pr2 = Coq_paths_refl }).pr1 (id_TRRGraphiso g).pr1 Coq_paths_refl *)
  (*        (pr1weq (coq_TRRGraph_univalence_weq2 g g) { pr1 = Coq_paths_refl; *)
  (*          pr2 = Coq_paths_refl }).pr2 *)
  (*    in *)
  (*    let x' = (id_TRRGraphiso g).pr2 in *)
  (*    (Obj.magic isaprop_isTRRGhomo g g f x2 x').pr1) } *)
  (* in *)
  (* (x0 x1 y y0).pr1 *)

(** val coq_TRRGraph_univalence_weq1_idpath :
    coq_TRRGraph -> (hSet, coq_TRRGraphData) coq_PathPair paths **)

let coq_TRRGraph_univalence_weq1_idpath g =
  let x = fun x y -> (total2_paths_equiv x y).pr2 in
  let x0 = fun x0 y y0 -> (x x0 y y0).pr1 in
  let x1 = pr1weq (coq_TRRGraph_univalence_weq1 g g) Coq_paths_refl in
  let y = { pr1 = Coq_paths_refl; pr2 = Coq_paths_refl } in
  let y0 = { pr1 = Coq_paths_refl; pr2 = Coq_paths_refl } in (x0 x1 y y0).pr1

(** val isweq_TRRGraph_univalence_map :
    coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths, coq_TRRGraphiso)
    isweq **)

let isweq_TRRGraph_univalence_map g h = g h
  (* isweqhomot *)
  (*   (pr1weq *)
  (*     (weqcomp (coq_TRRGraph_univalence_weq1 g h) *)
  (*       (coq_TRRGraph_univalence_weq2 g h))) *)
  (*   (coq_TRRGraph_univalence_map g h) (fun _ -> *)
  (*   pathscomp0 *)
  (*     (pr1weq *)
  (*       (weqcomp (coq_TRRGraph_univalence_weq1 g g) *)
  (*         (coq_TRRGraph_univalence_weq2 g g)) Coq_paths_refl) *)
  (*     (pr1weq (coq_TRRGraph_univalence_weq2 g g) *)
  (*       (pr1weq (coq_TRRGraph_univalence_weq1 g g) Coq_paths_refl)) *)
  (*     (coq_TRRGraph_univalence_map g g Coq_paths_refl) *)
  (*     (weqcomp_to_funcomp_app Coq_paths_refl *)
  (*       (coq_TRRGraph_univalence_weq1 g g) (coq_TRRGraph_univalence_weq2 g g)) *)
  (*     (internal_paths_rew_r *)
  (*       (pr1weq (coq_TRRGraph_univalence_weq1 g g) Coq_paths_refl) { pr1 = *)
  (*       Coq_paths_refl; pr2 = Coq_paths_refl } *)
  (*       (internal_paths_rew_r *)
  (*         (pr1weq (coq_TRRGraph_univalence_weq2 g g) { pr1 = Coq_paths_refl; *)
  (*           pr2 = Coq_paths_refl }) (id_TRRGraphiso g) Coq_paths_refl *)
  (*         (coq_TRRGraph_univalence_weq2_idpath g)) *)
  (*       (coq_TRRGraph_univalence_weq1_idpath g))) *)
  (*   (weqproperty *)
  (*     (weqcomp (coq_TRRGraph_univalence_weq1 g h) *)
  (*       (coq_TRRGraph_univalence_weq2 g h))) *)

(** val coq_TRRGraph_univalence :
    coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths, coq_TRRGraphiso) weq **)

let coq_TRRGraph_univalence g h =
  make_weq (coq_TRRGraph_univalence_map g h)
    (isweq_TRRGraph_univalence_map g h)

(** val coq_TRRGraph_univalence_compute :
    coq_TRRGraph -> coq_TRRGraph -> (coq_TRRGraph paths -> coq_TRRGraphiso)
    paths **)

let coq_TRRGraph_univalence_compute _ _ =
  Coq_paths_refl

type coq_DownwardClosure = (pr1hSet, hProptoType) total2

type antisymmetric = (hProptoType, hProptoType) dirprod -> pr1hSet paths

(** val total : coq_TRRGraph -> pr1hSet -> pr1hSet -> hProp **)

let total _ _ _ =
  hdisj

type isatree =
  pr1hSet -> coq_DownwardClosure -> coq_DownwardClosure -> (antisymmetric,
  hProptoType) dirprod

(** val isaprop_isatree : coq_TRRGraph -> isatree isaprop **)

let isaprop_isatree g =
  impred (S O) (fun _ ->
    impred (S O) (fun x ->
      impred (S O) (fun y ->
        isapropdirprod
          (impred (S O) (fun _ -> setproperty g.pr1 y.pr1 x.pr1))
          (propproperty (total g x.pr1 y.pr1)))))

type coq_Tree = (coq_TRRGraph, isatree) total2

type coq_Tree_iso = coq_TRRGraphiso

(** val coq_Tree_univalence :
    coq_Tree -> coq_Tree -> (coq_Tree paths, coq_Tree_iso) weq **)

let coq_Tree_univalence t1 t2 =
  let q = fun g -> { pr1 = __; pr2 = (isaprop_isatree g) } in
  Obj.magic substructure_univalence coq_TRRGraph_univalence q t1 t2

type coq_Upw_underlying = (pr1hSet, hProptoType) total2

(** val isaset_Upw_underlying :
    coq_Tree -> pr1hSet -> coq_Upw_underlying isaset **)

let isaset_Upw_underlying t x =
  isaset_total2 (setproperty t.pr1.pr1) (fun y ->
    let p = coq_TRRG_edgerel t.pr1 x y in (hProp_to_hSet p).pr2)

(** val coq_Upw : coq_Tree -> pr1hSet -> hSet **)

let coq_Upw t x =
  { pr1 = __; pr2 = (Obj.magic isaset_Upw_underlying t x) }

(** val coq_Upw_E : coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> hProp **)

let coq_Upw_E t _ y z =
  t.pr1.pr2.pr1 (Obj.magic y).pr1 (Obj.magic z).pr1

(** val coq_Upw_to_PointedGraph : coq_Tree -> pr1hSet -> coq_PointedGraph **)

let coq_Upw_to_PointedGraph t x =
  { pr1 = (coq_Upw t x); pr2 = { pr1 = (coq_Upw_E t x); pr2 =
    (Obj.magic { pr1 = x; pr2 = (selfedge t.pr1 x) }) } }

(** val coq_Upw_reflexive : coq_Tree -> pr1hSet -> pr1hSet -> hProptoType **)

let coq_Upw_reflexive t _ y =
  selfedge t.pr1 (Obj.magic y).pr1

(** val coq_Upw_transitive :
    coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet -> hProptoType ->
    hProptoType -> hProptoType **)

let coq_Upw_transitive t _ y z w p q =
  coq_TRRG_transitivity t.pr1 (Obj.magic y).pr1 (Obj.magic z).pr1
    (Obj.magic w).pr1 p q

(** val coq_Upw_rooted : coq_Tree -> pr1hSet -> pr1hSet -> hProptoType **)

let coq_Upw_rooted _ _ y =
  (Obj.magic y).pr2

(** val coq_Upw_to_TRRGraph : coq_Tree -> pr1hSet -> coq_TRRGraph **)

let coq_Upw_to_TRRGraph t x =
  { pr1 = (coq_Upw_to_PointedGraph t x).pr1; pr2 = { pr1 =
    (coq_Upw_to_PointedGraph t x).pr2.pr1; pr2 = { pr1 =
    (coq_Upw_to_PointedGraph t x).pr2.pr2; pr2 = { pr1 =
    (coq_Upw_reflexive t x); pr2 = { pr1 = (coq_Upw_transitive t x); pr2 =
    (coq_Upw_rooted t x) } } } } }

(** val isatree_Upw : coq_Tree -> pr1hSet -> isatree **)

let isatree_Upw t x a y z =
  let zzz = (Obj.magic z).pr1.pr1 in
  let zz = z.pr1 in
  let yyy = (Obj.magic y).pr1.pr1 in
  let yy = y.pr1 in
  let eya = y.pr2 in
  let eza = z.pr2 in
  { pr1 = (fun x0 ->
  let yz = x0.pr1 in
  let zy = x0.pr2 in
  let l1 =
    (t.pr2 (Obj.magic a).pr1 { pr1 = yyy; pr2 = eya } { pr1 = zzz; pr2 =
      eza }).pr1 { pr1 = yz; pr2 = zy }
  in
  let q =
    proofirrelevance (t.pr1.pr2.pr1 x (Obj.magic zz).pr1).pr2
      (Obj.magic zz).pr2
      (transportb (Obj.magic zz).pr1 (Obj.magic yy).pr1 l1 (Obj.magic yy).pr2)
  in
  Obj.magic total2_paths_b zz yy l1 q); pr2 =
  (t.pr2 (Obj.magic a).pr1 { pr1 = yyy; pr2 = eya } { pr1 = zzz; pr2 = eza }).pr2 }

(** val coq_Up : coq_Tree -> pr1hSet -> coq_Tree **)

let coq_Up t x =
  { pr1 = (coq_Upw_to_TRRGraph t x); pr2 = (isatree_Upw t x) }

type isrigid = coq_Tree paths iscontr

(** val isaprop_isrigid : coq_Tree -> isrigid isaprop **)

let isaprop_isrigid _ =
  isapropiscontr

type issuperrigid = (isrigid, pr1hSet -> isrigid) dirprod

(** val isaprop_issuperrigid : coq_Tree -> issuperrigid isaprop **)

let isaprop_issuperrigid t =
  isapropdirprod (isaprop_isrigid t)
    (impred (S O) (fun t0 -> isaprop_isrigid (coq_Up t t0)))

(** val isWellFoundedUp : coq_Tree -> hProp **)

let isWellFoundedUp t = false
  (* hasSmallest t.pr1.pr2.pr1 *)

(** val hasLargest : 'a1 hrel -> hProp **)

let hasLargest _ =
  forall_hProp (fun _ -> himpl ishinh)

(** val isWellFoundedDown : coq_Tree -> hProp **)

let isWellFoundedDown t =
  hasLargest t.pr1.pr2.pr1

type coq_Tree_isWellFounded = (hProptoType, hProptoType) dirprod

(** val isaprop_Tree_isWellFounded :
    coq_Tree -> coq_Tree_isWellFounded isaprop **)

let isaprop_Tree_isWellFounded t = false
  (* isapropdirprod (propproperty (isWellFoundedUp t)) *)
  (*   (propproperty (isWellFoundedDown t)) *)

type ispreZFS = (coq_Tree_isWellFounded, issuperrigid) dirprod

(** val isaprop_ispreZFS : coq_Tree -> ispreZFS isaprop **)

let isaprop_ispreZFS t = false
  (* isapropdirprod (isaprop_Tree_isWellFounded t) (isaprop_issuperrigid t) *)

type preZFS = (coq_Tree, ispreZFS) total2

(** val coq_Ve : preZFS -> hSet **)

let coq_Ve x =
  x.pr1.pr1.pr1

(** val coq_Ed : preZFS -> pr1hSet -> pr1hSet -> hProp **)

let coq_Ed x =
  x.pr1.pr1.pr2.pr1

(** val root : preZFS -> pr1hSet **)

let root x =
  x.pr1.pr1.pr2.pr2.pr1

(** val preZFS_isrigid : preZFS -> preZFS paths iscontr **)

let preZFS_isrigid x =
  Obj.magic pr1contr_to_contr (fun x0 -> { pr1 = __; pr2 =
    (isaprop_ispreZFS x0) }) x x.pr2.pr2.pr1

(** val isaset_preZFS : preZFS isaset **)

let isaset_preZFS x _ =
  Obj.magic (fun _ q ->
    Obj.magic hlevelntosn O (preZFS_isrigid x) Coq_paths_refl q)

type preZFS_iso = coq_Tree_iso

(** val preZFS_univalence :
    preZFS -> preZFS -> (preZFS paths, preZFS_iso) weq **)

let preZFS_univalence x y =
  let q = fun x0 -> { pr1 = __; pr2 = (isaprop_ispreZFS x0) } in
  Obj.magic substructure_univalence coq_Tree_univalence q x y

(** val preZFS_Branch : preZFS -> pr1hSet -> coq_Tree **)

let preZFS_Branch t x =
  coq_Up t.pr1 x

(** val preZFS_Branch_hsubtype_tohsubtype :
    preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet hsubtype **)

let preZFS_Branch_hsubtype_tohsubtype _ _ _ _ =
  ishinh

(** val hsubtype_to_preZFS_Branch_hsubtype :
    preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet hsubtype **)

let hsubtype_to_preZFS_Branch_hsubtype t x s z =
  hconj (s (Obj.magic z).pr1) (coq_Ed t x (Obj.magic z).pr1)

(** val coq_Branch_to_subtype :
    preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet hsubtype paths **)


(** val fromBranch_hsubtype :
    preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet -> hProptoType ->
    hProptoType **)

let fromBranch_hsubtype _ _ _ t s =
  Obj.magic (fun _ x -> x { pr1 = (Obj.magic t).pr2; pr2 = s })

(** val toBranch_hsubtype :
    preZFS -> pr1hSet -> pr1hSet hsubtype -> pr1hSet -> hProptoType ->
    hProptoType -> hProptoType **)

let toBranch_hsubtype _ _ _ _ e s =
  Obj.magic { pr1 = s; pr2 = e }

(** val preZFS_Branch_isWellFounded :
    preZFS -> pr1hSet -> coq_Tree_isWellFounded **)

let preZFS_Branch_isWellFounded t x = t x
  (* { pr1 = *)
  (*   (Obj.magic (fun s -> *)
  (*     let sS = preZFS_Branch_hsubtype_tohsubtype t x s in *)
  (*     (fun x0 -> *)
  (*     let wfunder = t.pr2.pr1 in *)
  (*     let wfunder0 = wfunder.pr1 in *)
  (*     let l1 = Obj.magic wfunder0 sS in *)
  (*     let l2 = fun p -> *)
  (*       p ishinh (fun x1 -> *)
  (*         let te = x1.pr1 in *)
  (*         let s0 = x1.pr2 in *)
  (*         let t0 = te.pr1 in *)
  (*         let e = te.pr2 in *)
  (*         (fun _ x2 -> *)
  (*         x2 { pr1 = t0; pr2 = *)
  (*           (fromBranch_hsubtype t x s (Obj.magic { pr1 = t0; pr2 = e }) s0) })) *)
  (*     in *)
  (*     let x1 = l2 x0 in *)
  (*     l1 x1 ishinh (fun y -> *)
  (*       let t0 = y.pr1 in *)
  (*       let pr3 = y.pr2 in *)
  (*       let s0 = pr3.pr1 in *)
  (*       let _UU03c0_ = pr3.pr2 in *)
  (*       let e = s0 (coq_Ed t x t0) (fun y0 -> y0.pr1) in *)
  (*       let l4 = *)
  (*         internal_paths_rew *)
  (*           (hsubtype_to_preZFS_Branch_hsubtype t x *)
  (*             (preZFS_Branch_hsubtype_tohsubtype t x s)) *)
  (*           (toBranch_hsubtype t x sS t0 e (Obj.magic s0)) s *)
  (*           (coq_Branch_to_subtype t x s) *)
  (*       in *)
  (*       (fun _ y0 -> *)
  (*       y0 { pr1 = { pr1 = t0; pr2 = e }; pr2 = { pr1 = l4; pr2 = *)
  (*         (fun xx q -> *)
  (*         _UU03c0_ xx.pr1 (fun _ z -> z { pr1 = xx.pr2; pr2 = q })) } }))))); *)
  (*   pr2 = *)
  (*   (Obj.magic (fun s -> *)
  (*     let sS = preZFS_Branch_hsubtype_tohsubtype t x s in *)
  (*     (fun x0 -> *)
  (*     let wfunder = t.pr2.pr1.pr2 in *)
  (*     let l1 = Obj.magic wfunder sS in *)
  (*     let l2 = fun y -> *)
  (*       y ishinh (fun z -> *)
  (*         let te = z.pr1 in *)
  (*         let s0 = z.pr2 in *)
  (*         let t0 = te.pr1 in *)
  (*         let e = te.pr2 in *)
  (*         (fun _ w -> *)
  (*         w { pr1 = t0; pr2 = *)
  (*           (fromBranch_hsubtype t x s (Obj.magic { pr1 = t0; pr2 = e }) s0) })) *)
  (*     in *)
  (*     let x1 = l2 x0 in *)
  (*     l1 x1 ishinh (fun y -> *)
  (*       let t0 = y.pr1 in *)
  (*       let pr3 = y.pr2 in *)
  (*       let s0 = pr3.pr1 in *)
  (*       let _UU03c0_ = pr3.pr2 in *)
  (*       let e = s0 (coq_Ed t x t0) (fun y0 -> y0.pr1) in *)
  (*       let l4 = *)
  (*         internal_paths_rew *)
  (*           (hsubtype_to_preZFS_Branch_hsubtype t x *)
  (*             (preZFS_Branch_hsubtype_tohsubtype t x s)) *)
  (*           (toBranch_hsubtype t x sS t0 e (Obj.magic s0)) s *)
  (*           (coq_Branch_to_subtype t x s) *)
  (*       in *)
  (*       (fun _ y0 -> *)
  (*       y0 { pr1 = { pr1 = t0; pr2 = e }; pr2 = { pr1 = l4; pr2 = *)
  (*         (fun xx q -> *)
  (*         _UU03c0_ xx.pr1 (fun _ z -> z { pr1 = xx.pr2; pr2 = q })) } }))))) } *)

(** val iscontrauto_Tree_TRRGraph :
    coq_Tree -> isrigid -> coq_TRRGraph paths iscontr **)

let iscontrauto_Tree_TRRGraph t =
  Obj.magic contr_to_pr1contr (fun x -> { pr1 = __; pr2 =
    (isaprop_isatree x) }) t

(** val coq_Up_to_Up :
    coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet **)

let coq_Up_to_Up t x y x0 =
  let t0 = (Obj.magic x0).pr1 in
  let _UU03c0_ = (Obj.magic x0).pr2 in
  let y0 = (Obj.magic y).pr1 in
  let _UU03c3_ = (Obj.magic y).pr2 in
  Obj.magic { pr1 = { pr1 = t0; pr2 =
    (t.pr1.pr2.pr2.pr2.pr2.pr1 x y0 t0 _UU03c3_ _UU03c0_) }; pr2 = _UU03c0_ }

(** val coq_Up_to_Up_inv :
    coq_Tree -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet **)

let coq_Up_to_Up_inv _ _ _ x =
  let t = (Obj.magic x).pr1 in
  let _UU03c0_ = (Obj.magic x).pr2 in
  let tt = t.pr1 in Obj.magic { pr1 = tt; pr2 = _UU03c0_ }

(** val isweq_Up_to_Up :
    coq_Tree -> pr1hSet -> pr1hSet -> (pr1hSet, pr1hSet) isweq **)

let isweq_Up_to_Up t x y = t
  (* let f = coq_Up_to_Up t x y in *)
  (* let g = coq_Up_to_Up_inv t x y in *)
  (* let l = fun z -> *)
  (*   let z0 = z.pr1 in *)
  (*   let _UU03c0_ = z.pr2 in *)
  (*   let x0 = fun x0 y0 -> (total2_paths_equiv x0 y0).pr2 in *)
  (*   let x1 = fun x1 y0 y1 -> (x0 x1 y0 y1).pr1 in *)
  (*   let x2 = { pr1 = { pr1 = z0.pr1; pr2 = *)
  (*     (t.pr1.pr2.pr2.pr2.pr2.pr1 x (Obj.magic y).pr1 z0.pr1 (Obj.magic y).pr2 *)
  (*       _UU03c0_) }; pr2 = _UU03c0_ } *)
  (*   in *)
  (*   let y0 = { pr1 = z0; pr2 = _UU03c0_ } in *)
  (*   let y1 = *)
  (*     let h = *)
  (*       let x3 = fun x3 y1 -> (total2_paths_equiv x3 y1).pr2 in *)
  (*       let x4 = fun x4 y1 y2 -> (x3 x4 y1 y2).pr1 in *)
  (*       let x5 = { pr1 = z0.pr1; pr2 = *)
  (*         (t.pr1.pr2.pr2.pr2.pr2.pr1 x (Obj.magic y).pr1 z0.pr1 *)
  (*           (Obj.magic y).pr2 _UU03c0_) } *)
  (*       in *)
  (*       let y1 = { pr1 = Coq_paths_refl; pr2 = *)
  (*         (let p = t.pr1.pr2.pr1 x z0.pr1 in *)
  (*          let x6 = *)
  (*            transportf z0.pr1 z0.pr1 Coq_paths_refl *)
  (*              (t.pr1.pr2.pr2.pr2.pr2.pr1 x (Obj.magic y).pr1 z0.pr1 *)
  (*                (Obj.magic y).pr2 _UU03c0_) *)
  (*          in *)
  (*          let x' = z0.pr2 in (Obj.magic propproperty p x6 x').pr1) } *)
  (*       in *)
  (*       (x4 x5 z0 y1).pr1 *)
  (*     in *)
  (*     { pr1 = h; pr2 = *)
  (*     (let p = (Obj.magic coq_Up t x).pr1.pr2.pr1 y z0 in *)
  (*      let x3 = *)
  (*        transportf { pr1 = z0.pr1; pr2 = *)
  (*          (t.pr1.pr2.pr2.pr2.pr2.pr1 x (Obj.magic y).pr1 z0.pr1 *)
  (*            (Obj.magic y).pr2 _UU03c0_) } z0 h _UU03c0_ *)
  (*      in *)
  (*      (Obj.magic propproperty p x3 _UU03c0_).pr1) } *)
  (*   in *)
  (*   (x1 x2 y0 y1).pr1 *)
  (* in *)
  (* let lL = fun _ -> Coq_paths_refl in *)
  (* let x0 = (weq_iso (Obj.magic f) (Obj.magic g) lL l).pr2 in Obj.magic x0 *)

(** val isTRRGhomo_Up_to_Up : coq_Tree -> pr1hSet -> pr1hSet -> isTRRGhomo **)

let isTRRGhomo_Up_to_Up t x y =
  { pr1 = (fun _ _ -> { pr1 = (fun p -> p); pr2 = (fun p -> p) }); pr2 =
    (let x0 = fun x0 y0 -> (total2_paths_equiv x0 y0).pr2 in
     let x1 = fun x1 y0 y1 -> (x0 x1 y0 y1).pr1 in
     let x2 = fun x2 y0 y1 -> (x1 x2 y0 y1).pr1 in
     Obj.magic x2 { pr1 = { pr1 = (Obj.magic y).pr1; pr2 =
       (t.pr1.pr2.pr2.pr2.pr2.pr1 x (Obj.magic y).pr1 (Obj.magic y).pr1
         (Obj.magic y).pr2 (selfedge t.pr1 (Obj.magic y).pr1)) }; pr2 =
       (selfedge t.pr1 (Obj.magic y).pr1) }
       (coq_TRRG_root (coq_Upw_to_TRRGraph (coq_Up t x) y))
       (let y0 = (Obj.magic y).pr1 in
        let _UU03c0_ = (Obj.magic y).pr2 in
        let q =
          let p = t.pr1.pr2.pr1 x y0 in
          let x3 =
            t.pr1.pr2.pr2.pr2.pr2.pr1 x y0 y0 _UU03c0_ (selfedge t.pr1 y0)
          in
          (Obj.magic propproperty p x3 _UU03c0_).pr1
        in
        internal_paths_rew_r
          (t.pr1.pr2.pr2.pr2.pr2.pr1 x y0 y0 _UU03c0_ (selfedge t.pr1 y0))
          _UU03c0_ { pr1 = Coq_paths_refl; pr2 =
          (let p =
             coq_Upw_E t x (Obj.magic { pr1 = y0; pr2 = _UU03c0_ })
               (Obj.magic coq_TRRG_root
                 (coq_Upw_to_TRRGraph (coq_Up t x)
                   (Obj.magic { pr1 = y0; pr2 = _UU03c0_ }))).pr1
           in
           let x3 =
             transportf { pr1 = y0; pr2 = _UU03c0_ }
               (Obj.magic coq_TRRG_root
                 (coq_Upw_to_TRRGraph (coq_Up t x)
                   (Obj.magic { pr1 = y0; pr2 = _UU03c0_ }))).pr1
               Coq_paths_refl (selfedge t.pr1 y0)
           in
           let x' =
             (Obj.magic coq_TRRG_root
               (coq_Upw_to_TRRGraph (coq_Up t x)
                 (Obj.magic { pr1 = y0; pr2 = _UU03c0_ }))).pr2
           in
           (Obj.magic propproperty p x3 x').pr1) } q)) }

(** val coq_UpUpid : coq_Tree -> pr1hSet -> pr1hSet -> coq_TRRGraph paths **)

let coq_UpUpid t x y = t
  (* let x0 = fun g h -> (coq_TRRGraph_univalence g h).pr2 in *)
  (* let x1 = fun g h y0 -> (x0 g h y0).pr1 in *)
  (* let g = (coq_Up t (Obj.magic y).pr1).pr1 in *)
  (* let h = coq_Upw_to_TRRGraph (coq_Up t x) y in *)
  (* let y0 = { pr1 = (make_weq (coq_Up_to_Up t x y) (isweq_Up_to_Up t x y)); *)
  (*   pr2 = (isTRRGhomo_Up_to_Up t x y) } *)
  (* in *)
  (* (x1 g h y0).pr1 *)

(** val preZFS_Branch_issuperrigid : preZFS -> pr1hSet -> issuperrigid **)

let preZFS_Branch_issuperrigid t x = t
  (* { pr1 = *)
  (*   (Obj.magic pr1contr_to_contr (fun x0 -> { pr1 = __; pr2 = *)
  (*     (isaprop_isatree x0) }) (preZFS_Branch t x) *)
  (*     (iscontrauto_Tree_TRRGraph (coq_Up t.pr1 x) (t.pr2.pr2.pr2 x))); pr2 = *)
  (*   (fun y -> *)
  (*   Obj.magic pr1contr_to_contr (fun x0 -> { pr1 = __; pr2 = *)
  (*     (isaprop_isatree x0) }) (coq_Up (preZFS_Branch t x) y) *)
  (*     (internal_paths_rew (coq_Up t.pr1 (Obj.magic y).pr1).pr1 *)
  (*       (iscontrauto_Tree_TRRGraph (coq_Up t.pr1 (Obj.magic y).pr1) *)
  (*         (t.pr2.pr2.pr2 (Obj.magic y).pr1)) *)
  (*       (coq_Upw_to_TRRGraph (coq_Up t.pr1 x) y) (coq_UpUpid t.pr1 x y))) } *)

(** val coq_Branch : preZFS -> pr1hSet -> preZFS **)

let coq_Branch t x = t x
  (* { pr1 = (preZFS_Branch t x); pr2 = { pr1 = *)
  (*   (preZFS_Branch_isWellFounded t x); pr2 = *)
  (*   (preZFS_Branch_issuperrigid t x) } } *)

type hasuniquerepbranch = pr1hSet -> pr1hSet -> preZFS paths -> pr1hSet paths

(** val isaprop_hasuniquerepbranch : preZFS -> hasuniquerepbranch isaprop **)

let isaprop_hasuniquerepbranch t =
  impred (S O) (fun t0 ->
    impred (S O) (fun t1 ->
      impred (S O) (fun _ -> setproperty (coq_Ve t) t0 t1)))

type coq_ZFS = (preZFS, hasuniquerepbranch) total2

(** val pr1ZFS : coq_ZFS -> preZFS **)

let pr1ZFS x =
  x.pr1

type coq_ZFS_iso = preZFS_iso

(** val coq_ZFS_univalence :
    coq_ZFS -> coq_ZFS -> (coq_ZFS paths, coq_ZFS_iso) weq **)

let coq_ZFS_univalence x y =
  let q = fun x0 -> { pr1 = __; pr2 = (isaprop_hasuniquerepbranch x0) } in
  Obj.magic substructure_univalence preZFS_univalence q x y

(** val isaset_ZFS : coq_ZFS isaset **)

let isaset_ZFS =
  Obj.magic isofhleveltotal2 (S (S O)) isaset_preZFS (fun x ->
    hlevelntosn (S O) (isaprop_hasuniquerepbranch x))

(** val coq_Branch_of_Branch_to_Branch :
    preZFS -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet **)

let coq_Branch_of_Branch_to_Branch _ _ _ x =
  let pr3 = (Obj.magic x).pr1 in
  let e = pr3.pr1 in
  let _UU03c0_ = (Obj.magic x).pr2 in Obj.magic { pr1 = e; pr2 = _UU03c0_ }

(** val coq_Branch_of_Branch_to_Branch_inv :
    preZFS -> pr1hSet -> pr1hSet -> pr1hSet -> pr1hSet **)

let coq_Branch_of_Branch_to_Branch_inv t x y x0 =
  Obj.magic { pr1 = { pr1 = (Obj.magic x0).pr1; pr2 =
    (t.pr1.pr1.pr2.pr2.pr2.pr2.pr1 x (Obj.magic y).pr1 (Obj.magic x0).pr1
      (Obj.magic y).pr2 (Obj.magic x0).pr2) }; pr2 = (Obj.magic x0).pr2 }

(** val isweq_Branch_of_Branch_to_Branch :
    preZFS -> pr1hSet -> pr1hSet -> (pr1hSet, pr1hSet) isweq **)

let isweq_Branch_of_Branch_to_Branch t x y =
  let f = coq_Branch_of_Branch_to_Branch t x y in
  let g = coq_Branch_of_Branch_to_Branch_inv t x y in
  let l = fun _ -> Coq_paths_refl in
  let lL = fun z ->
    let z0 = z.pr1 in
    let _UU03c0_ = z.pr2 in
    let x0 = fun x0 y0 -> (total2_paths_equiv x0 y0).pr2 in
    let x1 = fun x1 y0 y1 -> (x0 x1 y0 y1).pr1 in
    let x2 = { pr1 = { pr1 = z0.pr1; pr2 =
      (t.pr1.pr1.pr2.pr2.pr2.pr2.pr1 x (Obj.magic y).pr1 z0.pr1
        (Obj.magic y).pr2 _UU03c0_) }; pr2 = _UU03c0_ }
    in
    let y0 = { pr1 = z0; pr2 = _UU03c0_ } in
    let y1 =
      let h =
        let x3 = fun x3 y1 -> (total2_paths_equiv x3 y1).pr2 in
        let x4 = fun x4 y1 y2 -> (x3 x4 y1 y2).pr1 in
        let x5 = { pr1 = z0.pr1; pr2 =
          (t.pr1.pr1.pr2.pr2.pr2.pr2.pr1 x (Obj.magic y).pr1 z0.pr1
            (Obj.magic y).pr2 _UU03c0_) }
        in
        let y1 = { pr1 = Coq_paths_refl; pr2 =
          (let p = t.pr1.pr1.pr2.pr1 x z0.pr1 in
           let x6 =
             transportf z0.pr1 z0.pr1 Coq_paths_refl
               (t.pr1.pr1.pr2.pr2.pr2.pr2.pr1 x (Obj.magic y).pr1 z0.pr1
                 (Obj.magic y).pr2 _UU03c0_)
           in
           let x' = z0.pr2 in (Obj.magic propproperty p x6 x').pr1) }
        in
        (x4 x5 z0 y1).pr1
      in
      { pr1 = h; pr2 =
      (let p = coq_Upw_E t.pr1 x y (Obj.magic z0) in
       let x3 =
         transportf { pr1 = z0.pr1; pr2 =
           (t.pr1.pr1.pr2.pr2.pr2.pr2.pr1 x (Obj.magic y).pr1 z0.pr1
             (Obj.magic y).pr2 _UU03c0_) } z0 h _UU03c0_
       in
       (Obj.magic propproperty p x3 _UU03c0_).pr1) }
    in
    (x1 x2 y0 y1).pr1
  in
  let x0 = (weq_iso (Obj.magic f) (Obj.magic g) lL l).pr2 in Obj.magic x0

(** val isTRRGhomo_Branch_of_Branch_to_Branch :
    preZFS -> pr1hSet -> pr1hSet -> isTRRGhomo **)

let isTRRGhomo_Branch_of_Branch_to_Branch t x y =
  { pr1 = (fun _ _ -> { pr1 = (fun p -> p); pr2 = (fun p -> p) }); pr2 =
    (let x0 = fun x0 y0 -> (total2_paths_equiv x0 y0).pr2 in
     let x1 = fun x1 y0 y1 -> (x0 x1 y0 y1).pr1 in
     let x2 = fun x2 y0 y1 -> (x1 x2 y0 y1).pr1 in
     Obj.magic x2 { pr1 = (Obj.magic y).pr1; pr2 =
       (selfedge (coq_Upw_to_TRRGraph t.pr1 x) y) }
       (coq_TRRG_root (coq_Upw_to_TRRGraph t.pr1 (Obj.magic y).pr1))
       (let y0 = (Obj.magic y).pr1 in
        let _UU03c0_ = (Obj.magic y).pr2 in
        { pr1 = Coq_paths_refl; pr2 =
        (let p =
           t.pr1.pr1.pr2.pr1 y0
             (Obj.magic coq_TRRG_root (coq_Upw_to_TRRGraph t.pr1 y0)).pr1
         in
         let x3 =
           transportf y0
             (Obj.magic coq_TRRG_root (coq_Upw_to_TRRGraph t.pr1 y0)).pr1
             Coq_paths_refl
             (selfedge (coq_Upw_to_TRRGraph t.pr1 x)
               (Obj.magic { pr1 = y0; pr2 = _UU03c0_ }))
         in
         let x' = (Obj.magic coq_TRRG_root (coq_Upw_to_TRRGraph t.pr1 y0)).pr2
         in
         (Obj.magic propproperty p x3 x').pr1) })) }

(** val coq_Branch_of_Branch_eq_Branch :
    preZFS -> pr1hSet -> pr1hSet -> preZFS paths **)

let coq_Branch_of_Branch_eq_Branch t x y = t
  (* let x0 = fun x0 y0 -> (preZFS_univalence x0 y0).pr2 in *)
  (* let x1 = fun x1 y0 y1 -> (x0 x1 y0 y1).pr1 in *)
  (* let x2 = coq_Branch (coq_Branch t x) y in *)
  (* let y0 = coq_Branch t (Obj.magic y).pr1 in *)
  (* let y1 = { pr1 = { pr1 = (coq_Branch_of_Branch_to_Branch t x y); pr2 = *)
  (*   (isweq_Branch_of_Branch_to_Branch t x y) }; pr2 = *)
  (*   (isTRRGhomo_Branch_of_Branch_to_Branch t x y) } *)
  (* in *)
  (* (x1 x2 y0 y1).pr1 *)

(** val coq_ZFS_Branch_is_ZFS : coq_ZFS -> pr1hSet -> hasuniquerepbranch **)

let coq_ZFS_Branch_is_ZFS x x0 y z = x
  (* internal_paths_rew_r (coq_Branch (coq_Branch (pr1ZFS x) x0) y) *)
  (*   (coq_Branch (pr1ZFS x) (Obj.magic y).pr1) *)
  (*   (internal_paths_rew_r (coq_Branch (coq_Branch (pr1ZFS x) x0) z) *)
  (*     (coq_Branch (pr1ZFS x) (Obj.magic z).pr1) (fun p -> *)
  (*     let _UU03c0_ = x.pr2 in *)
  (*     let _UU03c4_ = _UU03c0_ (Obj.magic y).pr1 (Obj.magic z).pr1 p in *)
  (*     let x1 = fun x1 y0 -> (total2_paths_equiv x1 y0).pr2 in *)
  (*     let x2 = fun x2 y0 y1 -> (x1 x2 y0 y1).pr1 in *)
  (*     let x3 = fun x3 y0 y1 -> (x2 x3 y0 y1).pr1 in *)
  (*     Obj.magic x3 y z { pr1 = _UU03c4_; pr2 = *)
  (*       (let p0 = (pr1ZFS x).pr1.pr1.pr2.pr1 x0 (Obj.magic z).pr1 in *)
  (*        let x4 = *)
  (*          transportf (Obj.magic y).pr1 (Obj.magic z).pr1 _UU03c4_ *)
  (*            (Obj.magic y).pr2 *)
  (*        in *)
  (*        let x' = (Obj.magic z).pr2 in (Obj.magic propproperty p0 x4 x').pr1) }) *)
  (*     (coq_Branch_of_Branch_eq_Branch (pr1ZFS x) x0 z)) *)
  (*   (coq_Branch_of_Branch_eq_Branch (pr1ZFS x) x0 y) *)

(** val coq_ZFS_Branch : coq_ZFS -> pr1hSet -> coq_ZFS **)

let coq_ZFS_Branch x x0 =
  { pr1 = (coq_Branch (pr1ZFS x) x0); pr2 = (coq_ZFS_Branch_is_ZFS x x0) }

(** val coq_Root : coq_ZFS -> pr1hSet **)

let coq_Root x =
  x.pr1.pr1.pr1.pr2.pr2.pr1

(** val isapoint : coq_ZFS -> pr1hSet -> hProp **)

let isapoint _ _ =
  hneg

(** val isaprop_isapoint : coq_ZFS -> pr1hSet -> hProptoType isaprop **)

let isaprop_isapoint _ _ =
  impred (S O) (fun _ -> isapropempty)

type coq_ZFS_elementof =
  (pr1hSet, (hProptoType, coq_ZFS paths) dirprod) total2

(** val isaprop_ZFS_elementof :
    coq_ZFS -> coq_ZFS -> coq_ZFS_elementof isaprop **)

let isaprop_ZFS_elementof x y =x
  (* invproofirrelevance (fun z w -> *)
  (*   let z0 = z.pr1 in *)
  (*   let pr3 = z.pr2 in *)
  (*   let ispp = pr3.pr1 in *)
  (*   let p = pr3.pr2 in *)
  (*   let w0 = w.pr1 in *)
  (*   let pr4 = w.pr2 in *)
  (*   let ispq = pr4.pr1 in *)
  (*   let q = pr4.pr2 in *)
  (*   let r = *)
  (*     pathscomp0 (coq_ZFS_Branch y w0) x (coq_ZFS_Branch y z0) *)
  (*       (pathsinv0 x (coq_ZFS_Branch y w0) q) p *)
  (*   in *)
  (*   let x0 = fun x0 y0 -> (total2_paths_equiv x0 y0).pr1 in *)
  (*   let r0 = x0 (coq_ZFS_Branch y w0) (coq_ZFS_Branch y z0) r in *)
  (*   let r1 = r0.pr1 in *)
  (*   let s = y.pr2 w0 z0 r1 in *)
  (*   let _UU03c4_ = fun y0 -> *)
  (*     isapropdirprod (isaprop_isapoint y y0) *)
  (*       (isaset_ZFS x (coq_ZFS_Branch y y0)) *)
  (*   in *)
  (*   let p0 = fun y0 -> { pr1 = __; pr2 = (_UU03c4_ y0) } in *)
  (*   let x1 = *)
  (*     (total2_paths_hProp_equiv p0 { pr1 = z0; pr2 = *)
  (*       (Obj.magic { pr1 = ispp; pr2 = p }) } { pr1 = w0; pr2 = *)
  (*       (Obj.magic { pr1 = ispq; pr2 = q }) }).pr2 *)
  (*   in *)
  (*   let x2 = fun y0 -> (x1 y0).pr1 in *)
  (*   let x3 = fun y0 -> (x2 y0).pr1 in Obj.magic x3 (pathsinv0 w0 z0 s)) *)

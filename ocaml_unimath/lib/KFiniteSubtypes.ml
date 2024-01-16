open FiniteSets
open KFiniteTypes
open PartA
open PartA0
open Preamble
open Propositions
open Sets
open StandardFiniteSets
open Subtypes

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val iskfinite_singleton : 'a1 -> 'a1 carrier iskfinite **)

let iskfinite_singleton x =
  kfinstruct_iskfinite
    (make_kfinstruct (S O) (fun _ -> { pr1 = x; pr2 =
      (hinhpr Coq_paths_refl) }) (fun y ->
      let z = y.pr1 in
      let xz = y.pr2 in
      hinhfun (fun x0 ->
        make_hfiber (fun _ -> { pr1 = x; pr2 = (hinhpr Coq_paths_refl) })
          { pr1 = z; pr2 = xz } { pr1 = O; pr2 = Coq_paths_refl }
          (subtypePath_prop (singleton x) { pr1 = x; pr2 =
            (hinhpr Coq_paths_refl) } { pr1 = z; pr2 = xz }
            (pathsinv0 z x x0))) xz))

(** val indexed_carrier_to_carrier_union :
    ('a2 -> 'a1 hsubtype) -> ('a2, 'a1 carrier) total2 -> 'a1 carrier **)

let indexed_carrier_to_carrier_union _ h =
  { pr1 = h.pr2.pr1; pr2 = (hinhpr { pr1 = h.pr1; pr2 = h.pr2.pr2 }) }

(** val issurjective_indexed_carrier_to_union :
    ('a2 -> 'a1 hsubtype) -> (('a2, 'a1 carrier) total2, 'a1 carrier)
    issurjective **)

let issurjective_indexed_carrier_to_union index y =
  let x = y.pr1 in
  let in_union = y.pr2 in
  hinhfun (fun x0 ->
    let i = x0.pr1 in
    let in_index = x0.pr2 in
    make_hfiber (indexed_carrier_to_carrier_union index) { pr1 = x; pr2 =
      in_union } { pr1 = i; pr2 = { pr1 = x; pr2 = in_index } }
      (subtypePath_prop (subtype_union index)
        (indexed_carrier_to_carrier_union index { pr1 = i; pr2 = { pr1 = x;
          pr2 = in_index } }) { pr1 = x; pr2 = in_union } Coq_paths_refl))
    in_union

(** val reindex_carrier_union :
    ('a2 -> 'a1 hsubtype) -> ('a3 -> 'a2) -> 'a1 carrier -> 'a1 carrier **)

let reindex_carrier_union index g =
  subtype_inc (subtype_union (funcomp g index)) (subtype_union index)
    (Obj.magic (fun _ -> hinhfun (fpmap g)))

(** val issurjective_reindex_carrier_union :
    ('a2 -> 'a1 hsubtype) -> ('a3 -> 'a2) -> ('a3, 'a2) issurjective -> ('a1
    carrier, 'a1 carrier) issurjective **)

let issurjective_reindex_carrier_union index g gsurjective y =
  let x = y.pr1 in
  let in_union = y.pr2 in
  hinhfun (fun x0 ->
    let i = x0.pr1 in
    let index_ix = x0.pr2 in
    make_hfiber (reindex_carrier_union index g) { pr1 = x; pr2 = in_union }
      { pr1 = x; pr2 =
      (hinhfun (fun x1 ->
        let j = x1.pr1 in
        let jpath = x1.pr2 in
        { pr1 = j; pr2 =
        (transportb (funcomp g index j x) (index i x)
          (eqtohomot (funcomp g index j) (index i)
            (maponpaths index (g j) i jpath) x) index_ix) }) (gsurjective i)) }
      (subtypePath_prop (subtype_union index)
        (reindex_carrier_union index g { pr1 = x; pr2 =
          (hinhfun (fun x1 -> { pr1 = x1.pr1; pr2 =
            (transportb (funcomp g index x1.pr1 x) (index i x)
              (eqtohomot (funcomp g index x1.pr1) (index i)
                (maponpaths index (g x1.pr1) i x1.pr2) x) index_ix) })
            (gsurjective i)) }) { pr1 = x; pr2 = in_union } Coq_paths_refl))
    in_union

(** val kfinstruct_union :
    ('a1 -> 'a2 hsubtype) -> 'a1 kfinstruct -> ('a1 -> 'a2 carrier
    kfinstruct) -> 'a2 carrier kfinstruct **)

let kfinstruct_union index g index_finite =
  kfinstruct_from_surjection (reindex_carrier_union index (kfinstruct_map g))
    (issurjective_reindex_carrier_union index (kfinstruct_map g)
      (issurjective_kfinstruct g))
    (kfinstruct_from_surjection
      (indexed_carrier_to_carrier_union (funcomp (kfinstruct_map g) index))
      (issurjective_indexed_carrier_to_union
        (funcomp (kfinstruct_map g) index))
      (kfinstruct_stn_indexed (kfinstruct_cardinality g) (fun k ->
        index_finite (kfinstruct_map g k))))

(** val iskfinite_union :
    ('a1 -> 'a2 hsubtype) -> hProptoType -> ('a1 -> 'a2 carrier iskfinite) ->
    'a2 carrier iskfinite **)

let iskfinite_union index ifinite index_finite =
  let finitechoicebase =
    Obj.magic ischoicebasefiniteset ifinite __ index_finite
  in
  hinhfun2 (fun x0 -> kfinstruct_union index (kfinstruct_finstruct x0))
    ifinite finitechoicebase

(** val iskfinite_binary_union :
    'a1 hsubtype -> 'a1 hsubtype -> 'a1 carrier iskfinite -> 'a1 carrier
    iskfinite -> 'a1 carrier iskfinite **)

let iskfinite_binary_union a b afinite bfinite =
  hinhfun2 (fun afinstruct bfinstruct ->
    make_kfinstruct
      (add (kfinstruct_cardinality afinstruct)
        (kfinstruct_cardinality bfinstruct))
      (funcomp
        (funcomp
          (let x0 = fun n m -> (weqfromcoprodofstn n m).pr2 in
           let x1 = fun n m y -> (x0 n m y).pr1 in
           let n = kfinstruct_cardinality afinstruct in
           let m = kfinstruct_cardinality bfinstruct in
           (fun y -> (x1 n m y).pr1))
          (coprodf (kfinstruct_map afinstruct) (kfinstruct_map bfinstruct)))
        (coprod_carrier_binary_union a b))
      (issurjcomp
        (funcomp
          (let x0 = fun n m -> (weqfromcoprodofstn n m).pr2 in
           let x1 = fun n m y -> (x0 n m y).pr1 in
           let n = kfinstruct_cardinality afinstruct in
           let m = kfinstruct_cardinality bfinstruct in
           (fun y -> (x1 n m y).pr1))
          (coprodf (kfinstruct_map afinstruct) (kfinstruct_map bfinstruct)))
        (coprod_carrier_binary_union a b)
        (issurjcomp
          (let x0 = fun n m -> (weqfromcoprodofstn n m).pr2 in
           let x1 = fun n m y -> (x0 n m y).pr1 in
           let n = kfinstruct_cardinality afinstruct in
           let m = kfinstruct_cardinality bfinstruct in
           (fun y -> (x1 n m y).pr1))
          (coprodf (kfinstruct_map afinstruct) (kfinstruct_map bfinstruct))
          (issurjectiveweq
            (let x0 = fun n m -> (weqfromcoprodofstn n m).pr2 in
             let x1 = fun n m y -> (x0 n m y).pr1 in
             let n = kfinstruct_cardinality afinstruct in
             let m = kfinstruct_cardinality bfinstruct in
             (fun y -> (x1 n m y).pr1))
            (isweqinvmap
              (weqfromcoprodofstn (kfinstruct_cardinality afinstruct)
                (kfinstruct_cardinality bfinstruct))))
          (issurjective_coprodf (kfinstruct_map afinstruct)
            (kfinstruct_map bfinstruct) (issurjective_kfinstruct afinstruct)
            (issurjective_kfinstruct bfinstruct)))
        (issurjective_coprod_carrier_binary_union a b))) afinite bfinite

type 'x kfinite_subtype = ('x hsubtype, 'x carrier iskfinite) total2

(** val subtype_from_kfinite_subtype : 'a1 kfinite_subtype -> 'a1 hsubtype **)

let subtype_from_kfinite_subtype x =
  x.pr1

(** val kfinite_subtype_property :
    'a1 kfinite_subtype -> 'a1 carrier iskfinite **)

let kfinite_subtype_property a =
  a.pr2

(** val make_kfinite_subtype :
    'a1 hsubtype -> 'a1 carrier iskfinite -> 'a1 kfinite_subtype **)

let make_kfinite_subtype a finite_carrier =
  { pr1 = a; pr2 = finite_carrier }

(** val kfinite_subtype_union_subproof :
    ('a2 -> 'a1 kfinite_subtype) -> hProptoType -> 'a1 carrier iskfinite **)

let kfinite_subtype_union_subproof index index_finite =
  iskfinite_union (fun x -> subtype_from_kfinite_subtype (index x))
    index_finite (fun i -> kfinite_subtype_property (index i))

(** val kfinite_subtype_union :
    ('a2 -> 'a1 kfinite_subtype) -> hProptoType -> 'a1 kfinite_subtype **)

let kfinite_subtype_union index index_finite =
  make_kfinite_subtype
    (subtype_union (fun x -> subtype_from_kfinite_subtype (index x)))
    (kfinite_subtype_union_subproof index index_finite)

(** val kfinite_subtype_singleton : 'a1 -> 'a1 kfinite_subtype **)

let kfinite_subtype_singleton x =
  make_kfinite_subtype (singleton x) (iskfinite_singleton x)

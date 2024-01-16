open Notations
open PartA
open PartA0
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Sets
open UnivalenceAxiom

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val ishinh_irrel : 'a1 -> hProptoType -> hProptoType paths **)

let ishinh_irrel x x' =
  proofirrelevance (propproperty ishinh) (hinhpr x) x'

(** val squash_to_hProp :
    hProp -> hProptoType -> ('a1 -> hProptoType) -> hProptoType **)

let squash_to_hProp q h f =
  hinhuniv q f h

(** val hdisj_impl_1 :
    hProp -> hProp -> hProptoType -> (hProptoType -> hProptoType) ->
    hProptoType **)

let hdisj_impl_1 p _ o f =
  squash_to_hProp p o (fun x ->
    match x with
    | Coq_ii1 h -> h
    | Coq_ii2 h -> f h)

(** val hdisj_impl_2 :
    hProp -> hProp -> hProptoType -> (hProptoType -> hProptoType) ->
    hProptoType **)

let hdisj_impl_2 _ q o f =
  squash_to_hProp q o (fun x ->
    match x with
    | Coq_ii1 h -> f h
    | Coq_ii2 h -> h)

(** val weqlogeq : hProp -> hProp -> (hProp paths, hProptoType) weq **)

let weqlogeq p q =
  weqimplimpl (fun _ -> Obj.magic isrefl_logeq) (fun c ->
    hPropUnivalence p q (Obj.magic c).pr1 (Obj.magic c).pr2)
    (isasethProp p q) (propproperty (hequiv p q))

(** val decidable_proof_by_contradiction :
    hProp -> hProptoType decidable -> hProptoType -> hProptoType **)

let decidable_proof_by_contradiction _ dec nnp =
  match dec with
  | Coq_ii1 a -> a
  | Coq_ii2 b -> fromempty (Obj.magic nnp b)

(** val proof_by_contradiction :
    hProp -> hProptoType -> hProptoType -> hProptoType **)

let proof_by_contradiction p lem =
  decidable_proof_by_contradiction p (Obj.magic lem p)

(** val dneg_elim_to_LEM :
    (hProp -> hProptoType -> hProptoType) -> hProptoType **)

let dneg_elim_to_LEM dne =
  Obj.magic (fun p ->
    Obj.magic dne { pr1 = __; pr2 = (isapropdec p.pr2) } (fun n ->
      let q = weqnegtonegishinh.pr1 n in
      let r = fromnegcoprod_prop p hneg (Obj.magic q) in
      (Obj.magic r).pr2 (Obj.magic r).pr1))

(** val negforall_to_existsneg :
    ('a1 -> hProp) -> hProptoType -> hProptoType -> hProptoType **)

let negforall_to_existsneg p lem nf =
  proof_by_contradiction ishinh lem
    (Obj.magic (fun c ->
      Obj.magic nf (fun x ->
        let q = neghexisttoforallneg c x in proof_by_contradiction (p x) lem q)))

(** val negimpl_to_conj :
    hProp -> hProp -> hProptoType -> hProptoType -> hProptoType **)

let negimpl_to_conj p q lem ni =
  let r = negforall_to_existsneg (fun _ -> q) lem ni in
  squash_to_hProp (hconj p hneg) r (fun x ->
    let p0 = x.pr1 in let nq = x.pr2 in Obj.magic { pr1 = p0; pr2 = nq })

(** val hrel_set : hSet -> hSet **)

let hrel_set x =
  make_hSet (isaset_hrel x)

(** val isaprop_assume_it_is : ('a1 -> 'a1 isaprop) -> 'a1 isaprop **)

let isaprop_assume_it_is f =
  invproofirrelevance (fun x y -> proofirrelevance (f y) x y)

(** val isaproptotal2 :
    ('a1, 'a2) isPredicate -> ('a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths) ->
    ('a1, 'a2) total2 isaprop **)

let isaproptotal2 _ _ =
  invproofirrelevance (fun _ _ -> Coq_paths_refl)

(** val squash_rec :
    (hProptoType -> hProp) -> ('a1 -> hProptoType) -> hProptoType ->
    hProptoType **)

let squash_rec p xp x' =
  hinhuniv (p x') xp x'

(** val logeq_if_both_true :
    hProp -> hProp -> hProptoType -> hProptoType -> hProptoType **)

let logeq_if_both_true _ _ p q =
  Obj.magic { pr1 = (fun _ -> q); pr2 = (fun _ -> p) }

(** val logeq_if_both_false :
    hProp -> hProp -> hProptoType -> hProptoType -> hProptoType **)

let logeq_if_both_false _ _ np nq =
  Obj.magic { pr1 = (fun p -> fromempty (Obj.magic np p)); pr2 = (fun q ->
    fromempty (Obj.magic nq q)) }

(** val proofirrelevance_hProp : hProp -> hProptoType isProofIrrelevant **)

let proofirrelevance_hProp x =
  proofirrelevance (propproperty x)

(** val iscontr_hProp : hProp **)

let iscontr_hProp =
  make_hProp isapropiscontr

(** val islogeqassochconj :
    hProp -> hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqassochconj _ _ _ =
  { pr1 = (fun pQR ->
    Obj.magic { pr1 = (Obj.magic pQR).pr1.pr1; pr2 = { pr1 =
      (Obj.magic pQR).pr1.pr2; pr2 = (Obj.magic pQR).pr2 } }); pr2 =
    (fun pQR ->
    Obj.magic { pr1 = { pr1 = (Obj.magic pQR).pr1; pr2 =
      (Obj.magic pQR).pr2.pr1 }; pr2 = (Obj.magic pQR).pr2.pr2 }) }

(** val islogeqcommhconj :
    hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqcommhconj _ _ =
  { pr1 = (fun pQ ->
    Obj.magic { pr1 = (Obj.magic pQ).pr2; pr2 = (Obj.magic pQ).pr1 }); pr2 =
    (fun qP ->
    Obj.magic { pr1 = (Obj.magic qP).pr2; pr2 = (Obj.magic qP).pr1 }) }

(** val islogeqassochdisj :
    hProp -> hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqassochdisj _ _ _ =
  { pr1 =
    (hinhuniv hdisj (fun hPQR ->
      match hPQR with
      | Coq_ii1 a ->
        hinhuniv hdisj (fun hPQ ->
          match hPQ with
          | Coq_ii1 a0 -> hinhpr (Coq_ii1 a0)
          | Coq_ii2 b -> hinhpr (Coq_ii2 (hinhpr (Coq_ii1 b)))) a
      | Coq_ii2 b -> hinhpr (Coq_ii2 (hinhpr (Coq_ii2 b))))); pr2 =
    (hinhuniv hdisj (fun hPQR ->
      match hPQR with
      | Coq_ii1 a -> hinhpr (Coq_ii1 (hinhpr (Coq_ii1 a)))
      | Coq_ii2 b ->
        hinhuniv hdisj (fun hQR ->
          match hQR with
          | Coq_ii1 a -> hinhpr (Coq_ii1 (hinhpr (Coq_ii2 a)))
          | Coq_ii2 b0 -> hinhpr (Coq_ii2 b0)) b)) }

(** val islogeqhconj_absorb_hdisj :
    hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqhconj_absorb_hdisj _ _ =
  { pr1 = (fun hPPQ -> (Obj.magic hPPQ).pr1); pr2 = (fun hP ->
    Obj.magic { pr1 = hP; pr2 = (hinhpr (Coq_ii1 hP)) }) }

(** val islogeqhdisj_absorb_hconj :
    hProp -> hProp -> (hProptoType, hProptoType) logeq **)

let islogeqhdisj_absorb_hconj p _ =
  { pr1 =
    (hinhuniv p (fun hPPQ ->
      match hPPQ with
      | Coq_ii1 a -> a
      | Coq_ii2 b -> b.pr1)); pr2 = (fun hP -> hinhpr (Coq_ii1 hP)) }

(** val islogeqhfalse_hdisj : hProp -> (hProptoType, hProptoType) logeq **)

let islogeqhfalse_hdisj p =
  { pr1 =
    (hinhuniv p (fun hPPQ ->
      match hPPQ with
      | Coq_ii1 _ -> assert false (* absurd case *)
      | Coq_ii2 b -> b)); pr2 = (fun hP -> hinhpr (Coq_ii2 hP)) }

(** val islogeqhhtrue_hconj : hProp -> (hProptoType, hProptoType) logeq **)

let islogeqhhtrue_hconj _ =
  { pr1 = (fun hP -> (Obj.magic hP).pr2); pr2 = (fun hP ->
    Obj.magic { pr1 = Coq_tt; pr2 = hP }) }

(** val isassoc_hconj : hProp -> hProp -> hProp -> hProp paths **)

let isassoc_hconj p q r =
  hPropUnivalence (hconj (hconj p q) r) (hconj p (hconj q r))
    (islogeqassochconj p q r).pr1 (islogeqassochconj p q r).pr2

(** val iscomm_hconj : hProp -> hProp -> hProp paths **)

let iscomm_hconj p q =
  hPropUnivalence (hconj p q) (hconj q p) (islogeqcommhconj p q).pr1
    (islogeqcommhconj q p).pr1

(** val isassoc_hdisj : hProp -> hProp -> hProp -> hProp paths **)

let isassoc_hdisj p q r =
  hPropUnivalence hdisj hdisj (islogeqassochdisj p q r).pr1
    (islogeqassochdisj p q r).pr2

(** val iscomm_hdisj : hProp -> hProp -> hProp paths **)

let iscomm_hdisj p q =
  hPropUnivalence hdisj hdisj (islogeqcommhdisj p q).pr1
    (islogeqcommhdisj q p).pr1

(** val hconj_absorb_hdisj : hProp -> hProp -> hProp paths **)

let hconj_absorb_hdisj p q =
  hPropUnivalence (hconj p hdisj) p (islogeqhconj_absorb_hdisj p q).pr1
    (islogeqhconj_absorb_hdisj p q).pr2

(** val hdisj_absorb_hconj : hProp -> hProp -> hProp paths **)

let hdisj_absorb_hconj p q =
  hPropUnivalence hdisj p (islogeqhdisj_absorb_hconj p q).pr1
    (islogeqhdisj_absorb_hconj p q).pr2

(** val hfalse_hdisj : hProp -> hProp paths **)

let hfalse_hdisj p =
  hPropUnivalence hdisj p (islogeqhfalse_hdisj p).pr1
    (islogeqhfalse_hdisj p).pr2

(** val htrue_hconj : hProp -> hProp paths **)

let htrue_hconj p =
  hPropUnivalence (hconj htrue p) p (islogeqhhtrue_hconj p).pr1
    (islogeqhhtrue_hconj p).pr2

(** val squash_uniqueness : 'a1 -> hProptoType -> hProptoType paths **)

let squash_uniqueness x h =
  let x0 = hinhpr x in (Obj.magic propproperty ishinh x0 h).pr1

(** val coq_Unnamed_thm : 'a2 isaprop -> ('a1 -> 'a2) -> 'a1 -> 'a2 paths **)

let coq_Unnamed_thm _ _ _ =
  Coq_paths_refl

(** val factor_dep_through_squash :
    (hProptoType -> 'a2 isaprop) -> ('a1 -> 'a2) -> hProptoType -> 'a2 **)

let factor_dep_through_squash i f h =
  Obj.magic h (make_hProp (i h)) f

(** val factor_through_squash_hProp :
    hProp -> ('a1 -> hProptoType) -> hProptoType -> hProptoType **)

let factor_through_squash_hProp hQ =
  let i = hQ.pr2 in (fun f h -> Obj.magic h { pr1 = __; pr2 = i } f)

(** val funspace_isaset : 'a2 isaset -> ('a1 -> 'a2) isaset **)

let funspace_isaset is =
  Obj.magic impredfun (S (S O)) is

(** val squash_map_uniqueness :
    'a2 isaset -> (hProptoType -> 'a2) -> (hProptoType -> 'a2) -> ('a1, 'a2)
    homot -> (hProptoType, 'a2) homot **)

let squash_map_uniqueness ip g g' h =
  factor_dep_through_squash (fun y -> ip (g y) (g' y)) h

(** val squash_map_epi :
    'a2 isaset -> (hProptoType -> 'a2) -> (hProptoType -> 'a2) -> ('a1 ->
    'a2) paths -> (hProptoType -> 'a2) paths **)

let squash_map_epi ip g g' _ =
  Obj.magic funextsec g g'
    (squash_map_uniqueness (Obj.magic ip) (Obj.magic g) (Obj.magic g')
      (fun _ -> Coq_paths_refl))

(** val uniqueExists :
    'a1 -> 'a1 -> ('a1, 'a2) total2 iscontr -> 'a2 -> 'a2 -> 'a1 paths **)

let uniqueExists a b hexists ha hb =
  let h =
    proofirrelevancecontr hexists { pr1 = a; pr2 = ha } { pr1 = b; pr2 = hb }
  in
  base_paths { pr1 = a; pr2 = ha } { pr1 = b; pr2 = hb } h

(** val isConnected : hProp **)

let isConnected =
  hconj ishinh (forall_hProp (fun _ -> forall_hProp (fun _ -> ishinh)))

(** val predicateOnConnectedType :
    hProptoType -> ('a1 -> hProp) -> 'a1 -> hProptoType -> 'a1 -> hProptoType **)

let predicateOnConnectedType i p x0 p0 x =
  squash_to_hProp (p x) ((Obj.magic i).pr2 x x0) (fun _ -> p0)

(** val isBaseConnected : coq_PointedType -> hProp **)

let isBaseConnected _ =
  forall_hProp (fun _ -> ishinh)

(** val isConnected_isBaseConnected :
    coq_PointedType -> (hProptoType, hProptoType) logeq **)

let isConnected_isBaseConnected x =
  { pr1 = (fun x0 ->
    let ic = (Obj.magic x0).pr2 in Obj.magic (fun x1 -> ic (basepoint x) x1));
    pr2 = (fun ibc ->
    Obj.magic { pr1 = (hinhpr (basepoint x)); pr2 = (fun x0 y ->
      squash_to_hProp ishinh (Obj.magic ibc x0) (fun p ->
        squash_to_hProp ishinh (Obj.magic ibc y) (fun q ->
          hinhpr
            (pathscomp0 x0 (basepoint x) y (pathsinv0 (basepoint x) x0 p) q)))) }) }

(** val coq_BasePointComponent : coq_PointedType -> coq_PointedType **)

let coq_BasePointComponent x =
  pointedType { pr1 = (basepoint x); pr2 = (hinhpr Coq_paths_refl) }

(** val basePointComponent_inclusion :
    coq_PointedType -> underlyingType -> underlyingType **)

let basePointComponent_inclusion _ x =
  (Obj.magic x).pr1

(** val coq_BasePointComponent_isBaseConnected :
    coq_PointedType -> hProptoType **)

let coq_BasePointComponent_isBaseConnected x =
  Obj.magic (fun x0 ->
    let c' = x0.pr2 in
    hinhfun (fun _ ->
      maponpaths (fun x1 -> { pr1 = (basepoint x); pr2 = x1 })
        (hinhpr Coq_paths_refl) c'
        (let x1 = hinhpr Coq_paths_refl in
         (Obj.magic propproperty ishinh x1 c').pr1)) c')

(** val coq_BasePointComponent_isincl :
    coq_PointedType -> (underlyingType, underlyingType) isincl **)

let coq_BasePointComponent_isincl _ =
  isinclpr1 (fun _ -> propproperty ishinh)

(** val coq_BasePointComponent_isweq :
    coq_PointedType -> hProptoType -> (underlyingType, underlyingType) isweq **)

let coq_BasePointComponent_isweq _ bc =
  Obj.magic isweqpr1 (fun x ->
    iscontraprop1 (propproperty ishinh) (Obj.magic bc x))

(** val coq_BasePointComponent_weq :
    coq_PointedType -> hProptoType -> (underlyingType, underlyingType) weq **)

let coq_BasePointComponent_weq x bc =
  make_weq (basePointComponent_inclusion x)
    (coq_BasePointComponent_isweq x bc)

(** val baseConnectedness : coq_PointedType -> hProptoType -> hProptoType **)

let baseConnectedness x p =
  Obj.magic { pr1 = (hinhpr (basepoint x)); pr2 = (fun x0 y ->
    let a = Obj.magic p x0 in
    let b = Obj.magic p y in
    squash_to_prop a (propproperty ishinh) (fun a0 ->
      squash_to_prop b (propproperty ishinh) (fun b0 ->
        hinhpr
          (pathscomp0 x0 (basepoint x) y (pathsinv0 (basepoint x) x0 a0) b0)))) }

(** val predicateOnBaseConnectedType :
    coq_PointedType -> hProptoType -> (underlyingType -> hProp) ->
    hProptoType -> underlyingType -> hProptoType **)

let predicateOnBaseConnectedType _ b p p0 x =
  squash_to_hProp (p x) (Obj.magic b x) (fun _ -> p0)

(** val predicateOnBasePointComponent :
    coq_PointedType -> (underlyingType -> hProp) -> hProptoType ->
    underlyingType -> hProptoType **)

let predicateOnBasePointComponent x p p0 x0 =
  squash_to_hProp (p x0)
    (Obj.magic coq_BasePointComponent_isBaseConnected x x0) (fun _ -> p0)

open PartA
open PartB
open PartC
open PartD
open Preamble
open Propositions
open Propositions0
open Sets
open UnivalenceAxiom

type __ = Obj.t

(** val hProp_set : hSet **)

let hProp_set =
  make_hSet isasethProp

(** val isconst : hSet -> ('a1 -> pr1hSet) -> hProp **)

let isconst y f =
  forall_hProp (fun x -> forall_hProp (fun x' -> eqset y (f x) (f x')))

(** val squash_to_hSet :
    hSet -> ('a1 -> pr1hSet) -> hProptoType -> hProptoType -> pr1hSet **)

let squash_to_hSet y f =
  Obj.magic squash_to_set (setproperty y) f

(** val isconst_2 : hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProp **)

let isconst_2 z f =
  forall_hProp (fun x ->
    forall_hProp (fun x' ->
      forall_hProp (fun y ->
        forall_hProp (fun y' -> eqset z (f x y) (f x' y')))))

(** val squash_to_hSet_2 :
    hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProptoType -> hProptoType ->
    hProptoType -> pr1hSet **)

let squash_to_hSet_2 z f c =
  squash_to_set (isaset_forall_hSet (fun _ -> z)) (fun x ->
    squash_to_hSet z (f x) (Obj.magic (fun y y' -> Obj.magic c x x y y')))
    (fun x x' ->
    funextfun
      (squash_to_hSet z (f x) (Obj.magic (fun y y' -> Obj.magic c x x y y')))
      (squash_to_hSet z (f x')
        (Obj.magic (fun y y' -> Obj.magic c x' x' y y'))) (fun yn ->
      squash_to_prop yn
        (setproperty z
          (squash_to_hSet z (f x)
            (Obj.magic (fun y y' -> Obj.magic c x x y y')) yn)
          (squash_to_hSet z (f x')
            (Obj.magic (fun y y' -> Obj.magic c x' x' y y')) yn)) (fun y ->
        Obj.magic c x x' y y)))

(** val isconst_2' : hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProp **)

let isconst_2' z f =
  hconj
    (forall_hProp (fun x ->
      forall_hProp (fun x' ->
        forall_hProp (fun y -> eqset z (f x y) (f x' y)))))
    (forall_hProp (fun x ->
      forall_hProp (fun y ->
        forall_hProp (fun y' -> eqset z (f x y) (f x y')))))

(** val squash_to_hSet_2' :
    hSet -> ('a1 -> 'a2 -> pr1hSet) -> hProptoType -> hProptoType ->
    hProptoType -> pr1hSet **)

let squash_to_hSet_2' z f x0 =
  let c = (Obj.magic x0).pr1 in
  let d = (Obj.magic x0).pr2 in
  squash_to_set (isaset_forall_hSet (fun _ -> z)) (fun x ->
    squash_to_hSet z (f x) (Obj.magic (fun y y' -> d x y y'))) (fun x x' ->
    funextfun (squash_to_hSet z (f x) (Obj.magic (fun y y' -> d x y y')))
      (squash_to_hSet z (f x') (Obj.magic (fun y y' -> d x' y y')))
      (fun yn ->
      squash_to_prop yn
        (setproperty z
          (squash_to_hSet z (f x) (Obj.magic (fun y y' -> d x y y')) yn)
          (squash_to_hSet z (f x') (Obj.magic (fun y y' -> d x' y y')) yn))
        (fun y -> c x x' y)))

(** val eqset_to_path :
    hSet -> pr1hSet -> pr1hSet -> hProptoType -> pr1hSet paths **)

let eqset_to_path _ _ _ e =
  Obj.magic e

(** val isapropiscomprelfun :
    hSet -> 'a1 hrel -> ('a1 -> pr1hSet) -> ('a1, pr1hSet) iscomprelfun
    isaprop **)

let isapropiscomprelfun y _ f =
  impred (S O) (fun x ->
    impred (S O) (fun x' -> impred (S O) (fun _ -> y.pr2 (f x) (f x'))))

(** val iscomprelfun_funcomp :
    'a1 hrel -> 'a2 hrel -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2)
    iscomprelrelfun -> ('a2, 'a3) iscomprelfun -> ('a1, 'a3) iscomprelfun **)

let iscomprelfun_funcomp _ _ f _ hf hg x x' r =
  hg (f x) (f x') (hf x x' r)

(** val fun_hrel_comp : ('a1 -> 'a2) -> 'a2 hrel -> 'a1 hrel **)

let fun_hrel_comp f gt x y =
  gt (f x) (f y)

(** val setquotunivprop' :
    'a1 eqrel -> ('a1 setquot -> 'a2 isaprop) -> ('a1 -> 'a2) -> 'a1 setquot
    -> 'a2 **)

let setquotunivprop' r h ps =
  Obj.magic setquotunivprop r (fun x -> make_hProp (h x)) ps

(** val setquotuniv2prop' :
    'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a2 isaprop) -> ('a1 -> 'a1
    -> 'a2) -> 'a1 setquot -> 'a1 setquot -> 'a2 **)

let setquotuniv2prop' r h ps =
  Obj.magic setquotuniv2prop r (fun x1 x2 -> make_hProp (h x1 x2)) ps

(** val setquotuniv3prop' :
    'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> 'a2 isaprop)
    -> ('a1 -> 'a1 -> 'a1 -> 'a2) -> 'a1 setquot -> 'a1 setquot -> 'a1
    setquot -> 'a2 **)

let setquotuniv3prop' r h ps =
  Obj.magic setquotuniv3prop r (fun x1 x2 x3 -> make_hProp (h x1 x2 x3)) ps

(** val setquotuniv4prop' :
    'a1 eqrel -> ('a1 setquot -> 'a1 setquot -> 'a1 setquot -> 'a1 setquot ->
    'a2 isaprop) -> ('a1 -> 'a1 -> 'a1 -> 'a1 -> 'a2) -> 'a1 setquot -> 'a1
    setquot -> 'a1 setquot -> 'a1 setquot -> 'a2 **)

let setquotuniv4prop' r h ps =
  Obj.magic setquotuniv4prop r (fun x1 x2 x3 x4 ->
    make_hProp (h x1 x2 x3 x4)) ps

(** val same_fiber_eqrel :
    hSet -> hSet -> (pr1hSet -> pr1hSet) -> pr1hSet eqrel **)

let same_fiber_eqrel _ y f =
  make_eqrel (fun x y0 -> eqset y (f x) (f y0))
    (iseqrelconstr (fun x y0 -> eqset y (f x) (f y0)) (fun x1 x2 x3 xy yz ->
      Obj.magic pathscomp0 (f x1) (f x2) (f x3) xy yz) (fun _ ->
      Obj.magic Coq_paths_refl) (fun x1 x2 eq ->
      Obj.magic pathsinv0 (f x1) (f x2) eq))

(** val pi0 : hSet **)

let pi0 =
  setquotinset (pr1eqrel pathseqrel)

(** val _UU03c0__UU2080_ : hSet **)

let _UU03c0__UU2080_ =
  pi0

(** val component : 'a1 -> pr1hSet **)

let component x =
  Obj.magic setquotpr pathseqrel x

(** val _UU03c0__UU2080__map : ('a1 -> 'a2) -> pr1hSet -> pr1hSet **)

let _UU03c0__UU2080__map f =
  Obj.magic setquotfun (pr1eqrel pathseqrel) pathseqrel f (fun x x' ->
    hinhfun (maponpaths f x x'))

(** val _UU03c0__UU2080__universal_property :
    hSet -> (pr1hSet -> pr1hSet, 'a1 -> pr1hSet) weq **)

let _UU03c0__UU2080__universal_property y =
  { pr1 = (fun h -> funcomp component h); pr2 = (fun f ->
    iscontraprop1
      (isaproptotal2 (fun h ->
        impred_isaset (fun _ -> setproperty y) (funcomp component h) f)
        (fun h h' e e' ->
        funextsec h h' (fun w ->
          surjectionisepitosets component h h'
            (Obj.magic issurjsetquotpr pathseqrel) (setproperty y) (fun x ->
            maponpaths (fun k -> k x) (funcomp component h)
              (funcomp component h')
              (pathscomp0 (funcomp component h) f (funcomp component h') e
                (pathsinv0 (funcomp component h') f e'))) w))) { pr1 =
      (Obj.magic setquotuniv (fun _ _ -> ishinh) y f (fun x y0 e ->
        squash_to_prop e (setproperty y (f x) (f y0)) (maponpaths f x y0)));
      pr2 = Coq_paths_refl }) }

(** val _UU03c0__UU2080__universal_map :
    hSet -> ('a1 -> pr1hSet) -> pr1hSet -> pr1hSet **)

let _UU03c0__UU2080__universal_map y =
  invmap (_UU03c0__UU2080__universal_property y)

(** val _UU03c0__UU2080__universal_map_eqn :
    hSet -> ('a1 -> pr1hSet) -> 'a1 -> pr1hSet paths **)

let _UU03c0__UU2080__universal_map_eqn _ _ _ =
  Coq_paths_refl

(** val _UU03c0__UU2080__universal_map_uniq :
    hSet -> (pr1hSet -> pr1hSet) -> (pr1hSet -> pr1hSet) -> ('a1 -> pr1hSet
    paths) -> (pr1hSet, pr1hSet) homot **)

let _UU03c0__UU2080__universal_map_uniq y h h' e x =
  surjectionisepitosets component h h' (Obj.magic issurjsetquotpr pathseqrel)
    (setproperty y) e x

(** val isaprop_eqrel_from_hrel :
    'a1 hrel -> 'a1 -> 'a1 -> ('a1 eqrel -> ('a1 -> 'a1 -> hProptoType ->
    hProptoType) -> hProptoType) isaprop **)

let isaprop_eqrel_from_hrel _ a b =
  impred (S O) (fun r -> impred_prop (fun _ -> pr1eqrel r a b))

(** val eqrel_from_hrel : 'a1 hrel -> 'a1 hrel **)

let eqrel_from_hrel r0 a b =
  make_hProp (isaprop_eqrel_from_hrel r0 a b)

(** val iseqrel_eqrel_from_hrel : 'a1 hrel -> 'a1 iseqrel **)

let iseqrel_eqrel_from_hrel _ =
  { pr1 = { pr1 = (fun x y z h1 h2 ->
    Obj.magic (fun r hR ->
      eqreltrans r x y z (Obj.magic h1 r hR) (Obj.magic h2 r hR))); pr2 =
    (fun x -> Obj.magic (fun r _ -> eqrelrefl r x)) }; pr2 = (fun x y h ->
    Obj.magic (fun r h' -> eqrelsymm r x y (Obj.magic h r h'))) }

(** val eqrel_impl : 'a1 hrel -> 'a1 -> 'a1 -> hProptoType -> hProptoType **)

let eqrel_impl _ a b h =
  Obj.magic (fun _ hR -> hR a b h)

(** val minimal_eqrel_from_hrel :
    'a1 hrel -> 'a1 eqrel -> ('a1 -> 'a1 -> hProptoType -> hProptoType) ->
    'a1 -> 'a1 -> hProptoType -> hProptoType **)

let minimal_eqrel_from_hrel _ r h _ _ h' =
  Obj.magic h' r h

(** val eqreleq : 'a1 eqrel -> 'a1 -> 'a1 -> 'a1 paths -> hProptoType **)

let eqreleq r x _ _ =
  eqrelrefl r x

(** val isaprop_isirrefl : 'a1 hrel -> 'a1 isirrefl isaprop **)

let isaprop_isirrefl _ =
  impred_isaprop (fun _ -> isapropneg)

(** val isaprop_issymm : 'a1 hrel -> 'a1 issymm isaprop **)

let isaprop_issymm rel =
  impred_isaprop (fun x ->
    impred_isaprop (fun y -> isapropimpl (rel y x).pr2))

(** val isaprop_iscotrans : 'a1 hrel -> 'a1 iscotrans isaprop **)

let isaprop_iscotrans _ =
  impred_isaprop (fun _ ->
    impred_isaprop (fun _ -> impred_isaprop (fun _ -> isapropimpl hdisj.pr2)))

(** val univalence_hSet :
    hSet -> hSet -> (pr1hSet, pr1hSet) weq -> hSet paths **)

let univalence_hSet x y w =
  invmap (hSet_univalence x y) w

(** val hSet_univalence_map_univalence_hSet :
    hSet -> hSet -> (pr1hSet, pr1hSet) weq -> (__, __) weq paths **)

let hSet_univalence_map_univalence_hSet x y w =
  homotweqinvweq (hSet_univalence x y) w

(** val hSet_univalence_univalence_hSet_map :
    hSet -> hSet -> hSet paths -> hSet paths paths **)

let hSet_univalence_univalence_hSet_map x y p =
  homotinvweqweq (hSet_univalence x y) p

(** val univalence_hSet_idweq : hSet -> hSet paths paths **)

let univalence_hSet_idweq x =
  pathscomp0 (univalence_hSet x x idweq)
    (univalence_hSet x x (hSet_univalence_map x x Coq_paths_refl))
    Coq_paths_refl
    (maponpaths (univalence_hSet x x) idweq
      (hSet_univalence_map x x Coq_paths_refl) Coq_paths_refl)
    (hSet_univalence_univalence_hSet_map x x Coq_paths_refl)

(** val hSet_univalence_map_inv :
    hSet -> hSet -> hSet paths -> (__, __) weq paths **)

let hSet_univalence_map_inv _ _ _ =
  subtypePath isapropisweq idweq (invweq idweq) Coq_paths_refl

(** val univalence_hSet_inv :
    hSet -> hSet -> (pr1hSet, pr1hSet) weq -> hSet paths paths **)

let univalence_hSet_inv x y w =
  pathscomp0 (pathsinv0 x y (univalence_hSet x y w))
    (univalence_hSet y x
      (hSet_univalence_map y x (pathsinv0 x y (univalence_hSet x y w))))
    (univalence_hSet y x (invweq w))
    (pathsinv0
      (univalence_hSet y x
        (hSet_univalence_map y x (pathsinv0 x y (univalence_hSet x y w))))
      (pathsinv0 x y (univalence_hSet x y w))
      (hSet_univalence_univalence_hSet_map y x
        (pathsinv0 x y (univalence_hSet x y w))))
    (maponpaths (univalence_hSet y x)
      (hSet_univalence_map y x (pathsinv0 x y (univalence_hSet x y w)))
      (invweq w)
      (internal_paths_rew_r
        (hSet_univalence_map y x (pathsinv0 x y (univalence_hSet x y w)))
        (invweq (hSet_univalence_map x y (univalence_hSet x y w)))
        (internal_paths_rew_r
          (hSet_univalence_map x y (univalence_hSet x y w)) w Coq_paths_refl
          (hSet_univalence_map_univalence_hSet x y w))
        (hSet_univalence_map_inv x y (univalence_hSet x y w))))

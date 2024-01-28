open PartA
open PartB
open Preamble
open UnivalenceAxiom

(** val isapropneg : 'a1 neg isaprop **)

let isapropneg =
  invproofirrelevance funextempty

(** val isaprop_isProofIrrelevant : 'a1 isProofIrrelevant isaprop **)

let isaprop_isProofIrrelevant =
  invproofirrelevance (fun i j ->
    funextsec i j (fun x ->
      Obj.magic funextsec (Obj.magic i x) (Obj.magic j x) (fun y ->
        let q = Obj.magic j x y in
        let p = Obj.magic i x y in Obj.magic isProofIrrelevant_paths j x y p q)))

(** val isapropdneg : 'a1 dneg isaprop **)

let isapropdneg =
  Obj.magic (fun x -> Obj.magic isapropneg x)

type 'x isaninvprop = ('x, 'x dneg) isweq

(** val invimpl : 'a1 isaninvprop -> 'a1 dneg -> 'a1 **)

let invimpl is =
  invmap (make_weq todneg is)

(** val isapropaninvprop : 'a1 isaninvprop -> 'a1 isaprop **)

let isapropaninvprop x0 =
  isofhlevelweqb (S O) (make_weq todneg x0) isapropdneg

(** val isaninvpropneg : 'a1 neg isaninvprop **)

let isaninvpropneg y =
  let g = negf todneg in isweqimplimpl todneg g isapropneg isapropneg y

(** val isapropdec : 'a1 isaprop -> 'a1 decidable isaprop **)

let isapropdec i =
  isapropcoprod i isapropneg (fun x n -> n x)

type 'x compl = ('x, 'x paths neg) total2

(** val make_compl :
    'a1 -> 'a1 -> 'a1 paths neg -> ('a1, 'a1 paths neg) total2 **)

let make_compl _ x x0 =
  { pr1 = x; pr2 = x0 }

(** val pr1compl : 'a1 -> ('a1, 'a1 paths neg) total2 -> 'a1 **)

let pr1compl _ t =
  t.pr1

(** val isinclpr1compl : 'a1 -> (('a1, 'a1 paths neg) total2, 'a1) isincl **)

let isinclpr1compl _ =
  isinclpr1 (fun _ -> isapropneg)

(** val recompl : 'a1 -> ('a1 compl, coq_unit) coprod -> 'a1 **)

let recompl x = function
| Coq_ii1 x0 -> pr1compl x x0
| Coq_ii2 _ -> x

(** val maponcomplincl :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> 'a1 compl -> 'a2 compl **)

let maponcomplincl f is x x0' =
  let x' = x0'.pr1 in
  let neqx = x0'.pr2 in
  { pr1 = (f x'); pr2 = (negf (invmaponpathsincl f is x x') neqx) }

(** val weqoncompl : ('a1, 'a2) weq -> 'a1 -> ('a1 compl, 'a2 compl) weq **)

let weqoncompl w x =
  weqcomp
    (weqfibtototal (fun x' ->
      weqiff (logeqnegs (weq_to_iff (weqonpaths w x x'))) isapropneg
        isapropneg)) (weqfp w)

(** val weqoncompl_compute :
    ('a1, 'a2) weq -> 'a1 -> 'a1 compl -> 'a2 paths **)

let weqoncompl_compute _ _ _ =
  Coq_paths_refl

(** val homotweqoncomplcomp :
    ('a1, 'a2) weq -> ('a2, 'a3) weq -> 'a1 -> ('a1 compl, 'a3 compl) homot **)

let homotweqoncomplcomp f g x x' =
  let x'0 = x'.pr1 in
  let nexx' = x'.pr2 in
  invmaponpathsincl (pr1compl (pr1weq g (pr1weq f x)))
    (isinclpr1compl (pr1weq g (pr1weq f x)))
    (pr1weq (weqcomp (weqoncompl f x) (weqoncompl g (pr1weq f x))) { pr1 =
      x'0; pr2 = nexx' })
    (pr1weq (weqoncompl (weqcomp f g) x) { pr1 = x'0; pr2 = nexx' })
    Coq_paths_refl

(** val invrecompl :
    'a1 -> 'a1 isisolated -> 'a1 -> ('a1 compl, coq_unit) coprod **)

let invrecompl x is x' =
  match is x' with
  | Coq_ii1 _ -> Coq_ii2 Coq_tt
  | Coq_ii2 phi -> Coq_ii1 (make_compl x x' phi)

(** val isweqrecompl :
    'a1 -> 'a1 isisolated -> (('a1 compl, coq_unit) coprod, 'a1) isweq **)

let isweqrecompl x is =
  let f = recompl x in
  let g = invrecompl x is in
  let efg = fun x' ->
    let c = is x' in
    (match c with
     | Coq_ii1 _ ->
       let c0 = is x in
       (match c0 with
        | Coq_ii1 _ -> Coq_paths_refl
        | Coq_ii2 _ -> assert false (* absurd case *))
     | Coq_ii2 _ ->
       let c0 = is x' in
       (match c0 with
        | Coq_ii1 _ -> assert false (* absurd case *)
        | Coq_ii2 _ -> Coq_paths_refl))
  in
  let egf = fun u ->
    let c = is (f u) in
    (match c with
     | Coq_ii1 a ->
       (match u with
        | Coq_ii1 _ -> assert false (* absurd case *)
        | Coq_ii2 _ ->
          let e1 = maponpaths g x (f (Coq_ii2 Coq_tt)) a in
          let e2 =
            let c0 = is x in
            (match c0 with
             | Coq_ii1 _ -> Coq_paths_refl
             | Coq_ii2 _ -> assert false (* absurd case *))
          in
          pathscomp0 (g (f (Coq_ii2 Coq_tt))) (g x) (Coq_ii2 Coq_tt) e1 e2)
     | Coq_ii2 _ ->
       (match u with
        | Coq_ii1 a ->
          let t = a.pr1 in
          let c0 = is t in
          (match c0 with
           | Coq_ii1 _ -> assert false (* absurd case *)
           | Coq_ii2 _ -> Coq_paths_refl)
        | Coq_ii2 _ ->
          let c0 = is x in
          (match c0 with
           | Coq_ii1 _ -> Coq_paths_refl
           | Coq_ii2 _ -> assert false (* absurd case *))))
  in
  isweq_iso f g egf efg

(** val weqrecompl :
    'a1 -> 'a1 isisolated -> (('a1 compl, coq_unit) coprod, 'a1) weq **)

let weqrecompl x is =
  make_weq (recompl x) (isweqrecompl x is)

(** val homotrecomplnat :
    ('a1, 'a2) weq -> 'a1 -> ('a1 compl, coq_unit) coprod -> 'a2 paths **)

let homotrecomplnat _ _ _ =
  Coq_paths_refl

(** val recomplf :
    'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> 'a1 -> 'a2 **)

let recomplf x y isx f =
  funcomp (funcomp (invmap (weqrecompl x isx)) (coprodf f idfun)) (recompl y)

(** val weqrecomplf :
    'a1 -> 'a2 -> 'a1 isisolated -> 'a2 isisolated -> ('a1 compl, 'a2 compl)
    weq -> ('a1, 'a2) weq **)

let weqrecomplf x y isx isy w =
  weqcomp (weqcomp (invweq (weqrecompl x isx)) (weqcoprodf w idweq))
    (weqrecompl y isy)

(** val homotrecomplfhomot :
    'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> ('a1 compl ->
    'a2 compl) -> ('a1 compl, 'a2 compl) homot -> ('a1, 'a2) homot **)

let homotrecomplfhomot x y isx f f' h a =
  maponpaths (recompl y)
    (coprodf f (fun t -> t) (invmap (weqrecompl x isx) a))
    (coprodf f' (fun t -> t) (invmap (weqrecompl x isx) a))
    (homotcoprodfhomot f f' (fun t -> t) (fun t -> t) h (fun _ ->
      Coq_paths_refl) (invmap (weqrecompl x isx) a))

(** val pathsrecomplfxtoy :
    'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> 'a2 paths **)

let pathsrecomplfxtoy x _ isx _ =
  let c = isx x in
  (match c with
   | Coq_ii1 _ -> Coq_paths_refl
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val homotrecomplfcomp :
    'a1 -> 'a2 -> 'a3 -> 'a1 isisolated -> 'a2 isisolated -> ('a1 compl ->
    'a2 compl) -> ('a2 compl -> 'a3 compl) -> ('a1, 'a3) homot **)

let homotrecomplfcomp x y _ isx isy f g x' =
  let e =
    homotinvweqweq (weqrecompl y isy)
      (coprodf f idfun (invmap (weqrecompl x isx) x'))
  in
  internal_paths_rew_r
    (invmap (weqrecompl y isy)
      (recompl y (coprodf f idfun (invmap (weqrecompl x isx) x'))))
    (coprodf f idfun (invmap (weqrecompl x isx) x'))
    (let e' = homotcoprodfcomp f idfun g idfun (invmap (weqrecompl x isx) x')
     in
     internal_paths_rew_r
       (coprodf g idfun (coprodf f idfun (invmap (weqrecompl x isx) x')))
       (coprodf (funcomp f g) (funcomp idfun idfun)
         (invmap (weqrecompl x isx) x')) Coq_paths_refl e') e

(** val homotrecomplfidfun : 'a1 -> 'a1 isisolated -> ('a1, 'a1) homot **)

let homotrecomplfidfun _ isx x' =
  let c = isx x' in
  (match c with
   | Coq_ii1 a -> a
   | Coq_ii2 _ -> Coq_paths_refl)

(** val ishomotinclrecomplf :
    'a1 -> 'a2 -> 'a1 isisolated -> ('a1 compl -> 'a2 compl) -> 'a1 compl ->
    'a2 compl -> 'a2 paths -> 'a2 compl paths **)

let ishomotinclrecomplf x y isx f x'n y'n e =
  let x' = x'n.pr1 in
  let nexx' = x'n.pr2 in
  let y' = y'n.pr1 in
  let neyy' = y'n.pr2 in
  invmaponpathsincl (pr1compl y) (isinclpr1compl y)
    (f { pr1 = x'; pr2 = nexx' }) { pr1 = y'; pr2 = neyy' }
    (internal_paths_rew_r y' (recomplf x y isx f x')
      (let c = isx x' in
       match c with
       | Coq_ii1 _ -> assert false (* absurd case *)
       | Coq_ii2 b ->
         let ee = proofirrelevance isapropneg nexx' b in
         internal_paths_rew_r nexx' b Coq_paths_refl ee)
      (pathsinv0 (recomplf x y isx f x') y' e))

(** val funtranspos0 :
    'a1 -> 'a1 -> 'a1 isisolated -> 'a1 compl -> 'a1 compl **)

let funtranspos0 t1 t2 is2 x =
  match is2 x.pr1 with
  | Coq_ii1 e ->
    (match is2 t1 with
     | Coq_ii1 e' ->
       fromempty (x.pr2 (pathscomp0 t1 t2 x.pr1 (pathsinv0 t2 t1 e') e))
     | Coq_ii2 ne' -> make_compl t2 t1 ne')
  | Coq_ii2 ne -> make_compl t2 x.pr1 ne

(** val homottranspos0t2t1t1t2 :
    'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1 compl, 'a1 compl)
    homot **)

let homottranspos0t2t1t1t2 t1 t2 is1 is2 x =
  let t = x.pr1 in
  let net1 = x.pr2 in
  let c = is2 t in
  (match c with
   | Coq_ii1 a ->
     let c0 = is2 t1 in
     (match c0 with
      | Coq_ii1 _ -> assert false (* absurd case *)
      | Coq_ii2 _ ->
        let c1 = is1 t1 in
        (match c1 with
         | Coq_ii1 _ ->
           let c2 = is1 t2 in
           (match c2 with
            | Coq_ii1 _ -> assert false (* absurd case *)
            | Coq_ii2 b ->
              invmaponpathsincl (pr1compl t1) (isinclpr1compl t1)
                (make_compl t1 t2 b) { pr1 = t; pr2 = net1 } a)
         | Coq_ii2 _ -> assert false (* absurd case *)))
   | Coq_ii2 _ ->
     let c0 = is1 t in
     (match c0 with
      | Coq_ii1 _ -> assert false (* absurd case *)
      | Coq_ii2 b ->
        invmaponpathsincl (pr1compl t1) (isinclpr1compl t1)
          (make_compl t1 t b) { pr1 = t; pr2 = net1 } Coq_paths_refl))

(** val weqtranspos0 :
    'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1 compl, 'a1 compl)
    weq **)

let weqtranspos0 t1 t2 is1 is2 =
  weq_iso (funtranspos0 t1 t2 is2) (funtranspos0 t2 t1 is1) (fun x ->
    homottranspos0t2t1t1t2 t1 t2 is1 is2 x) (fun x ->
    homottranspos0t2t1t1t2 t2 t1 is2 is1 x)

(** val funtranspos : 'a1 isolated -> 'a1 isolated -> 'a1 -> 'a1 **)

let funtranspos t1 t2 =
  recomplf t1.pr1 t2.pr1 t1.pr2 (funtranspos0 t1.pr1 t2.pr1 t2.pr2)

(** val homottranspost2t1t1t2 :
    'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1, 'a1) homot **)

let homottranspost2t1t1t2 t1 t2 is1 is2 t =
  internal_paths_rew_r
    (funcomp (recomplf t1 t2 is1 (funtranspos0 t1 t2 is2))
      (recomplf t2 t1 is2 (funtranspos0 t2 t1 is1)) t)
    (recomplf t1 t1 is1
      (funcomp (funtranspos0 t1 t2 is2) (funtranspos0 t2 t1 is1)) t)
    (let e =
       homotrecomplfhomot t1 t1 is1
         (funcomp (funtranspos0 t1 t2 is2) (funtranspos0 t2 t1 is1)) idfun
         (homottranspos0t2t1t1t2 t1 t2 is1 is2) t
     in
     let e' = homotrecomplfidfun t1 is1 t in
     pathscomp0
       (recomplf t1 t1 is1
         (funcomp (funtranspos0 t1 t2 is2) (funtranspos0 t2 t1 is1)) t)
       (recomplf t1 t1 is1 idfun t) (idfun t) e e')
    (homotrecomplfcomp t1 t2 t1 is1 is2 (funtranspos0 t1 t2 is2)
      (funtranspos0 t2 t1 is1) t)

(** val weqtranspos :
    'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1, 'a1) weq **)

let weqtranspos t1 t2 is1 is2 =
  let f = funtranspos { pr1 = t1; pr2 = is1 } { pr1 = t2; pr2 = is2 } in
  let g = funtranspos { pr1 = t2; pr2 = is2 } { pr1 = t1; pr2 = is1 } in
  { pr1 = f; pr2 =
  (let egf = fun t -> homottranspost2t1t1t2 t1 t2 is1 is2 t in
   let efg = fun t -> homottranspost2t1t1t2 t2 t1 is2 is1 t in
   isweq_iso f g egf efg) }

(** val pathsfuntransposoft1 :
    'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 paths **)

let pathsfuntransposoft1 t1 t2 is1 is2 =
  internal_paths_rew_r (recomplf t1 t2 is1 (funtranspos0 t1 t2 is2) t1) t2
    Coq_paths_refl (pathsrecomplfxtoy t1 t2 is1 (funtranspos0 t1 t2 is2))

(** val pathsfuntransposoft2 :
    'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 paths **)

let pathsfuntransposoft2 t1 t2 is1 is2 =
  let c = is1 t2 in
  (match c with
   | Coq_ii1 a -> pathsinv0 t1 t2 a
   | Coq_ii2 _ ->
     let c0 = is2 t2 in
     (match c0 with
      | Coq_ii1 _ ->
        let c1 = is2 t1 in
        (match c1 with
         | Coq_ii1 _ -> assert false (* absurd case *)
         | Coq_ii2 _ -> Coq_paths_refl)
      | Coq_ii2 _ -> assert false (* absurd case *)))

(** val pathsfuntransposofnet1t2 :
    'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> 'a1 -> 'a1 paths neg ->
    'a1 paths neg -> 'a1 paths **)

let pathsfuntransposofnet1t2 _ _ is1 is2 t _ _ =
  let c = is1 t in
  (match c with
   | Coq_ii1 _ -> assert false (* absurd case *)
   | Coq_ii2 _ ->
     let c0 = is2 t in
     (match c0 with
      | Coq_ii1 _ -> assert false (* absurd case *)
      | Coq_ii2 _ -> Coq_paths_refl))

(** val homotfuntranspos2 :
    'a1 -> 'a1 -> 'a1 isisolated -> 'a1 isisolated -> ('a1, 'a1) homot **)

let homotfuntranspos2 t1 t2 is1 is2 t =
  let c = is1 t in
  (match c with
   | Coq_ii1 a ->
     internal_paths_rew_r t t1
       (internal_paths_rew_r
         (funtranspos { pr1 = t1; pr2 = is1 } { pr1 = t2; pr2 = is2 } t1) t2
         (internal_paths_rew_r
           (funtranspos { pr1 = t1; pr2 = is1 } { pr1 = t2; pr2 = is2 } t2)
           t1 Coq_paths_refl (pathsfuntransposoft2 t1 t2 is1 is2))
         (pathsfuntransposoft1 t1 t2 is1 is2)) (pathsinv0 t1 t a)
   | Coq_ii2 b ->
     let c0 = is2 t in
     (match c0 with
      | Coq_ii1 a ->
        internal_paths_rew_r t t2
          (internal_paths_rew_r
            (funtranspos { pr1 = t1; pr2 = is1 } { pr1 = t2; pr2 = is2 } t2)
            t1
            (internal_paths_rew_r
              (funtranspos { pr1 = t1; pr2 = is1 } { pr1 = t2; pr2 = is2 } t1)
              t2 Coq_paths_refl (pathsfuntransposoft1 t1 t2 is1 is2))
            (pathsfuntransposoft2 t1 t2 is1 is2)) (pathsinv0 t2 t a)
      | Coq_ii2 b0 ->
        internal_paths_rew_r
          (funtranspos { pr1 = t1; pr2 = is1 } { pr1 = t2; pr2 = is2 } t) t
          (internal_paths_rew_r
            (funtranspos { pr1 = t1; pr2 = is1 } { pr1 = t2; pr2 = is2 } t) t
            Coq_paths_refl (pathsfuntransposofnet1t2 t1 t2 is1 is2 t b b0))
          (pathsfuntransposofnet1t2 t1 t2 is1 is2 t b b0)))

(** val eqbx : 'a1 -> 'a1 isisolated -> 'a1 -> bool **)

let eqbx _ is x' =
  let c = is x' in
  (match c with
   | Coq_ii1 _ -> Coq_true
   | Coq_ii2 _ -> Coq_false)

(** val iscontrhfibereqbx :
    'a1 -> 'a1 isisolated -> ('a1, bool) hfiber iscontr **)

let iscontrhfibereqbx x is =
  let b =
    let c = is x in
    (match c with
     | Coq_ii1 _ -> Coq_paths_refl
     | Coq_ii2 _ -> assert false (* absurd case *))
  in
  let i = make_hfiber (eqbx x is) Coq_true x b in
  { pr1 = i; pr2 =
  (let c = boolchoice (eqbx x is x) in
   fun t ->
   match c with
   | Coq_ii1 _ ->
     let x' = t.pr1 in
     let e = t.pr2 in
     let e' =
       let c0 = is x' in
       (match c0 with
        | Coq_ii1 a -> pathsinv0 x x' a
        | Coq_ii2 _ -> assert false (* absurd case *))
     in
     invmaponpathsincl (fun t0 -> t0.pr1)
       (isinclfromhfiber (eqbx x is) isasetbool Coq_true)
       (make_hfiber (eqbx x is) Coq_true x' e) i e'
   | Coq_ii2 _ -> assert false (* absurd case *)) }

type ('x, 'y) bhfiber = ('x, bool) hfiber

(** val weqhfibertobhfiber :
    ('a1 -> 'a2) -> 'a2 -> 'a2 isisolated -> (('a1, 'a2) hfiber, ('a1, 'a2)
    bhfiber) weq **)

let weqhfibertobhfiber f y is =
  let g = eqbx y is in
  let ye = (iscontrhfibereqbx y is).pr1 in
  { pr1 = (hfibersftogf f g Coq_true ye); pr2 =
  (Obj.magic isofhlevelfffromZ O (hfibersftogf f g Coq_true ye)
    (hfibersgftog f g Coq_true) ye (fibseqhf f g Coq_true ye)
    (isapropifcontr (iscontrhfibereqbx y is))) }

(** val isinclii1 : ('a1, ('a1, 'a2) coprod) isincl **)

let isinclii1 y =
  let f = fun x -> Coq_ii1 x in
  let gf = fun x -> coprodtoboolsum (f x) in
  let gf' = fun x -> { pr1 = Coq_true; pr2 = x } in
  let h = fun _ -> Coq_paths_refl in
  let is1 = isofhlevelfsnfib O Coq_true (isasetbool Coq_true Coq_true) in
  let is2 = isofhlevelfhomot (S O) gf' gf h is1 in
  isofhlevelff (S O) f coprodtoboolsum is2
    (isofhlevelfweq (S (S O)) weqcoprodtoboolsum) y

(** val iscontrhfiberii1x : 'a1 -> ('a1, ('a1, 'a2) coprod) hfiber iscontr **)

let iscontrhfiberii1x x =
  let xe1 = make_hfiber (fun x0 -> Coq_ii1 x0) (Coq_ii1 x) x Coq_paths_refl in
  iscontraprop1 (isinclii1 (Coq_ii1 x)) xe1

(** val neghfiberii1y : 'a2 -> ('a1, ('a1, 'a2) coprod) hfiber neg **)

let neghfiberii1y y xe =
  let x = xe.pr1 in let e = xe.pr2 in negpathsii1ii2 x y e

(** val isinclii2 : ('a2, ('a1, 'a2) coprod) isincl **)

let isinclii2 y =
  let f = fun x -> Coq_ii2 x in
  let gf = fun y0 -> coprodtoboolsum (f y0) in
  let gf' = fun y0 -> { pr1 = Coq_false; pr2 = y0 } in
  let h = fun _ -> Coq_paths_refl in
  let is1 = isofhlevelfsnfib O Coq_false (isasetbool Coq_false Coq_false) in
  let is2 = isofhlevelfhomot (S O) gf' gf h is1 in
  isofhlevelff (S O) f coprodtoboolsum is2
    (isofhlevelfweq (S (S O)) weqcoprodtoboolsum) y

(** val iscontrhfiberii2y : 'a2 -> ('a2, ('a1, 'a2) coprod) hfiber iscontr **)

let iscontrhfiberii2y y =
  let xe1 = make_hfiber (fun x -> Coq_ii2 x) (Coq_ii2 y) y Coq_paths_refl in
  iscontraprop1 (isinclii2 (Coq_ii2 y)) xe1

(** val neghfiberii2x : 'a1 -> ('a2, ('a1, 'a2) coprod) hfiber neg **)

let neghfiberii2x x ye =
  let y = ye.pr1 in let e = ye.pr2 in negpathsii2ii1 x y e

(** val negintersectii1ii2 :
    ('a1, 'a2) coprod -> ('a1, ('a1, 'a2) coprod) hfiber -> ('a2, ('a1, 'a2)
    coprod) hfiber -> empty **)

let negintersectii1ii2 z x0 x1 =
  let t = x0.pr1 in
  let x = x0.pr2 in
  let t0 = x1.pr1 in
  let x2 = x1.pr2 in
  let e =
    pathscomp0 (Coq_ii1 t) z (Coq_ii2 t0) x (pathsinv0 (Coq_ii2 t0) z x2)
  in
  negpathsii1ii2 t t0 e

(** val isolatedtoisolatedii1 :
    'a1 -> 'a1 isisolated -> ('a1, 'a2) coprod isisolated **)

let isolatedtoisolatedii1 x is = function
| Coq_ii1 a ->
  let c = is a in
  (match c with
   | Coq_ii1 a0 -> Coq_ii1 (maponpaths (fun x0 -> Coq_ii1 x0) x a a0)
   | Coq_ii2 b ->
     Coq_ii2 (negf (invmaponpathsincl (fun x0 -> Coq_ii1 x0) isinclii1 x a) b))
| Coq_ii2 b -> Coq_ii2 (negpathsii1ii2 x b)

(** val isolatedtoisolatedii2 :
    'a2 -> 'a2 isisolated -> ('a1, 'a2) coprod isisolated **)

let isolatedtoisolatedii2 y is = function
| Coq_ii1 a -> Coq_ii2 (negpathsii2ii1 a y)
| Coq_ii2 b ->
  let c = is b in
  (match c with
   | Coq_ii1 a -> Coq_ii1 (maponpaths (fun x -> Coq_ii2 x) y b a)
   | Coq_ii2 b0 ->
     Coq_ii2 (negf (invmaponpathsincl (fun x -> Coq_ii2 x) isinclii2 y b) b0))

(** val weqhfibercoprodf1 :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a3 -> (('a1, 'a3) hfiber, (('a1, 'a2)
    coprod, ('a3, 'a4) coprod) hfiber) weq **)

let weqhfibercoprodf1 f g x' =
  let ix = fun x -> Coq_ii1 x in
  let ix' = fun x -> Coq_ii1 x in
  let fpg = coprodf f g in
  let w1 = samehfibers f ix' isinclii1 x' in
  let w2 = { pr1 = (hfibersgftog ix fpg (ix' x')); pr2 = (fun y ->
    let u = invezmaphf ix fpg (ix' x') y in
    let is = isweqinvezmaphf ix fpg (ix' x') y in
    iscontrweqb (make_weq u is)
      (let xy = y.pr1 in
       let e = y.pr2 in
       (match xy with
        | Coq_ii1 a -> iscontrhfiberofincl (fun x -> Coq_ii1 x) isinclii1 a
        | Coq_ii2 b -> fromempty (negpathsii2ii1 x' (g b) e)))) }
  in
  weqcomp w1 w2

(** val weqhfibercoprodf2 :
    ('a1 -> 'a3) -> ('a2 -> 'a4) -> 'a4 -> (('a2, 'a4) hfiber, (('a1, 'a2)
    coprod, ('a3, 'a4) coprod) hfiber) weq **)

let weqhfibercoprodf2 f g y' =
  let iy = fun x -> Coq_ii2 x in
  let iy' = fun x -> Coq_ii2 x in
  let fpg = coprodf f g in
  let w1 = samehfibers g iy' isinclii2 y' in
  let w2 = { pr1 = (hfibersgftog iy fpg (iy' y')); pr2 = (fun y ->
    let u = invezmaphf iy fpg (iy' y') y in
    let is = isweqinvezmaphf iy fpg (iy' y') y in
    iscontrweqb (make_weq u is)
      (let xy = y.pr1 in
       let e = y.pr2 in
       (match xy with
        | Coq_ii1 a -> fromempty (negpathsii1ii2 (f a) y' e)
        | Coq_ii2 b -> iscontrhfiberofincl (fun x -> Coq_ii2 x) isinclii2 b))) }
  in
  weqcomp w1 w2

(** val isofhlevelfcoprodf :
    nat -> ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a3) isofhlevelf -> ('a2,
    'a4) isofhlevelf -> (('a1, 'a2) coprod, ('a3, 'a4) coprod) isofhlevelf **)

let isofhlevelfcoprodf n f g is1 is2 = function
| Coq_ii1 a -> isofhlevelweqf n (weqhfibercoprodf1 f g a) (is1 a)
| Coq_ii2 b -> isofhlevelweqf n (weqhfibercoprodf2 f g b) (is2 b)

(** val isofhlevelsnsummand1 :
    nat -> ('a1, 'a2) coprod isofhlevel -> 'a1 isofhlevel **)

let isofhlevelsnsummand1 n is =
  isofhlevelXfromfY (S n) (fun x -> Coq_ii1 x)
    (isofhlevelfsnincl n (fun x -> Coq_ii1 x) isinclii1) is

(** val isofhlevelsnsummand2 :
    nat -> ('a1, 'a2) coprod isofhlevel -> 'a2 isofhlevel **)

let isofhlevelsnsummand2 n is =
  isofhlevelXfromfY (S n) (fun x -> Coq_ii2 x)
    (isofhlevelfsnincl n (fun x -> Coq_ii2 x) isinclii2) is

(** val isofhlevelssncoprod :
    nat -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2) coprod isofhlevel **)

let isofhlevelssncoprod n isx isy =
  isofhlevelfromfun (S (S n))
    (let f = coprodf (fun _ -> Coq_tt) (fun _ -> Coq_tt) in
     let is1 =
       isofhlevelfcoprodf (S (S n)) (fun _ -> Coq_tt) (fun _ -> Coq_tt)
         (isofhleveltofun (S (S n)) isx) (isofhleveltofun (S (S n)) isy)
     in
     let is2 =
       isofhlevelweqb (S (S n)) boolascoprod (isofhlevelssnset n isasetbool)
     in
     isofhlevelfgf (S (S n)) f (fun _ -> Coq_tt) is1
       (isofhleveltofun (S (S n)) is2))

(** val isasetcoprod :
    'a1 isaset -> 'a2 isaset -> ('a1, 'a2) coprod isaset **)

let isasetcoprod isx isy =
  Obj.magic isofhlevelssncoprod O isx isy

(** val coprodofhfiberstohfiber :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a3 -> (('a1, 'a3) hfiber, ('a2, 'a3)
    hfiber) coprod -> (('a1, 'a2) coprod, 'a3) hfiber **)

let coprodofhfiberstohfiber _ _ _ = function
| Coq_ii1 a ->
  let x = a.pr1 in let fe = a.pr2 in { pr1 = (Coq_ii1 x); pr2 = fe }
| Coq_ii2 b ->
  let y = b.pr1 in let ge = b.pr2 in { pr1 = (Coq_ii2 y); pr2 = ge }

(** val hfibertocoprodofhfibers :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a3 -> (('a1, 'a2) coprod, 'a3) hfiber ->
    (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) coprod **)

let hfibertocoprodofhfibers f g z hsfg =
  let xy = hsfg.pr1 in
  let e = hsfg.pr2 in
  (match xy with
   | Coq_ii1 a -> Coq_ii1 (make_hfiber f z a e)
   | Coq_ii2 b -> Coq_ii2 (make_hfiber g z b e))

(** val weqhfibersofsumofmaps :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> 'a3 -> ((('a1, 'a3) hfiber, ('a2, 'a3)
    hfiber) coprod, (('a1, 'a2) coprod, 'a3) hfiber) weq **)

let weqhfibersofsumofmaps f g z =
  let ff = coprodofhfiberstohfiber f g z in
  let gg = hfibertocoprodofhfibers f g z in
  { pr1 = ff; pr2 =
  (let effgg = fun hsfg ->
     let xy = hsfg.pr1 in
     (match xy with
      | Coq_ii1 _ -> Coq_paths_refl
      | Coq_ii2 _ -> Coq_paths_refl)
   in
   let eggff = fun hfg ->
     match hfg with
     | Coq_ii1 _ -> Coq_paths_refl
     | Coq_ii2 _ -> Coq_paths_refl
   in
   isweq_iso ff gg eggff effgg) }

(** val isofhlevelfssnsumofmaps :
    nat -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2,
    'a3) isofhlevelf -> (('a1, 'a2) coprod, 'a3) isofhlevelf **)

let isofhlevelfssnsumofmaps n f g isf isg z =
  let w = weqhfibersofsumofmaps f g z in
  let is = isofhlevelssncoprod n (isf z) (isg z) in
  isofhlevelweqf (S (S n)) w is

(** val noil1 :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1 -> 'a2 -> 'a3 paths neg) -> 'a3 ->
    ('a1, 'a3) hfiber -> ('a2, 'a3) hfiber -> empty **)

let noil1 f g noi z hfz hgz =
  let x = hfz.pr1 in
  let fe = hfz.pr2 in
  let y = hgz.pr1 in
  let ge = hgz.pr2 in
  noi x y (pathscomp0 (f x) z (g y) fe (pathsinv0 (g y) z ge))

(** val weqhfibernoi1 :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1 -> 'a2 -> 'a3 paths neg) -> 'a3 ->
    ('a1, 'a3) hfiber -> ((('a1, 'a2) coprod, 'a3) hfiber, ('a1, 'a3) hfiber)
    weq **)

let weqhfibernoi1 f g noi z xe =
  let w1 = invweq (weqhfibersofsumofmaps f g z) in
  let a = fun ye -> noil1 f g noi z xe ye in
  let w2 = invweq (weqii1withneg a) in weqcomp w1 w2

(** val weqhfibernoi2 :
    ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1 -> 'a2 -> 'a3 paths neg) -> 'a3 ->
    ('a2, 'a3) hfiber -> ((('a1, 'a2) coprod, 'a3) hfiber, ('a2, 'a3) hfiber)
    weq **)

let weqhfibernoi2 f g noi z ye =
  let w1 = invweq (weqhfibersofsumofmaps f g z) in
  let a = fun xe -> noil1 f g noi z xe ye in
  let w2 = invweq (weqii2withneg a) in weqcomp w1 w2

(** val isofhlevelfsumofmapsnoi :
    nat -> ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2,
    'a3) isofhlevelf -> ('a1 -> 'a2 -> 'a3 paths neg) -> (('a1, 'a2) coprod,
    'a3) isofhlevelf **)

let isofhlevelfsumofmapsnoi n f g isf isg noi z =
  match n with
  | O -> assert false (* absurd case *)
  | S n0 ->
    isofhlevelsn n0 (fun hfgz ->
      let c = pr1weq (invweq (weqhfibersofsumofmaps f g z)) hfgz in
      (match c with
       | Coq_ii1 a ->
         isofhlevelweqb (S n0) (weqhfibernoi1 f g noi z a) (isf z)
       | Coq_ii2 b ->
         isofhlevelweqb (S n0) (weqhfibernoi2 f g noi z b) (isg z)))

(** val tocompltoii1x :
    'a1 -> ('a1 compl, 'a2) coprod -> ('a1, 'a2) coprod compl **)

let tocompltoii1x x = function
| Coq_ii1 a ->
  { pr1 = (Coq_ii1 a.pr1); pr2 =
    (let e = a.pr2 in
     negf (invmaponpathsincl (fun x1 -> Coq_ii1 x1) isinclii1 x a.pr1) e) }
| Coq_ii2 b ->
  { pr1 = (Coq_ii2 b); pr2 =
    (negf (pathsinv0 (Coq_ii1 x) (Coq_ii2 b)) (negpathsii2ii1 x b)) }

(** val fromcompltoii1x :
    'a1 -> ('a1, 'a2) coprod compl -> ('a1 compl, 'a2) coprod **)

let fromcompltoii1x x x0 =
  let t = x0.pr1 in
  let x1 = x0.pr2 in
  (match t with
   | Coq_ii1 a ->
     let ne = negf (maponpaths (fun x2 -> Coq_ii1 x2) x a) x1 in
     Coq_ii1 (make_compl x a ne)
   | Coq_ii2 b -> Coq_ii2 b)

(** val isweqtocompltoii1x :
    'a1 -> (('a1 compl, 'a2) coprod, ('a1, 'a2) coprod compl) isweq **)

let isweqtocompltoii1x x =
  let f = tocompltoii1x x in
  let g = fromcompltoii1x x in
  let egf = fun nexy ->
    match nexy with
    | Coq_ii1 a ->
      let t = a.pr1 in
      let x0 = a.pr2 in
      let e =
        let x1 =
          negf (maponpaths (fun x1 -> Coq_ii1 x1) x t)
            (negf (invmaponpathsincl (fun x1 -> Coq_ii1 x1) isinclii1 x t) x0)
        in
        (Obj.magic isapropneg x1 x0).pr1
      in
      maponpaths (fun ee -> Coq_ii1 (make_compl x t ee))
        (negf (maponpaths (fun x1 -> Coq_ii1 x1) x t)
          (negf (invmaponpathsincl (fun x1 -> Coq_ii1 x1) isinclii1 x t) x0))
        x0 e
    | Coq_ii2 _ -> Coq_paths_refl
  in
  let efg = fun neii1x ->
    let t = neii1x.pr1 in
    let x0 = neii1x.pr2 in
    (match t with
     | Coq_ii1 a ->
       let e =
         let x1 =
           negf (invmaponpathsincl (fun x1 -> Coq_ii1 x1) isinclii1 x a)
             (negf (maponpaths (fun x1 -> Coq_ii1 x1) x a) x0)
         in
         (Obj.magic isapropneg x1 x0).pr1
       in
       maponpaths (fun ee -> make_compl (Coq_ii1 x) (Coq_ii1 a) ee)
         (negf (invmaponpathsincl (fun x1 -> Coq_ii1 x1) isinclii1 x a)
           (negf (maponpaths (fun x1 -> Coq_ii1 x1) x a) x0)) x0 e
     | Coq_ii2 b ->
       let e =
         let x1 =
           negf (pathsinv0 (Coq_ii1 x) (Coq_ii2 b)) (negpathsii2ii1 x b)
         in
         (Obj.magic isapropneg x1 x0).pr1
       in
       maponpaths (fun ee -> make_compl (Coq_ii1 x) (Coq_ii2 b) ee)
         (negf (pathsinv0 (Coq_ii1 x) (Coq_ii2 b)) (negpathsii2ii1 x b)) x0 e)
  in
  isweq_iso f g egf efg

(** val tocompltoii2y :
    'a2 -> ('a1, 'a2 compl) coprod -> ('a1, 'a2) coprod compl **)

let tocompltoii2y y = function
| Coq_ii1 a -> { pr1 = (Coq_ii1 a); pr2 = (negpathsii2ii1 a y) }
| Coq_ii2 b ->
  { pr1 = (Coq_ii2 b.pr1); pr2 =
    (let e = b.pr2 in
     negf (invmaponpathsincl (fun x -> Coq_ii2 x) isinclii2 y b.pr1) e) }

(** val fromcompltoii2y :
    'a2 -> ('a1, 'a2) coprod compl -> ('a1, 'a2 compl) coprod **)

let fromcompltoii2y y x0 =
  let t = x0.pr1 in
  let x = x0.pr2 in
  (match t with
   | Coq_ii1 a -> Coq_ii1 a
   | Coq_ii2 b ->
     let ne = negf (maponpaths (fun x1 -> Coq_ii2 x1) y b) x in
     Coq_ii2 (make_compl y b ne))

(** val isweqtocompltoii2y :
    'a2 -> (('a1, 'a2 compl) coprod, ('a1, 'a2) coprod compl) isweq **)

let isweqtocompltoii2y y =
  let f = tocompltoii2y y in
  let g = fromcompltoii2y y in
  let egf = fun nexy ->
    match nexy with
    | Coq_ii1 _ -> Coq_paths_refl
    | Coq_ii2 b ->
      let t = b.pr1 in
      let x = b.pr2 in
      let e =
        let x0 =
          negf (maponpaths (fun x0 -> Coq_ii2 x0) y t)
            (negf (invmaponpathsincl (fun x0 -> Coq_ii2 x0) isinclii2 y t) x)
        in
        (Obj.magic isapropneg x0 x).pr1
      in
      maponpaths (fun ee -> Coq_ii2 (make_compl y t ee))
        (negf (maponpaths (fun x0 -> Coq_ii2 x0) y t)
          (negf (invmaponpathsincl (fun x0 -> Coq_ii2 x0) isinclii2 y t) x))
        x e
  in
  let efg = fun neii2x ->
    let t = neii2x.pr1 in
    let x = neii2x.pr2 in
    (match t with
     | Coq_ii1 a ->
       let e = let x0 = negpathsii2ii1 a y in (Obj.magic isapropneg x0 x).pr1
       in
       maponpaths (fun ee -> make_compl (Coq_ii2 y) (Coq_ii1 a) ee)
         (negpathsii2ii1 a y) x e
     | Coq_ii2 b ->
       let e =
         let x0 =
           negf (invmaponpathsincl (fun x0 -> Coq_ii2 x0) isinclii2 y b)
             (negf (maponpaths (fun x0 -> Coq_ii2 x0) y b) x)
         in
         (Obj.magic isapropneg x0 x).pr1
       in
       maponpaths (fun ee -> make_compl (Coq_ii2 y) (Coq_ii2 b) ee)
         (negf (invmaponpathsincl (fun x0 -> Coq_ii2 x0) isinclii2 y b)
           (negf (maponpaths (fun x0 -> Coq_ii2 x0) y b) x)) x e)
  in
  isweq_iso f g egf efg

(** val tocompltodisjoint : 'a1 -> ('a1, coq_unit) coprod compl **)

let tocompltodisjoint x =
  make_compl (Coq_ii2 Coq_tt) (Coq_ii1 x) (negpathsii2ii1 x Coq_tt)

(** val fromcompltodisjoint : ('a1, coq_unit) coprod compl -> 'a1 **)

let fromcompltodisjoint x0 =
  let t = x0.pr1 in
  let x = x0.pr2 in
  (match t with
   | Coq_ii1 a -> a
   | Coq_ii2 _ -> fromempty (x Coq_paths_refl))

(** val isweqtocompltodisjoint : ('a1, ('a1, coq_unit) coprod compl) isweq **)

let isweqtocompltodisjoint y =
  let egf = fun _ -> Coq_paths_refl in
  let efg = fun xx ->
    let t = xx.pr1 in
    let x = xx.pr2 in
    (match t with
     | Coq_ii1 _ -> Coq_paths_refl
     | Coq_ii2 _ -> fromempty (x Coq_paths_refl))
  in
  isweq_iso tocompltodisjoint fromcompltodisjoint egf efg y

(** val weqtocompltodisjoint : ('a1, ('a1, coq_unit) coprod compl) weq **)

let weqtocompltodisjoint =
  make_weq tocompltodisjoint isweqtocompltodisjoint

(** val isweqfromcompltodisjoint :
    (('a1, coq_unit) coprod compl, 'a1) isweq **)

let isweqfromcompltodisjoint y =
  isweqinvmap weqtocompltodisjoint y

(** val isdecpropif' :
    'a1 isaprop -> ('a1, 'a1 neg) coprod -> ('a1, 'a1 neg) coprod iscontr **)

let isdecpropif' is a =
  let is1 = isapropdec is in iscontraprop1 is1 a

(** val isdecproppaths : 'a1 isdeceq -> 'a1 -> 'a1 -> 'a1 paths isdecprop **)

let isdecproppaths is x x' =
  isdecpropif (isasetifdeceq is x x') (is x x')

(** val isdeceqif : ('a1 -> 'a1 -> 'a1 paths isdecprop) -> 'a1 isdeceq **)

let isdeceqif is x x' =
  (is x x').pr1

(** val isaninv1 : 'a1 isdecprop -> 'a1 isaninvprop **)

let isaninv1 is1 =
  let is2 = is1.pr1 in
  let adjevinv = fun _ ->
    match is2 with
    | Coq_ii1 a -> a
    | Coq_ii2 _ -> assert false (* absurd case *)
  in
  isweqimplimpl todneg adjevinv (isdecproptoisaprop is1) isapropneg

(** val isdecpropfibseq1 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a1
    isdecprop -> 'a3 isaprop -> 'a2 isdecprop **)

let isdecpropfibseq1 f g z fs isx isz =
  let isc = iscontraprop1 isz z in
  let x0 = isweqfinfibseq f g z fs isc in isdecpropweqf (make_weq f x0) isx

(** val isdecpropfibseq0 :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2
    isdecprop -> 'a3 isdeceq -> 'a1 isdecprop **)

let isdecpropfibseq0 f g z fs isy isz =
  let isg =
    isofhlevelffromXY (S O) g (isdecproptoisaprop isy)
      (Obj.magic isasetifdeceq isz)
  in
  let isp = isofhlevelXfromg (S O) f g z fs isg in
  let c = isy.pr1 in
  (match c with
   | Coq_ii1 a ->
     isdecpropfibseq1 (d1 f g z fs a) f a (fibseq1 f g z fs a)
       (isdecproppaths isz (g a) z) (isdecproptoisaprop isy)
   | Coq_ii2 b -> isdecpropif isp (Coq_ii2 (negf f b)))

(** val isdecpropdirprod :
    'a1 isdecprop -> 'a2 isdecprop -> ('a1, 'a2) dirprod isdecprop **)

let isdecpropdirprod isx isy =
  let isp =
    isofhleveldirprod (S O) (isdecproptoisaprop isx) (isdecproptoisaprop isy)
  in
  let c = isx.pr1 in
  (match c with
   | Coq_ii1 a ->
     let c0 = isy.pr1 in
     (match c0 with
      | Coq_ii1 a0 -> isdecpropif isp (Coq_ii1 (make_dirprod a a0))
      | Coq_ii2 b ->
        let nxy = fun xy -> let y0 = xy.pr2 in b y0 in
        isdecpropif isp (Coq_ii2 nxy))
   | Coq_ii2 b ->
     let nxy = fun xy -> let x0 = xy.pr1 in b x0 in
     isdecpropif isp (Coq_ii2 nxy))

(** val fromneganddecx :
    'a1 isdecprop -> ('a1, 'a2) dirprod neg -> ('a1 neg, 'a2 neg) coprod **)

let fromneganddecx isx nf =
  let c = isx.pr1 in
  (match c with
   | Coq_ii1 a -> let ny = negf (fun y -> make_dirprod a y) nf in Coq_ii2 ny
   | Coq_ii2 b -> Coq_ii1 b)

(** val fromneganddecy :
    'a2 isdecprop -> ('a1, 'a2) dirprod neg -> ('a1 neg, 'a2 neg) coprod **)

let fromneganddecy isy nf =
  let c = isy.pr1 in
  (match c with
   | Coq_ii1 a -> let nx = negf (fun x -> make_dirprod x a) nf in Coq_ii1 nx
   | Coq_ii2 b -> Coq_ii2 b)

(** val isdecproppathsfromisolated :
    'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isdecprop **)

let isdecproppathsfromisolated x is x' =
  isdecpropif (isaproppathsfromisolated x is x') (is x')

(** val isdecproppathstoisolated :
    'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isdecprop **)

let isdecproppathstoisolated x is x' =
  isdecpropweqf (weqpathsinv0 x x') (isdecproppathsfromisolated x is x')

type ('x, 'y) isdecincl = 'y -> ('x, 'y) hfiber isdecprop

(** val isdecincltoisincl :
    ('a1 -> 'a2) -> ('a1, 'a2) isdecincl -> ('a1, 'a2) isincl **)

let isdecincltoisincl _ is y =
  isdecproptoisaprop (is y)

(** val isdecinclfromisweq :
    ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) isdecincl **)

let isdecinclfromisweq _ iswf y =
  isdecpropfromiscontr (iswf y)

(** val isdecpropfromdecincl :
    ('a1 -> 'a2) -> ('a1, 'a2) isdecincl -> 'a2 isdecprop -> 'a1 isdecprop **)

let isdecpropfromdecincl f isf isy =
  let c = isy.pr1 in
  (match c with
   | Coq_ii1 a ->
     let w = weqhfibertocontr f a (iscontraprop1 (isdecproptoisaprop isy) a)
     in
     isdecpropweqf w (isf a)
   | Coq_ii2 b ->
     isdecpropif
       (isapropinclb f (isdecincltoisincl f isf) (isdecproptoisaprop isy))
       (Coq_ii2 (negf f b)))

(** val isdecinclii1 : ('a1, ('a1, 'a2) coprod) isdecincl **)

let isdecinclii1 = function
| Coq_ii1 a ->
  isdecpropif (isinclii1 (Coq_ii1 a)) (Coq_ii1
    (make_hfiber (fun x -> Coq_ii1 x) (Coq_ii1 a) a Coq_paths_refl))
| Coq_ii2 b -> isdecpropif (isinclii1 (Coq_ii2 b)) (Coq_ii2 (neghfiberii1y b))

(** val isdecinclii2 : ('a2, ('a1, 'a2) coprod) isdecincl **)

let isdecinclii2 = function
| Coq_ii1 a -> isdecpropif (isinclii2 (Coq_ii1 a)) (Coq_ii2 (neghfiberii2x a))
| Coq_ii2 b ->
  isdecpropif (isinclii2 (Coq_ii2 b)) (Coq_ii1
    (make_hfiber (fun x -> Coq_ii2 x) (Coq_ii2 b) b Coq_paths_refl))

(** val isdecinclpr1 :
    ('a1 -> 'a2 isdecprop) -> (('a1, 'a2) total2, 'a1) isdecincl **)

let isdecinclpr1 is x =
  let w = ezweqpr1 x in isdecpropweqf w (is x)

(** val isdecinclhomot :
    ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2)
    isdecincl -> ('a1, 'a2) isdecincl **)

let isdecinclhomot f g h is y =
  isdecpropweqf (weqhfibershomot f g h y) (is y)

(** val isdecinclcomp :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isdecincl -> ('a2, 'a3)
    isdecincl -> ('a1, 'a3) isdecincl **)

let isdecinclcomp f g isf isg z =
  let ww = fun y -> samehfibers f g (isdecincltoisincl g isg) y in
  let c = (isg z).pr1 in
  (match c with
   | Coq_ii1 a -> let y = a.pr1 in isdecpropweqf (ww y) (isf y)
   | Coq_ii2 _ ->
     let wz = { pr1 = (hfibersgftog f g z); pr2 = (fun _ -> assert false
       (* absurd case *)) }
     in
     isdecpropweqb wz (isg z))

(** val isdecinclf :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> ('a1, 'a3) isdecincl
    -> ('a1, 'a2) isdecincl **)

let isdecinclf f g isg isgf y =
  let ww = samehfibers f g isg y in isdecpropweqb ww (isgf (g y))

(** val isdecinclg :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a1, 'a3) isdecincl
    -> ('a2, 'a3) isdecincl **)

let isdecinclg f g isf isgf z =
  let w = { pr1 = (hfibersgftog f g z); pr2 = (fun ye ->
    let ww = ezweqhf f g z ye in iscontrweqf ww (isf ye.pr1)) }
  in
  isdecpropweqf w (isgf z)

(** val isisolateddecinclf :
    ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) isdecincl -> 'a1 isisolated -> 'a2
    isisolated **)

let isisolateddecinclf f x isf isx =
  let is' = fun y xe ->
    let w = ezweq2g f y x xe in
    isdecpropweqf w (isdecproppathstoisolated x isx xe.pr1)
  in
  let is'' = fun y -> isdecpropfromdecincl (d1g f y x) (is' y) (isf y) in
  (fun y' -> (is'' y').pr1)

type ('x, 'y) negimage = ('y, ('x, 'y) hfiber neg) total2

(** val make_negimage :
    ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber neg -> ('a2, ('a1, 'a2) hfiber
    neg) total2 **)

let make_negimage _ x x0 =
  { pr1 = x; pr2 = x0 }

(** val isinclfromcoprodwithnegimage :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> (('a1, ('a2, ('a1, 'a2) hfiber neg)
    total2) coprod, 'a2) isincl **)

let isinclfromcoprodwithnegimage f is =
  let noi = fun x nx e -> let y = nx.pr1 in nx.pr2 (make_hfiber f y x e) in
  let is' = isinclpr1 (fun _ -> isapropneg) in
  isofhlevelfsumofmapsnoi (S O) f (fun t -> t.pr1) is is' noi

type ('x, 'y) iscoproj =
  (('x, ('y, ('x, 'y) hfiber neg) total2) coprod, 'y) isweq

(** val weqcoproj :
    ('a1 -> 'a2) -> ('a1, 'a2) iscoproj -> (('a1, ('a1, 'a2) negimage)
    coprod, 'a2) weq **)

let weqcoproj f is =
  make_weq (sumofmaps f (fun t -> t.pr1)) is

(** val iscoprojfromisdecincl :
    ('a1 -> 'a2) -> ('a1, 'a2) isdecincl -> ('a1, 'a2) iscoproj **)

let iscoprojfromisdecincl f is =
  let p = sumofmaps f (fun t -> t.pr1) in
  let is' = isinclfromcoprodwithnegimage f (isdecincltoisincl f is) in
  (fun y ->
  let c = (is y).pr1 in
  (match c with
   | Coq_ii1 a -> let x = a.pr1 in iscontrhfiberofincl p is' (Coq_ii1 x)
   | Coq_ii2 b -> iscontrhfiberofincl p is' (Coq_ii2 (make_negimage f y b))))

(** val isdecinclfromiscoproj :
    ('a1 -> 'a2) -> ('a1, 'a2) iscoproj -> ('a1, 'a2) isdecincl **)

let isdecinclfromiscoproj f is =
  isdecinclcomp (fun x -> Coq_ii1 x) (sumofmaps f (fun t -> t.pr1))
    isdecinclii1 (isdecinclfromisweq (sumofmaps f (fun t -> t.pr1)) is)

open PartA
open PartB
open PartC
open Preamble
open UnivalenceAxiom

(** val totaltoforall :
    ('a1 -> 'a2, 'a1 -> 'a3) total2 -> 'a1 -> ('a2, 'a3) total2 **)

let totaltoforall x0 x =
  { pr1 = (x0.pr1 x); pr2 = (x0.pr2 x) }

(** val foralltototal :
    ('a1 -> ('a2, 'a3) total2) -> ('a1 -> 'a2, 'a1 -> 'a3) total2 **)

let foralltototal x0 =
  { pr1 = (fun x -> (x0 x).pr1); pr2 = (fun x -> (x0 x).pr2) }

(** val isweqforalltototal :
    ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) isweq **)

let isweqforalltototal y =
  isweq_iso foralltototal totaltoforall (Obj.magic (fun _ -> Coq_paths_refl))
    (Obj.magic (fun _ -> Coq_paths_refl)) y

(** val isweqtotaltoforall :
    (('a1 -> 'a2, 'a1 -> 'a3) total2, 'a1 -> ('a2, 'a3) total2) isweq **)

let isweqtotaltoforall y =
  isweq_iso totaltoforall foralltototal (Obj.magic (fun _ -> Coq_paths_refl))
    (Obj.magic (fun _ -> Coq_paths_refl)) y

(** val weqforalltototal :
    ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq **)

let weqforalltototal =
  make_weq foralltototal isweqforalltototal

(** val weqtotaltoforall :
    (('a1 -> 'a2, 'a1 -> 'a3) total2, 'a1 -> ('a2, 'a3) total2) weq **)

let weqtotaltoforall =
  invweq weqforalltototal

(** val weqfuntototaltototal :
    ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq **)

let weqfuntototaltototal =
  weqforalltototal

(** val funtoprodtoprod :
    ('a1 -> ('a2, 'a3) dirprod) -> ('a1 -> 'a2, 'a1 -> 'a3) dirprod **)

let funtoprodtoprod f =
  make_dirprod (fun x -> (f x).pr1) (fun x -> (f x).pr2)

(** val prodtofuntoprod :
    ('a1 -> 'a2, 'a1 -> 'a3) dirprod -> 'a1 -> ('a2, 'a3) dirprod **)

let prodtofuntoprod fg x =
  { pr1 = (fg.pr1 x); pr2 = (fg.pr2 x) }

(** val weqfuntoprodtoprod :
    ('a1 -> ('a2, 'a3) dirprod, ('a1 -> 'a2, 'a1 -> 'a3) dirprod) weq **)

let weqfuntoprodtoprod =
  make_weq funtoprodtoprod
    (isweq_iso funtoprodtoprod prodtofuntoprod (fun a ->
      Obj.magic funextfun (prodtofuntoprod (funtoprodtoprod (Obj.magic a))) a
        (fun _ -> Coq_paths_refl)) (fun _ -> Coq_paths_refl))

(** val maponsec : ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3 **)

let maponsec f s x =
  f x (s x)

(** val maponsec1 : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3 **)

let maponsec1 f sy x =
  sy (f x)

(** val hfibertoforall :
    ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> 'a2, 'a1 -> 'a3) hfiber ->
    'a1 -> ('a2, 'a3) hfiber **)

let hfibertoforall f s =
  let map1 =
    totalfun (fun pointover -> toforallpaths (fun x -> f x (pointover x)) s)
  in
  funcomp map1 totaltoforall

(** val foralltohfiber :
    ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> ('a2, 'a3) hfiber) -> ('a1
    -> 'a2, 'a1 -> 'a3) hfiber **)

let foralltohfiber f s =
  let map1inv =
    totalfun (fun pointover ->
      funextsec (fun x -> Obj.magic f x (pointover x)) (Obj.magic s))
  in
  (fun a -> Obj.magic map1inv (foralltototal a))

(** val isweqhfibertoforall :
    ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> (('a1 -> 'a2, 'a1 -> 'a3) hfiber,
    'a1 -> ('a2, 'a3) hfiber) isweq **)

let isweqhfibertoforall f s =
  twooutof3c
    (totalfun (fun pointover -> toforallpaths (fun x -> f x (pointover x)) s))
    totaltoforall
    (isweqfibtototal (fun pointover ->
      Obj.magic weqtoforallpaths
        (maponsec (Obj.magic f) (Obj.magic pointover)) s)) isweqtotaltoforall

(** val weqhfibertoforall :
    ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> (('a1 -> 'a2, 'a1 -> 'a3) hfiber,
    'a1 -> ('a2, 'a3) hfiber) weq **)

let weqhfibertoforall f s =
  make_weq (hfibertoforall f s) (isweqhfibertoforall f s)

(** val isweqforalltohfiber :
    ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> ('a2, 'a3) hfiber, ('a1 ->
    'a2, 'a1 -> 'a3) hfiber) isweq **)

let isweqforalltohfiber f s =
  twooutof3c foralltototal
    (totalfun (fun pointover ->
      Obj.magic funextsec (fun x -> Obj.magic f x (Obj.magic pointover x)) s))
    isweqforalltototal
    (isweqfibtototal (fun pointover ->
      weqfunextsec (fun x -> f x (pointover x)) s))

(** val weqforalltohfiber :
    ('a1 -> 'a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1 -> ('a2, 'a3) hfiber, ('a1 ->
    'a2, 'a1 -> 'a3) hfiber) weq **)

let weqforalltohfiber f s =
  make_weq (foralltohfiber f s) (isweqforalltohfiber f s)

(** val isweqmaponsec :
    ('a1 -> ('a2, 'a3) weq) -> ('a1 -> 'a2, 'a1 -> 'a3) isweq **)

let isweqmaponsec f y =
  let is1 = let is2 = fun x -> (f x).pr2 (y x) in funcontr (Obj.magic is2) in
  iscontrweqb (Obj.magic weqhfibertoforall (fun x -> pr1weq (f x)) y) is1

(** val weqonsecfibers :
    ('a1 -> ('a2, 'a3) weq) -> ('a1 -> 'a2, 'a1 -> 'a3) weq **)

let weqonsecfibers f =
  make_weq (maponsec (fun x -> pr1weq (f x))) (isweqmaponsec f)

(** val weqffun : ('a2, 'a3) weq -> ('a1 -> 'a2, 'a1 -> 'a3) weq **)

let weqffun w =
  weqonsecfibers (fun _ -> w)

(** val maponsec1l0 :
    ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let maponsec1l0 f h s x =
  transportf (f x) x (h x) (s (f x))

(** val maponsec1l1 : 'a1 -> ('a1 -> 'a2) -> 'a2 paths **)

let maponsec1l1 _ _ =
  Coq_paths_refl

(** val maponsec1l2 :
    ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a1 -> 'a2) -> 'a1 -> 'a2 paths **)

let maponsec1l2 f h s x =
  let map = fun ff -> maponsec1l0 ff.pr1 ff.pr2 s x in
  let is1 = funextcontr (fun t -> t) in
  let e =
    proofirrelevancecontr (Obj.magic is1) { pr1 = f; pr2 = (Obj.magic h) }
      { pr1 = (fun x0 -> x0); pr2 = (fun _ -> Coq_paths_refl) }
  in
  maponpaths (Obj.magic map) { pr1 = f; pr2 = (Obj.magic h) } { pr1 =
    (fun x0 -> x0); pr2 = (fun _ -> Coq_paths_refl) } e

(** val isweqmaponsec1 : ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) isweq **)

let isweqmaponsec1 f =
  let map = maponsec1 (pr1weq f) in
  let invf = invmap f in
  let im1 = fun sx y -> sx (invf y) in
  let im2 = fun sy' y ->
    transportf (pr1weq f (invmap f y)) y (homotweqinvweq f y) (sy' y)
  in
  let invmapp = fun sx -> im2 (im1 sx) in
  let efg0 = fun sx x ->
    let e3x = fun x0 ->
      invmaponpathsweq f (invf (pr1weq f x0)) x0
        (homotweqinvweq f (pr1weq f x0))
    in
    let e3 = e3x x in
    let e4 =
      pathsinv0
        (maponpaths (pr1weq f) (invf (pr1weq f x)) x
          (invmaponpathsweq f (invf (pr1weq f x)) x
            (homotweqinvweq f (pr1weq f x)))) (homotweqinvweq f (pr1weq f x))
        (pathsweq4 f (invf (pr1weq f x)) x (homotweqinvweq f (pr1weq f x)))
    in
    let e5 =
      maponpaths (fun e40 ->
        transportf (pr1weq f (invf (pr1weq f x))) (pr1weq f x) e40
          (sx (invf (pr1weq f x)))) (homotweqinvweq f (pr1weq f x))
        (maponpaths (pr1weq f) (invf (pr1weq f x)) x e3) e4
    in
    let e6 =
      pathsinv0
        (transportf (invf (pr1weq f x)) x e3 (sx (invf (pr1weq f x))))
        (transportf (pr1weq f (invf (pr1weq f x))) (pr1weq f x)
          (maponpaths (pr1weq f) (invf (pr1weq f x)) x e3)
          (sx (invf (pr1weq f x))))
        (functtransportf (pr1weq f) (invf (pr1weq f x)) x e3
          (sx (invf (pr1weq f x))))
    in
    let ff = fun x0 -> invf (pr1weq f x0) in
    let e7 = maponsec1l2 ff e3x sx x in
    pathscomp0
      (transportf (pr1weq f (invmap f (pr1weq f x))) (pr1weq f x)
        (homotweqinvweq f (pr1weq f x)) (sx (invf (pr1weq f x))))
      (transportf (invf (pr1weq f x)) x e3 (sx (invf (pr1weq f x)))) 
      (sx x)
      (pathscomp0
        (transportf (pr1weq f (invmap f (pr1weq f x))) (pr1weq f x)
          (homotweqinvweq f (pr1weq f x)) (sx (invf (pr1weq f x))))
        (transportf (pr1weq f (invf (pr1weq f x))) (pr1weq f x)
          (maponpaths (pr1weq f) (invf (pr1weq f x)) x e3)
          (sx (invf (pr1weq f x))))
        (transportf (invf (pr1weq f x)) x e3 (sx (invf (pr1weq f x)))) e5 e6)
      e7
  in
  let efg = fun sx ->
    funextsec (Obj.magic map (invmapp sx)) (Obj.magic sx) (Obj.magic efg0 sx)
  in
  let egf0 = fun sy y ->
    let ff = fun y0 -> pr1weq f (invf y0) in
    maponsec1l2 ff (homotweqinvweq f) sy y
  in
  let egf = fun sy ->
    funextsec (Obj.magic invmapp (map sy)) (Obj.magic sy) (Obj.magic egf0 sy)
  in
  isweq_iso map invmapp (Obj.magic egf) (Obj.magic efg)

(** val weqonsecbase : ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) weq **)

let weqonsecbase f =
  make_weq (maponsec1 (pr1weq f)) (isweqmaponsec1 f)

(** val weqbfun : ('a1, 'a2) weq -> ('a2 -> 'a3, 'a1 -> 'a3) weq **)

let weqbfun =
  weqonsecbase

(** val iscontrsecoverempty : (empty -> 'a1) iscontr **)

let iscontrsecoverempty =
  { pr1 = fromempty; pr2 = (fun t ->
    Obj.magic funextsec t (fun x -> fromempty (Obj.magic x)) (fun _ ->
      assert false (* absurd case *))) }

(** val iscontrsecoverempty2 : 'a1 neg -> ('a1 -> 'a2) iscontr **)

let iscontrsecoverempty2 is =
  let w = weqtoempty is in
  let w' = weqonsecbase (invweq w) in iscontrweqb w' iscontrsecoverempty

(** val secovercoprodtoprod :
    (('a1, 'a2) coprod -> 'a3) -> ('a1 -> 'a3, 'a2 -> 'a3) dirprod **)

let secovercoprodtoprod a =
  make_dirprod (fun x -> a (Coq_ii1 x)) (fun y -> a (Coq_ii2 y))

(** val prodtosecovercoprod :
    ('a1 -> 'a3, 'a2 -> 'a3) dirprod -> ('a1, 'a2) coprod -> 'a3 **)

let prodtosecovercoprod a = function
| Coq_ii1 a0 -> a.pr1 a0
| Coq_ii2 b -> a.pr2 b

(** val weqsecovercoprodtoprod :
    (('a1, 'a2) coprod -> 'a3, ('a1 -> 'a3, 'a2 -> 'a3) dirprod) weq **)

let weqsecovercoprodtoprod =
  weq_iso secovercoprodtoprod prodtosecovercoprod (fun x ->
    Obj.magic funextsec (prodtosecovercoprod (secovercoprodtoprod x)) x
      (fun _ -> Coq_paths_refl)) (fun a ->
    pathsdirprod (fun x -> prodtosecovercoprod a (Coq_ii1 x)) a.pr1 (fun y ->
      prodtosecovercoprod a (Coq_ii2 y)) a.pr2
      (Obj.magic funextsec (fun x ->
        prodtosecovercoprod (Obj.magic a) (Coq_ii1 x)) (Obj.magic a).pr1
        (homotrefl (fun x -> prodtosecovercoprod (Obj.magic a) (Coq_ii1 x))))
      (Obj.magic funextsec (fun y ->
        prodtosecovercoprod (Obj.magic a) (Coq_ii2 y)) (Obj.magic a).pr2
        (homotrefl (fun y -> prodtosecovercoprod (Obj.magic a) (Coq_ii2 y)))))

(** val iscontrfunfromempty : (empty -> 'a1) iscontr **)

let iscontrfunfromempty =
  { pr1 = fromempty; pr2 = (fun t ->
    Obj.magic funextfun t fromempty (fun _ -> assert false (* absurd case *))) }

(** val iscontrfunfromempty2 : 'a2 neg -> ('a2 -> 'a1) iscontr **)

let iscontrfunfromempty2 is =
  let w = weqtoempty is in
  let w' = weqbfun (invweq w) in iscontrweqb w' iscontrfunfromempty

(** val funfromcoprodtoprod :
    (('a1, 'a2) coprod -> 'a3) -> ('a1 -> 'a3, 'a2 -> 'a3) dirprod **)

let funfromcoprodtoprod f =
  make_dirprod (fun x -> f (Coq_ii1 x)) (fun y -> f (Coq_ii2 y))

(** val prodtofunfromcoprod :
    ('a1 -> 'a3, 'a2 -> 'a3) dirprod -> ('a1, 'a2) coprod -> 'a3 **)

let prodtofunfromcoprod fg =
  sumofmaps fg.pr1 fg.pr2

(** val weqfunfromcoprodtoprod :
    (('a1, 'a2) coprod -> 'a3, ('a1 -> 'a3, 'a2 -> 'a3) dirprod) weq **)

let weqfunfromcoprodtoprod =
  make_weq funfromcoprodtoprod
    (isweq_iso funfromcoprodtoprod prodtofunfromcoprod (fun a ->
      Obj.magic funextfun (prodtofunfromcoprod (funfromcoprodtoprod a)) a
        (fun _ -> Coq_paths_refl)) (fun _ -> Coq_paths_refl))

(** val tosecoverunit : 'a1 -> coq_unit -> 'a1 **)

let tosecoverunit p _ =
  p

(** val weqsecoverunit : (coq_unit -> 'a1, 'a1) weq **)

let weqsecoverunit =
  let f = fun a -> a Coq_tt in
  { pr1 = f; pr2 =
  (let egf = fun a ->
     funextsec (Obj.magic tosecoverunit (Obj.magic f a)) a (fun _ ->
       Coq_paths_refl)
   in
   let efg = fun _ -> Coq_paths_refl in
   isweq_iso f tosecoverunit (Obj.magic egf) efg) }

(** val weqsecovercontr : 'a1 iscontr -> ('a1 -> 'a2, 'a2) weq **)

let weqsecovercontr is =
  let w1 = weqonsecbase (wequnittocontr is) in weqcomp w1 weqsecoverunit

(** val tosecovertotal2 : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3 **)

let tosecovertotal2 a xp =
  let x = xp.pr1 in let p = xp.pr2 in a x p

(** val weqsecovertotal2 :
    (('a1, 'a2) total2 -> 'a3, 'a1 -> 'a2 -> 'a3) weq **)

let weqsecovertotal2 =
  let f = fun a x p -> a { pr1 = x; pr2 = p } in
  { pr1 = f; pr2 =
  (let egf = fun a ->
     funextsec (Obj.magic tosecovertotal2 (Obj.magic f a)) a (fun _ ->
       Coq_paths_refl)
   in
   let efg = fun a ->
     funextsec (Obj.magic f (tosecovertotal2 a)) (Obj.magic a) (fun x ->
       Obj.magic funextsec (f (tosecovertotal2 a) x) (a x) (fun _ ->
         Coq_paths_refl))
   in
   isweq_iso f tosecovertotal2 (Obj.magic egf) (Obj.magic efg)) }

(** val weqfunfromunit : (coq_unit -> 'a1, 'a1) weq **)

let weqfunfromunit =
  weqsecoverunit

(** val weqfunfromcontr : 'a1 iscontr -> ('a1 -> 'a2, 'a2) weq **)

let weqfunfromcontr =
  weqsecovercontr

(** val weqfunfromtotal2 :
    (('a1, 'a2) total2 -> 'a3, 'a1 -> 'a2 -> 'a3) weq **)

let weqfunfromtotal2 =
  weqsecovertotal2

(** val weqfunfromdirprod :
    (('a1, 'a2) dirprod -> 'a3, 'a1 -> 'a2 -> 'a3) weq **)

let weqfunfromdirprod =
  weqsecovertotal2

(** val impred : nat -> ('a1 -> 'a2 isofhlevel) -> ('a1 -> 'a2) isofhlevel **)

let rec impred n x =
  match n with
  | O -> Obj.magic funcontr x
  | S n0 ->
    Obj.magic (fun x0 x' ->
      let is = fun t -> Obj.magic x t (x0 t) (x' t) in
      let is2 = impred n0 is in
      let u = toforallpaths x0 x' in
      let is3 = isweqtoforallpaths (Obj.magic x0) (Obj.magic x') in
      let v = invmap (make_weq (Obj.magic u) is3) in
      let is4 = isweqinvmap (make_weq (Obj.magic u) is3) in
      isofhlevelweqf n0 (make_weq v is4) is2)

(** val impred_iscontr : ('a1 -> 'a2 iscontr) -> ('a1 -> 'a2) iscontr **)

let impred_iscontr x =
  Obj.magic impred O x

(** val impred_isaprop : ('a1 -> 'a2 isaprop) -> ('a1 -> 'a2) isaprop **)

let impred_isaprop x =
  impred (S O) x

(** val impred_isaset : ('a1 -> 'a2 isaset) -> ('a1 -> 'a2) isaset **)

let impred_isaset x =
  Obj.magic impred (S (S O)) x

(** val impredtwice :
    nat -> ('a1 -> 'a2 -> 'a3 isofhlevel) -> ('a1 -> 'a2 -> 'a3) isofhlevel **)

let impredtwice n x =
  let is1 = fun t -> impred n (x t) in impred n is1

(** val impredfun : nat -> 'a2 isofhlevel -> ('a1 -> 'a2) isofhlevel **)

let impredfun n is =
  impred n (fun _ -> is)

(** val impredtech1 :
    nat -> ('a1 -> 'a2 isofhlevel) -> ('a1 -> 'a2) isofhlevel **)

let impredtech1 n x0 =
  match n with
  | O ->
    Obj.magic { pr1 = (fun x -> (Obj.magic x0 x).pr1); pr2 = (fun t ->
      let s1 = fun x ->
        proofirrelevancecontr (Obj.magic x0 x) (t x) (Obj.magic x0 x).pr1
      in
      funextsec (Obj.magic t) (fun x -> (Obj.magic x0 x).pr1) (Obj.magic s1)) }
  | S n0 ->
    Obj.magic (fun x x' ->
      let s1 = impred n0 (fun t -> Obj.magic x0 t (x t) (x' t)) in
      let w = weqfunextsec x x' in isofhlevelweqf n0 w s1)

(** val iscontrfuntounit : ('a1 -> coq_unit) iscontr **)

let iscontrfuntounit =
  { pr1 = (fun _ -> Coq_tt); pr2 = (fun f ->
    Obj.magic funextfun f (fun _ -> Obj.magic Coq_tt) (fun _ ->
      Coq_paths_refl)) }

(** val iscontrfuntocontr : 'a2 iscontr -> ('a1 -> 'a2) iscontr **)

let iscontrfuntocontr is =
  let w = weqcontrtounit is in
  let w' = weqffun w in iscontrweqb w' iscontrfuntounit

(** val isapropimpl : 'a2 isaprop -> ('a1 -> 'a2) isaprop **)

let isapropimpl isy =
  impred (S O) (fun _ -> isy)

(** val isapropneg2 : 'a2 neg -> ('a1 -> 'a2) isaprop **)

let isapropneg2 is =
  impred (S O) (fun _ -> isapropifnegtrue is)

(** val iscontriscontr : 'a1 iscontr -> 'a1 iscontr iscontr **)

let iscontriscontr is =
  let is1 = fun cntr ->
    let is2 = let is2 = isapropifcontr is in (fun x -> Obj.magic is2 x cntr)
    in
    funcontr is2
  in
  let f = fun t -> t.pr1 in
  let x1 = isweqpr1 is1 in iscontrweqb (make_weq f (Obj.magic x1)) is

(** val isapropiscontr : 'a1 iscontr isaprop **)

let isapropiscontr =
  Obj.magic (fun x x' ->
    let is = iscontriscontr x in
    let is2 = isapropifcontr is in Obj.magic is2 x x')

(** val isapropisweq : ('a1 -> 'a2) -> ('a1, 'a2) isweq isaprop **)

let isapropisweq _ =
  impred (S O) (fun _ -> isapropiscontr)

(** val isapropisisolated : 'a1 -> 'a1 isisolated isaprop **)

let isapropisisolated x =
  isofhlevelsn O (fun is ->
    impred (S O) (fun x' -> isapropdec (isaproppathsfromisolated x is x')))

(** val isapropisdeceq : 'a1 isdeceq isaprop **)

let isapropisdeceq =
  isofhlevelsn O (fun _ -> impred (S O) isapropisisolated)

(** val isapropisofhlevel : nat -> 'a1 isofhlevel isaprop **)

let rec isapropisofhlevel = function
| O -> isapropiscontr
| S n0 -> impred (S O) (fun _ -> impred (S O) (fun _ -> isapropisofhlevel n0))

(** val isapropisaprop : 'a1 isaprop isaprop **)

let isapropisaprop =
  Obj.magic (fun x -> Obj.magic isapropisofhlevel (S O) x)

(** val isapropisdecprop : 'a1 isdecprop isaprop **)
let make_dirprod x y =
  { pr1 = x; pr2 = y }

let weqdirprodcomm =
  let f = fun xy -> make_dirprod xy.pr2 xy.pr1 in
  let g = fun yx -> make_dirprod yx.pr2 yx.pr1 in
  let egf = fun _ -> Coq_paths_refl in
  let efg = fun _ -> Coq_paths_refl in
  { pr1 = f; pr2 = (isweq_iso f g egf efg) }

let isapropisdecprop =
  isofhlevelweqf (S O) weqdirprodcomm
    (isofhleveltotal2 (S O) isapropisaprop isapropdec)

(** val isapropisaset : 'a1 isaset isaprop **)

let isapropisaset =
  Obj.magic (fun x -> Obj.magic isapropisofhlevel (S (S O)) x)

(** val isapropisofhlevelf :
    nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf isaprop **)

let isapropisofhlevelf n _ =
  impred (S O) (fun _ -> isapropisofhlevel n)

(** val isapropisincl : ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf isaprop **)

let isapropisincl f =
  isapropisofhlevelf (S O) f

(** val isaprop_isInjective :
    ('a1 -> 'a2) -> ('a1, 'a2) isInjective isaprop **)

let isaprop_isInjective f =
  impred (S O) (fun t ->
    impred (S O) (fun t0 -> isapropisweq (maponpaths f t t0)))

(** val incl_injectivity :
    ('a1 -> 'a2) -> (('a1, 'a2) isincl, ('a1, 'a2) isInjective) weq **)

let incl_injectivity f =
  weqimplimpl (isweqonpathsincl f) (isinclweqonpaths f) (isapropisincl f)
    (isaprop_isInjective f)

(** val isinclpr1weq : (('a1, 'a2) weq, 'a1 -> 'a2) isincl **)

let isinclpr1weq y =
  isinclpr1 isapropisweq y

(** val isinjpr1weq : (('a1, 'a2) weq, 'a1 -> 'a2) isInjective **)

let isinjpr1weq x =
  isweqonpathsincl pr1weq isinclpr1weq x

(** val isinclpr1isolated : ('a1 isolated, 'a1) isincl **)

let isinclpr1isolated y =
  isinclpr1 isapropisisolated y

(** val weqcomp_assoc :
    ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3, 'a4) weq -> ('a1, 'a4) weq paths **)

let weqcomp_assoc f g h =
  subtypePath isapropisweq (weqcomp (weqcomp f g) h)
    (weqcomp f (weqcomp g h)) Coq_paths_refl

(** val eqweqmap_pathscomp0 :
    coq_UU paths -> coq_UU paths -> ('a1, 'a3) weq paths **)

let eqweqmap_pathscomp0 _ _ =
  pair_path_in2 (fun x -> Obj.magic x)
    (twooutof3c (pr1weq (eqweqmap Coq_paths_refl))
      (pr1weq (eqweqmap Coq_paths_refl)) (eqweqmap Coq_paths_refl).pr2
      (eqweqmap Coq_paths_refl).pr2) (Obj.magic idisweq)
    (let f = fun x -> x in
     let x =
       twooutof3c (pr1weq (eqweqmap Coq_paths_refl))
         (pr1weq (eqweqmap Coq_paths_refl)) (eqweqmap Coq_paths_refl).pr2
         (eqweqmap Coq_paths_refl).pr2
     in
     (Obj.magic isapropisweq f x idisweq).pr1)

(** val inv_idweq_is_idweq : ('a1, 'a1) weq paths **)

let inv_idweq_is_idweq =
  pair_path_in2 (fun x -> x) idisweq (isweqinvmap idweq)
    (let f = fun x -> x in
     let x' = isweqinvmap idweq in (Obj.magic isapropisweq f idisweq x').pr1)

(** val eqweqmap_pathsinv0 : coq_UU paths -> ('a2, 'a1) weq paths **)

let eqweqmap_pathsinv0 _ =
  Obj.magic inv_idweq_is_idweq

(** val weqfweq : ('a2, 'a3) weq -> (('a1, 'a2) weq, ('a1, 'a3) weq) weq **)

let weqfweq w =
  let f = fun a -> weqcomp a w in
  let g = fun b -> weqcomp b (invweq w) in
  { pr1 = f; pr2 =
  (let egf = fun a ->
     invmaponpathsincl pr1weq isinclpr1weq (Obj.magic g (Obj.magic f a)) a
       (funextfun (pr1weq (Obj.magic g (Obj.magic f a))) (pr1weq a) (fun x ->
         homotinvweqweq (Obj.magic w) (pr1weq a x)))
   in
   let efg = fun b ->
     invmaponpathsincl pr1weq isinclpr1weq (Obj.magic f (Obj.magic g b)) b
       (funextfun (pr1weq (Obj.magic f (Obj.magic g b))) (pr1weq b) (fun x ->
         homotweqinvweq (Obj.magic w) (pr1weq b x)))
   in
   isweq_iso f g (Obj.magic egf) (Obj.magic efg)) }

(** val weqbweq : ('a1, 'a2) weq -> (('a2, 'a3) weq, ('a1, 'a3) weq) weq **)

let weqbweq w =
  let f = fun a -> weqcomp w a in
  let g = fun b -> weqcomp (invweq w) b in
  { pr1 = f; pr2 =
  (let egf = fun a ->
     invmaponpathsincl pr1weq isinclpr1weq (Obj.magic g (Obj.magic f a)) a
       (funextfun (pr1weq (Obj.magic g (Obj.magic f a))) (pr1weq a) (fun y ->
         maponpaths (pr1weq a)
           (pr1weq (Obj.magic w) (invmap (Obj.magic w) y)) y
           (homotweqinvweq (Obj.magic w) y)))
   in
   let efg = fun b ->
     invmaponpathsincl pr1weq isinclpr1weq (Obj.magic f (Obj.magic g b)) b
       (funextfun (pr1weq (Obj.magic f (Obj.magic g b))) (pr1weq b) (fun x ->
         maponpaths (pr1weq b)
           (invmap (Obj.magic w) (pr1weq (Obj.magic w) x)) x
           (homotinvweqweq (Obj.magic w) x)))
   in
   isweq_iso f g (Obj.magic egf) (Obj.magic efg)) }

(** val weqweq : ('a1, 'a2) weq -> (('a1, 'a1) weq, ('a2, 'a2) weq) weq **)

let weqweq w =
  weqcomp (weqfweq w) (invweq (weqbweq w))

(** val weqinvweq : (('a1, 'a2) weq, ('a2, 'a1) weq) weq **)

let weqinvweq =
  weq_iso invweq invweq (fun x ->
    invmaponpathsincl (Obj.magic pr1weq) isinclpr1weq (invweq (invweq x)) x
      (funextfun (pr1weq (invweq (invweq (Obj.magic x))))
        (pr1weq (Obj.magic x)) (homotrefl (pr1weq (Obj.magic x))))) (fun y ->
    invmaponpathsincl (Obj.magic pr1weq) isinclpr1weq (invweq (invweq y)) y
      (funextfun (pr1weq (invweq (invweq (Obj.magic y))))
        (pr1weq (Obj.magic y)) (homotrefl (pr1weq (Obj.magic y)))))

(** val isofhlevelsnweqtohlevelsn :
    nat -> 'a2 isofhlevel -> ('a1, 'a2) weq isofhlevel **)

let isofhlevelsnweqtohlevelsn n is =
  isofhlevelsninclb n pr1weq isinclpr1weq (impred (S n) (fun _ -> is))

(** val isofhlevelsnweqfromhlevelsn :
    nat -> 'a2 isofhlevel -> ('a2, 'a1) weq isofhlevel **)

let isofhlevelsnweqfromhlevelsn n is =
  isofhlevelweqf (S n) weqinvweq (isofhlevelsnweqtohlevelsn n is)

(** val isapropweqtocontr : 'a2 iscontr -> ('a1, 'a2) weq isaprop **)

let isapropweqtocontr is =
  isofhlevelsnweqtohlevelsn O (isapropifcontr is)

(** val isapropweqfromcontr : 'a2 iscontr -> ('a2, 'a1) weq isaprop **)

let isapropweqfromcontr is =
  isofhlevelsnweqfromhlevelsn O (isapropifcontr is)

(** val isapropweqtoprop : 'a2 isaprop -> ('a1, 'a2) weq isaprop **)

let isapropweqtoprop is =
  isofhlevelsnweqtohlevelsn O is

(** val isapropweqfromprop : 'a2 isaprop -> ('a2, 'a1) weq isaprop **)

let isapropweqfromprop is =
  isofhlevelsnweqfromhlevelsn O is

(** val isasetweqtoset : 'a2 isaset -> ('a1, 'a2) weq isaset **)

let isasetweqtoset is =
  Obj.magic isofhlevelsnweqtohlevelsn (S O) is

(** val isasetweqfromset : 'a2 isaset -> ('a2, 'a1) weq isaset **)

let isasetweqfromset is =
  Obj.magic isofhlevelsnweqfromhlevelsn (S O) is

(** val isapropweqtoempty : ('a1, empty) weq isaprop **)

let isapropweqtoempty =
  Obj.magic (fun x -> Obj.magic isofhlevelsnweqtohlevelsn O isapropempty x)

(** val isapropweqtoempty2 : 'a2 neg -> ('a1, 'a2) weq isaprop **)

let isapropweqtoempty2 is =
  isofhlevelsnweqtohlevelsn O (isapropifnegtrue is)

(** val isapropweqfromempty : (empty, 'a1) weq isaprop **)

let isapropweqfromempty =
  Obj.magic (fun x -> Obj.magic isofhlevelsnweqfromhlevelsn O isapropempty x)

(** val isapropweqfromempty2 : 'a2 neg -> ('a2, 'a1) weq isaprop **)

let isapropweqfromempty2 is =
  isofhlevelsnweqfromhlevelsn O (isapropifnegtrue is)

(** val isapropweqtounit : ('a1, coq_unit) weq isaprop **)

let isapropweqtounit =
  Obj.magic (fun x -> Obj.magic isofhlevelsnweqtohlevelsn O isapropunit x)

(** val isapropweqfromunit : (coq_unit, 'a1) weq isaprop **)

let isapropweqfromunit =
  isofhlevelsnweqfromhlevelsn O isapropunit

(** val cutonweq :
    'a1 -> 'a1 isisolated -> ('a1, 'a1) weq -> ('a1 isolated, ('a1 compl, 'a1
    compl) weq) dirprod **)

let cutonweq t is w =
  { pr1 = { pr1 = (pr1weq w t); pr2 = (isisolatedweqf w t is) }; pr2 =
    (weqcomp (weqoncompl w t)
      (weqtranspos0 (pr1weq w t) t (isisolatedweqf w t is) is)) }

(** val invcutonweq :
    'a1 -> 'a1 isisolated -> ('a1 isolated, ('a1 compl, 'a1 compl) weq)
    dirprod -> ('a1, 'a1) weq **)

let invcutonweq t is t'w =
  weqcomp (weqrecomplf t t is is t'w.pr2)
    (weqtranspos t t'w.pr1.pr1 is t'w.pr1.pr2)

(** val pathsinvcuntonweqoft :
    'a1 -> 'a1 isisolated -> ('a1 isolated, ('a1 compl, 'a1 compl) weq)
    dirprod -> 'a1 paths **)

let pathsinvcuntonweqoft t is t'w =
  let c = is t in
  (match c with
   | Coq_ii1 _ -> pathsfuntransposoft1 t t'w.pr1.pr1 is t'w.pr1.pr2
   | Coq_ii2 _ -> assert false (* absurd case *))

(** val weqcutonweq :
    'a1 -> 'a1 isisolated -> (('a1, 'a1) weq, ('a1 isolated, ('a1 compl, 'a1
    compl) weq) dirprod) weq **)

let weqcutonweq t is =
  let f = cutonweq t is in
  let g = invcutonweq t is in
  weq_iso f g (fun w ->
    invmaponpathsincl (Obj.magic pr1weq) isinclpr1weq (g (f w)) w
      (funextfun (pr1weq (Obj.magic g (f w))) (pr1weq (Obj.magic w))
        (fun t' ->
        let c = Obj.magic is t' in
        (match c with
         | Coq_ii1 a ->
           internal_paths_rew_r t' (Obj.magic t)
             (pathsfuntransposoft1 (Obj.magic t) (pr1weq (Obj.magic w) t)
               (Obj.magic is) (isisolatedweqf (Obj.magic w) t is))
             (pathsinv0 (Obj.magic t) t' a)
         | Coq_ii2 b ->
           let c0 = is (pr1weq w t) in
           (match c0 with
            | Coq_ii1 a ->
              let c1 = is (pr1weq (Obj.magic w) t') in
              (match c1 with
               | Coq_ii1 _ -> assert false (* absurd case *)
               | Coq_ii2 b0 ->
                 let netwt' = internal_paths_rew t b0 (pr1weq w t) a in
                 pathsfuntransposofnet1t2 (Obj.magic t)
                   (pr1weq (Obj.magic w) t) (Obj.magic is)
                   (isisolatedweqf (Obj.magic w) t is)
                   (pr1weq (Obj.magic w) t') (Obj.magic b0) (Obj.magic netwt'))
            | Coq_ii2 _ ->
              let c1 = is (pr1weq (Obj.magic w) t') in
              (match c1 with
               | Coq_ii1 a ->
                 internal_paths_rew_r (pr1weq (Obj.magic w) t') t
                   (pathsfuntransposoft2 (Obj.magic t)
                     (pr1weq (Obj.magic w) t) (Obj.magic is)
                     (isisolatedweqf (Obj.magic w) t is))
                   (pathsinv0 t (pr1weq (Obj.magic w) t') a)
               | Coq_ii2 b0 ->
                 let ne =
                   negf (invmaponpathsweq (Obj.magic w) (Obj.magic t) t') b
                 in
                 pathsfuntransposofnet1t2 (Obj.magic t)
                   (pr1weq (Obj.magic w) t) (Obj.magic is)
                   (isisolatedweqf (Obj.magic w) t is)
                   (pr1weq (Obj.magic w) t') (Obj.magic b0) ne))))))
    (fun xw ->
    let x = xw.pr1 in
    let w = xw.pr2 in
    let t' = x.pr1 in
    let is' = x.pr2 in
    pathsdirprod { pr1 =
      (pr1weq (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t); pr2 =
      (isisolatedweqf (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t is) }
      { pr1 = t'; pr2 = is' }
      (weqcomp (weqoncompl (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t)
        (weqtranspos0
          (pr1weq (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t) t
          (isisolatedweqf (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t is)
          is)) w
      (invmaponpathsincl pr1isolated isinclpr1isolated { pr1 =
        (pr1weq (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t); pr2 =
        (isisolatedweqf (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t is) }
        { pr1 = t'; pr2 = is' }
        (let c = is t in
         match c with
         | Coq_ii1 _ -> pathsfuntransposoft1 t t' is is'
         | Coq_ii2 _ -> assert false (* absurd case *)))
      (invmaponpathsincl (Obj.magic pr1weq) isinclpr1weq
        (weqcomp
          (weqoncompl (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t)
          (weqtranspos0
            (funtranspos { pr1 = t; pr2 = is } { pr1 = t'; pr2 = is' }
              (recompl t
                (coprodf (pr1weq w) (fun x0 -> x0)
                  (invmap (weqrecompl t is) t)))) t
            (isisolatedweqf (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t
              is) is)) w
        (funextfun
          (pr1weq
            (weqcomp
              (Obj.magic weqoncompl
                (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t)
              (Obj.magic weqtranspos0
                (funtranspos { pr1 = t; pr2 = is } { pr1 = t'; pr2 = is' }
                  (recompl t
                    (coprodf (pr1weq w) (fun x0 -> x0)
                      (invmap (weqrecompl t is) t)))) t
                (isisolatedweqf
                  (g { pr1 = { pr1 = t'; pr2 = is' }; pr2 = w }) t is) is)))
          (pr1weq (Obj.magic w)) (fun x0 ->
          let x1 = (Obj.magic x0).pr1 in
          let netx = (Obj.magic x0).pr2 in
          let int =
            funtranspos { pr1 = t; pr2 = is } { pr1 = t'; pr2 = is' }
              (recompl t
                (coprodf (pr1weq w) (fun x2 -> x2)
                  (invmap (weqrecompl t is) t)))
          in
          let eee =
            let c = is t in
            (match c with
             | Coq_ii1 _ -> pathsfuntransposoft1 t t' is is'
             | Coq_ii2 _ -> assert false (* absurd case *))
          in
          let isint = internal_paths_rew_r int t' is' eee in
          Obj.magic ishomotinclrecomplf int t isint (funtranspos0 int t is)
            (weqfp_map
              (weqcomp (weqrecomplf t t is is w) (weqtranspos t t' is is'))
              (totalfun (fun x2 ->
                negf
                  (invmap
                    (weqonpaths
                      (weqcomp (weqrecomplf t t is is w)
                        (weqtranspos t t' is is')) t x2))) { pr1 = x1; pr2 =
                netx })) (pr1weq w { pr1 = x1; pr2 = netx })
            (let ee =
               invmaponpathsincl pr1isolated isinclpr1isolated { pr1 = int;
                 pr2 = isint } { pr1 = t'; pr2 = is' } eee
             in
             internal_paths_rew_r { pr1 = int; pr2 = isint } { pr1 = t';
               pr2 = is' }
               (let e =
                  homottranspost2t1t1t2 t t' is is'
                    (recompl t
                      (coprodf (pr1weq w) (fun x2 -> x2)
                        (invmap (weqrecompl t is) x1)))
                in
                internal_paths_rew_r
                  (funtranspos { pr1 = t'; pr2 = is' } { pr1 = t; pr2 = is }
                    (funtranspos { pr1 = t; pr2 = is } { pr1 = t'; pr2 =
                      is' }
                      (recompl t
                        (coprodf (pr1weq w) (fun x2 -> x2)
                          (invmap (weqrecompl t is) x1)))))
                  (recompl t
                    (coprodf (pr1weq w) (fun x2 -> x2)
                      (invmap (weqrecompl t is) x1)))
                  (let c = is x1 in
                   match c with
                   | Coq_ii1 _ -> assert false (* absurd case *)
                   | Coq_ii2 b ->
                     maponpaths (fun t0 -> t0.pr1)
                       (pr1weq w (make_compl t x1 b))
                       (pr1weq w { pr1 = x1; pr2 = netx })
                       (maponpaths (pr1weq w) (make_compl t x1 b) { pr1 = x1;
                         pr2 = netx }
                         (invmaponpathsincl (pr1compl t) (isinclpr1compl t)
                           (make_compl t x1 b) { pr1 = x1; pr2 = netx }
                           Coq_paths_refl))) e) ee)))))

(** val weqcompidl : ('a1, 'a2) weq -> ('a1, 'a2) weq paths **)

let weqcompidl f =
  invmaponpathsincl (Obj.magic pr1weq) isinclpr1weq (weqcomp idweq f) f
    (funextsec (pr1weq (weqcomp (Obj.magic idweq) (Obj.magic f)))
      (pr1weq (Obj.magic f)) (fun _ -> Coq_paths_refl))

(** val weqcompidr : ('a1, 'a2) weq -> ('a1, 'a2) weq paths **)

let weqcompidr f =
  invmaponpathsincl (Obj.magic pr1weq) isinclpr1weq (weqcomp f idweq) f
    (funextsec (pr1weq (weqcomp (Obj.magic f) idweq)) (pr1weq (Obj.magic f))
      (fun _ -> Coq_paths_refl))

(** val weqcompinvl : ('a1, 'a2) weq -> ('a2, 'a2) weq paths **)

let weqcompinvl f =
  invmaponpathsincl (Obj.magic pr1weq) isinclpr1weq (weqcomp (invweq f) f)
    idweq
    (funextsec (pr1weq (weqcomp (invweq (Obj.magic f)) (Obj.magic f)))
      (pr1weq idweq) (fun y -> homotweqinvweq (Obj.magic f) y))

(** val weqcompinvr : ('a1, 'a2) weq -> ('a1, 'a1) weq paths **)

let weqcompinvr f =
  invmaponpathsincl (Obj.magic pr1weq) isinclpr1weq (weqcomp f (invweq f))
    idweq
    (funextsec (pr1weq (weqcomp (Obj.magic f) (invweq (Obj.magic f))))
      (pr1weq idweq) (fun x -> homotinvweqweq (Obj.magic f) x))

(** val weqcompassoc :
    ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3, 'a4) weq -> ('a1, 'a4) weq paths **)

let weqcompassoc f g h =
  invmaponpathsincl (Obj.magic pr1weq) isinclpr1weq (weqcomp (weqcomp f g) h)
    (weqcomp f (weqcomp g h))
    (funextsec (pr1weq (weqcomp (weqcomp (Obj.magic f) g) (Obj.magic h)))
      (pr1weq (weqcomp (Obj.magic f) (weqcomp g (Obj.magic h)))) (fun _ ->
      Coq_paths_refl))

(** val weqcompweql :
    ('a1, 'a2) weq -> (('a2, 'a3) weq, ('a1, 'a3) weq) isweq **)

let weqcompweql f =
  isweq_iso (fun g -> weqcomp f g) (fun h -> weqcomp (invweq f) h) (fun g ->
    internal_paths_rew (weqcomp (weqcomp (invweq f) f) g)
      (internal_paths_rew_r (weqcomp (invweq f) f) idweq (weqcompidl g)
        (weqcompinvl f)) (weqcomp (invweq f) (weqcomp f g))
      (weqcompassoc (invweq f) f g)) (fun h ->
    internal_paths_rew (weqcomp (weqcomp f (invweq f)) h)
      (internal_paths_rew_r (weqcomp f (invweq f)) idweq (weqcompidl h)
        (weqcompinvr f)) (weqcomp f (weqcomp (invweq f) h))
      (weqcompassoc f (invweq f) h))

(** val weqcompweqr :
    ('a2, 'a3) weq -> (('a1, 'a2) weq, ('a1, 'a3) weq) isweq **)

let weqcompweqr g =
  isweq_iso (fun f -> weqcomp f g) (fun h -> weqcomp h (invweq g)) (fun f ->
    internal_paths_rew_r (weqcomp (weqcomp f g) (invweq g))
      (weqcomp f (weqcomp g (invweq g)))
      (internal_paths_rew_r (weqcomp g (invweq g)) idweq (weqcompidr f)
        (weqcompinvr g)) (weqcompassoc f g (invweq g))) (fun h ->
    internal_paths_rew_r (weqcomp (weqcomp h (invweq g)) g)
      (weqcomp h (weqcomp (invweq g) g))
      (internal_paths_rew_r (weqcomp (invweq g) g) idweq (weqcompidr h)
        (weqcompinvl g)) (weqcompassoc h (invweq g) g))

(** val weqcompinjr :
    ('a1, 'a2) weq -> ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq
    paths -> ('a1, 'a2) weq paths **)

let weqcompinjr f f' g =
  invmaponpathsincl (fun f0 -> weqcomp f0 g)
    (isinclweq (fun f0 -> weqcomp f0 g) (weqcompweqr g)) f f'

(** val weqcompinjl :
    ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq
    paths -> ('a2, 'a3) weq paths **)

let weqcompinjl f g g' =
  invmaponpathsincl (fun g0 -> weqcomp f g0)
    (isinclweq (fun g0 -> weqcomp f g0) (weqcompweql f)) g g'

(** val invweqcomp :
    ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3, 'a1) weq paths **)

let invweqcomp f g =
  weqcompinjr (invweq (weqcomp f g)) (weqcomp (invweq g) (invweq f))
    (weqcomp f g)
    (internal_paths_rew_r (weqcomp (invweq (weqcomp f g)) (weqcomp f g))
      idweq
      (internal_paths_rew_r
        (weqcomp (weqcomp (invweq g) (invweq f)) (weqcomp f g))
        (weqcomp (invweq g) (weqcomp (invweq f) (weqcomp f g)))
        (internal_paths_rew (weqcomp (weqcomp (invweq f) f) g)
          (internal_paths_rew_r (weqcomp (invweq f) f) idweq
            (internal_paths_rew_r (weqcomp idweq g) g
              (internal_paths_rew_r (weqcomp (invweq g) g) idweq
                Coq_paths_refl (weqcompinvl g)) (weqcompidl g))
            (weqcompinvl f)) (weqcomp (invweq f) (weqcomp f g))
          (weqcompassoc (invweq f) f g))
        (weqcompassoc (invweq g) (invweq f) (weqcomp f g)))
      (weqcompinvl (weqcomp f g)))

(** val invmapweqcomp :
    ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3 -> 'a1) paths **)

let invmapweqcomp _ _ =
  Coq_paths_refl

(*
ocaml_unimath/lib/Subtypes.ml
*)

let chain_union_prelim_eq0 x s chain x0 y i j xi xj yi yj =
  let x1 = fun p q -> (weqlogeq p q).pr2 in
  let x2 = fun p q y0 -> (x1 p q y0).pr1 in
  let p =
    coq_WOSrel x (s i) (Obj.magic { pr1 = x0; pr2 = xi })
      (Obj.magic { pr1 = y; pr2 = yi })
  in
  let q =
    coq_WOSrel x (s j) (Obj.magic { pr1 = x0; pr2 = xj })
      (Obj.magic { pr1 = y; pr2 = yj })
  in
  let y0 =
    squash_to_hProp
      (hequiv
        (coq_WOSrel x (s i) (Obj.magic { pr1 = x0; pr2 = xi })
          (Obj.magic { pr1 = y; pr2 = yi }))
        (coq_WOSrel x (s j) (Obj.magic { pr1 = x0; pr2 = xj })
          (Obj.magic { pr1 = y; pr2 = yj }))) (Obj.magic chain i j)
      (fun x3 ->
      match x3 with
      | Coq_ii1 h ->
        Obj.magic { pr1 = (fun l ->
          let q0 =
            Obj.magic wosub_le_comp x (s i) (s j) h { pr1 = x0; pr2 = xi }
              { pr1 = y; pr2 = yi } l
          in
          h1'' x (coq_WOSubset_to_TOSubset x (s j))
            (subtype_inc
              (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s i)))
              (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s j)))
              (Obj.magic h).pr1 { pr1 = x0; pr2 = xi }) { pr1 = x0; pr2 =
            xj }
            (subtype_inc
              (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s i)))
              (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s j)))
              (Obj.magic h).pr1 { pr1 = y; pr2 = yi }) { pr1 = y; pr2 = yj }
            q0 Coq_paths_refl Coq_paths_refl); pr2 = (fun l ->
          (Obj.magic wosub_fidelity x (s i) (s j) h { pr1 = x0; pr2 = xi }
            { pr1 = y; pr2 = yi }).pr2
            (h1'' x (coq_WOSubset_to_TOSubset x (s j)) { pr1 = x0; pr2 = xj }
              (wosub_inc x (s i) (s j) h { pr1 = x0; pr2 = xi }) { pr1 = y;
              pr2 = yj } (wosub_inc x (s i) (s j) h { pr1 = y; pr2 = yi }) l
              Coq_paths_refl Coq_paths_refl)) }
      | Coq_ii2 h ->
        Obj.magic { pr1 = (fun l ->
          (Obj.magic wosub_fidelity x (s j) (s i) h { pr1 = x0; pr2 = xj }
            { pr1 = y; pr2 = yj }).pr2
            (h1'' x (coq_WOSubset_to_TOSubset x (s i)) { pr1 = x0; pr2 = xi }
              (wosub_inc x (s j) (s i) h { pr1 = x0; pr2 = xj }) { pr1 = y;
              pr2 = yi } (wosub_inc x (s j) (s i) h { pr1 = y; pr2 = yj }) l
              Coq_paths_refl Coq_paths_refl)); pr2 = (fun l ->
          let q0 =
            Obj.magic wosub_le_comp x (s j) (s i) h { pr1 = x0; pr2 = xj }
              { pr1 = y; pr2 = yj } l
          in
          h1'' x (coq_WOSubset_to_TOSubset x (s i))
            (subtype_inc
              (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s j)))
              (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s i)))
              (Obj.magic h).pr1 { pr1 = x0; pr2 = xj }) { pr1 = x0; pr2 =
            xi }
            (subtype_inc
              (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s j)))
              (coq_TOSubset_to_subtype x (coq_WOSubset_to_TOSubset x (s i)))
              (Obj.magic h).pr1 { pr1 = y; pr2 = yj }) { pr1 = y; pr2 = yi }
            q0 Coq_paths_refl Coq_paths_refl) })
  in
  (x2 p q y0).pr1

let hsubtype_univalence s t =
  weqcomp (Obj.magic weqtoforallpaths s t)
    (Obj.magic weqonsecfibers (fun x -> weqlogeq (s x) (t x)))

let subtype_containment_isantisymm s t i j =
  invmap (Obj.magic hsubtype_univalence s t)
    (let x0 = fun s0 t0 -> (Obj.magic subtype_equal_cond s0 t0).pr1 in
     Obj.magic x0 s t { pr1 = i; pr2 = j })

let hsubtype_rect s t =
  weqinvweq.pr1 (weqonsecbase (hsubtype_univalence s t))

let weq_vector_1 =
  weqcomp (invweq weqfunfromunit) (weqbfun weqstn1tounit)

let iscontr_rect'' i p0 x =
  invmap (weqsecovercontr i) p0 x
let iscontr_rect_compute'' i p =
  homotweqinvweq (weqsecovercontr i) p
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
let subtype_containment_isPartialOrder =
  make_dirprod subtype_containment_ispreorder subtype_containment_isantisymm

open PartA
open Preamble

type __ = Obj.t

type 'x isofhlevel = __

(** val hlevelretract :
    nat -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1
    isofhlevel -> 'a2 isofhlevel **)

let rec hlevelretract n p s eps x0 =
  match n with
  | O -> Obj.magic iscontrretract p s eps x0
  | S n0 ->
    Obj.magic (fun x x' ->
      let is = Obj.magic x0 (s x) (s x') in
      let s' = maponpaths s x x' in
      let p' = pathssec2 s p eps x x' in
      let eps' = pathssec3 s p eps x x' in
      Obj.magic hlevelretract n0 p' s' eps' is)

(** val isofhlevelweqf :
    nat -> ('a1, 'a2) weq -> 'a1 isofhlevel -> 'a2 isofhlevel **)

let isofhlevelweqf n f x0 =
  hlevelretract n (pr1weq f) (invmap f) (homotweqinvweq f) x0

(** val isofhlevelweqb :
    nat -> ('a1, 'a2) weq -> 'a2 isofhlevel -> 'a1 isofhlevel **)

let isofhlevelweqb n f x0 =
  hlevelretract n (invmap f) (pr1weq f) (homotinvweqweq f) x0

(** val isofhlevelsn : nat -> ('a1 -> 'a1 isofhlevel) -> 'a1 isofhlevel **)

let isofhlevelsn _ f =
  Obj.magic (fun x x' -> Obj.magic f x x x')

type ('x, 'y) isofhlevelf = 'y -> ('x, 'y) hfiber isofhlevel

(** val isofhlevelfhomot :
    nat -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2 paths) -> ('a1, 'a2)
    isofhlevelf -> ('a1, 'a2) isofhlevelf **)

let isofhlevelfhomot n f f' h x0 y =
  isofhlevelweqf n (weqhfibershomot f f' h y) (x0 y)

(** val isofhlevelffromXY :
    nat -> ('a1 -> 'a2) -> 'a1 isofhlevel -> 'a2 isofhlevel -> ('a1, 'a2)
    isofhlevelf **)

let rec isofhlevelffromXY n f x0 x1 =
  match n with
  | O ->
    let is1 = { pr1 = (f (Obj.magic x0).pr1); pr2 = (fun t ->
      let is = Obj.magic x1 t (f (Obj.magic x0).pr1) in is.pr1) }
    in
    Obj.magic isweqcontrcontr f x0 is1
  | S n0 ->
    let is3 = fun y x xe' ->
      Obj.magic isofhlevelffromXY n0 (d2g f y x xe') (Obj.magic x0 xe'.pr1 x)
        (Obj.magic x1 (f x) y)
    in
    let is4 = fun y x xe' e ->
      isofhlevelweqb n0 (ezweq3g f y x xe' e) (is3 y x xe' e)
    in
    (fun y ->
    Obj.magic (fun xe xe' ->
      let t = xe.pr1 in let x = xe.pr2 in is4 y t xe' x))

(** val isofhlevelXfromfY :
    nat -> ('a1 -> 'a2) -> ('a1, 'a2) isofhlevelf -> 'a2 isofhlevel -> 'a1
    isofhlevel **)

let rec isofhlevelXfromfY n f x0 x1 =
  match n with
  | O -> Obj.magic iscontrweqb (make_weq f (Obj.magic x0)) x1
  | S n0 ->
    let is1 = fun y xe xe' -> Obj.magic x0 y xe xe' in
    let is2 = fun y x xe' y0 ->
      isofhlevelweqf n0 (ezweq3g f y x xe' y0)
        (is1 y (make_hfiber f y x y0) xe')
    in
    Obj.magic (fun x' x ->
      let y = f x' in
      let e' = Coq_paths_refl in
      let xe' = make_hfiber f y x' e' in
      Obj.magic isofhlevelXfromfY n0 (d2g f y x xe') (is2 y x xe')
        (Obj.magic x1 (f x) y))

(** val isofhlevelfhfiberpr1y :
    nat -> ('a1 -> 'a2) -> 'a2 -> ('a2 -> 'a2 paths isofhlevel) -> (('a1,
    'a2) hfiber, 'a1) isofhlevelf **)

let isofhlevelfhfiberpr1y n f y is x =
  isofhlevelweqf n (ezweq1g f y x) (is (f x))

(** val isofhlevelfsnfib :
    nat -> 'a1 -> 'a1 paths isofhlevel -> ('a2, ('a1, 'a2) total2) isofhlevelf **)

let isofhlevelfsnfib n x is xp =
  isofhlevelweqf (S n) (ezweq1pr1 x xp) (isofhlevelsn n (fun _ -> is))

(** val isofhlevelfhfiberpr1 :
    nat -> ('a1 -> 'a2) -> 'a2 -> 'a2 isofhlevel -> (('a1, 'a2) hfiber, 'a1)
    isofhlevelf **)

let isofhlevelfhfiberpr1 n f y is =
  isofhlevelfhfiberpr1y n f y (fun y' -> Obj.magic is y' y)

(** val isofhlevelff :
    nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) isofhlevelf -> ('a2,
    'a3) isofhlevelf -> ('a1, 'a2) isofhlevelf **)

let isofhlevelff n f g x0 x1 y =
  let ye = make_hfiber g (g y) y Coq_paths_refl in
  isofhlevelweqb n (ezweqhf f g (g y) ye)
    (isofhlevelffromXY n (hfibersgftog f g (g y)) (x0 (g y)) (x1 (g y)) ye)

(** val isofhlevelfgf :
    nat -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isofhlevelf -> ('a2,
    'a3) isofhlevelf -> ('a1, 'a3) isofhlevelf **)

let isofhlevelfgf n f g x0 x1 z =
  let is1 = fun ye -> isofhlevelweqf n (ezweqhf f g z ye) (x0 ye.pr1) in
  let is2 = x1 z in isofhlevelXfromfY n (hfibersgftog f g z) is1 is2

type 'x isaprop = 'x isofhlevel

(** val isapropifcontr : 'a1 iscontr -> 'a1 isaprop **)

let isapropifcontr is =
  let f = fun _ -> Coq_tt in
  let isw = isweqcontrtounit is in
  isofhlevelweqb (S O) (make_weq f isw) (Obj.magic iscontrpathsinunit)

(** val hlevelntosn : nat -> 'a1 isofhlevel -> 'a1 isofhlevel **)

let rec hlevelntosn = function
| O -> Obj.magic isapropifcontr
| S n0 ->
  (fun x ->
    Obj.magic (fun t1 t2 -> let xX = Obj.magic x t1 t2 in hlevelntosn n0 xX))

(** val isofhlevelcontr : nat -> 'a1 iscontr -> 'a1 isofhlevel **)

let rec isofhlevelcontr n x0 =
  match n with
  | O -> Obj.magic x0
  | S n0 ->
    Obj.magic (fun x x' ->
      let is = Obj.magic isapropifcontr x0 x x' in isofhlevelcontr n0 is)

(** val isofhlevelfweq : nat -> ('a1, 'a2) weq -> ('a1, 'a2) isofhlevelf **)

let isofhlevelfweq n f y =
  isofhlevelcontr n (f.pr2 y)

(** val weqhfibertocontr :
    ('a1 -> 'a2) -> 'a2 -> 'a2 iscontr -> (('a1, 'a2) hfiber, 'a1) weq **)

let weqhfibertocontr f y is =
  { pr1 = (hfiberpr1 f y); pr2 =
    (Obj.magic isofhlevelfhfiberpr1 O f y (hlevelntosn O (Obj.magic is))) }

(** val weqhfibertounit : (('a1, coq_unit) hfiber, 'a1) weq **)

let weqhfibertounit =
  weqhfibertocontr (fun _ -> Coq_tt) Coq_tt iscontrunit

(** val isofhleveltofun :
    nat -> 'a1 isofhlevel -> ('a1, coq_unit) isofhlevelf **)

let isofhleveltofun n is _ =
  isofhlevelweqb n weqhfibertounit is

(** val isofhlevelfromfun :
    nat -> ('a1, coq_unit) isofhlevelf -> 'a1 isofhlevel **)

let isofhlevelfromfun n is =
  isofhlevelweqf n weqhfibertounit (is Coq_tt)

(** val isofhlevelsnprop : nat -> 'a1 isaprop -> 'a1 isofhlevel **)

let isofhlevelsnprop n is =
  Obj.magic (fun x x' -> isofhlevelcontr n (Obj.magic is x x'))

(** val iscontraprop1 : 'a1 isaprop -> 'a1 -> 'a1 iscontr **)

let iscontraprop1 is x =
  { pr1 = x; pr2 = (fun t -> let is' = Obj.magic is t x in is'.pr1) }

(** val iscontraprop1inv : ('a1 -> 'a1 iscontr) -> 'a1 isaprop **)

let iscontraprop1inv f =
  isofhlevelsn O (fun x -> hlevelntosn O (Obj.magic f x))

type ('x, 'y) isincl = ('x, 'y) isofhlevelf

(** val iscontrhfiberofincl :
    ('a1 -> 'a2) -> ('a1, 'a2) isincl -> 'a1 -> ('a1, 'a2) hfiber iscontr **)

let iscontrhfiberofincl f x0 x =
  let isy = x0 (f x) in
  iscontraprop1 isy (make_hfiber f (f x) x Coq_paths_refl)

(** val samehfibers :
    ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isincl -> 'a2 -> (('a1, 'a2)
    hfiber, ('a1, 'a3) hfiber) weq **)

let samehfibers f g is1 y =
  { pr1 = (hfibersftogf f g (g y) (make_hfiber g (g y) y Coq_paths_refl));
    pr2 =
    (let z = g y in
     let ye = make_hfiber g (g y) y Coq_paths_refl in
     (fun xe ->
     iscontrweqf { pr1 =
       (ezmap
         (d1 (hfibersftogf f g z ye) (hfibersgftog f g z) ye
           (fibseqhf f g z ye) xe) (hfibersftogf f g z ye) xe
         (fibseqstrtocomplxstr
           (d1 (hfibersftogf f g z ye) (hfibersgftog f g z) ye
             (fibseqhf f g z ye) xe) (hfibersftogf f g z ye) xe
           (fibseq1 (hfibersftogf f g z ye) (hfibersgftog f g z) ye
             (fibseqhf f g z ye) xe))); pr2 =
       (isweqezmap1 (hfibersftogf f g z (make_hfiber g z y Coq_paths_refl))
         (hfibersgftog f g z) ye (fibseqhf f g z ye) xe) }
       (Obj.magic isapropifcontr (iscontrhfiberofincl g is1 y)
         (hfibersgftog f g z xe) ye))) }

type 'x isaset = 'x -> 'x -> 'x paths isaprop

(** val isasetunit : coq_unit isaset **)

let isasetunit =
  Obj.magic isofhlevelcontr (S (S O)) iscontrunit

(** val isofhlevelssnset : nat -> 'a1 isaset -> 'a1 isofhlevel **)

let isofhlevelssnset n is =
  Obj.magic (fun x x' -> isofhlevelsnprop n (is x x'))

type 'x decidable = ('x, 'x neg) coprod

type 'x isdeceq = 'x -> 'x -> 'x paths decidable

(** val isdeceqbool : bool isdeceq **)

let isdeceqbool x' = function
| Coq_true ->
  (match x' with
   | Coq_true -> Coq_ii1 Coq_paths_refl
   | Coq_false -> Coq_ii2 nopathsfalsetotrue)
| Coq_false ->
  (match x' with
   | Coq_true -> Coq_ii2 nopathstruetofalse
   | Coq_false -> Coq_ii1 Coq_paths_refl)

type 'x isisolated = 'x -> ('x paths, 'x paths neg) coprod

(** val isaproppathsfromisolated :
    'a1 -> 'a1 isisolated -> 'a1 -> 'a1 paths isaprop **)

let isaproppathsfromisolated x is _ =
  iscontraprop1inv (fun _ ->
    let f = fun e -> coconusfromtpair x x e in
    let is' = onefiber x is in
    let is2 = iscontrcoconusfromt x in iscontrweqb (make_weq f is') is2)

(** val isasetifdeceq : 'a1 isdeceq -> 'a1 isaset **)

let isasetifdeceq is x x' =
  isaproppathsfromisolated x (is x) x'

(** val isasetbool : bool isaset **)

let isasetbool =
  isasetifdeceq isdeceqbool

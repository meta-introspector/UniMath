open Preamble

type __ = Obj.t

val fromempty : empty -> 'a1

val idfun : 'a1 -> 'a1

val funcomp : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3

type 'x neg = 'x -> empty

val pathscomp0 : 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths

val pathscomp0rid : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathsinv0 : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths

val pathsinv0l : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val maponpaths : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths

val maponpathscomp :
  'a1 -> 'a1 -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 paths -> 'a3 paths paths

type ('x, 'p) homot = 'x -> 'p paths

val pathssec1 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a2 -> 'a2
  paths -> 'a1 paths

val pathssec2 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a2
  paths -> 'a1 paths

val pathssec2id :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 paths paths

val pathssec3 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1
  paths -> 'a1 paths paths

val constr1 :
  'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a2, ('a2 -> ('a1, 'a2) total2 paths,
  'a2 -> 'a1 paths paths) total2) total2

val transportf : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2

val transportb : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2

val two_arg_paths_f :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
  -> 'a3 paths

type 't iscontr = ('t, 't -> 't paths) total2

val iscontrpr1 : 'a1 iscontr -> 'a1

val iscontrretract :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 iscontr -> 'a2
  iscontr

val proofirrelevancecontr : 'a1 iscontr -> 'a1 -> 'a1 -> 'a1 paths

type ('x, 'y) hfiber = ('x, 'y paths) total2

val make_hfiber : ('a1 -> 'a2) -> 'a2 -> 'a1 -> 'a2 paths -> ('a1, 'a2) hfiber

val hfiberpr1 : ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> 'a1

val hfibershomotftog :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber

val hfibershomotgtof :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber

val hfibertriangle1 :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> ('a1, 'a2)
  hfiber paths -> 'a2 paths paths

val hfibertriangle1inv0 :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> ('a1, 'a2)
  hfiber paths -> 'a2 paths paths

val hfibertriangle2 :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> 'a1 paths
  -> 'a2 paths paths -> ('a1, 'a2) hfiber paths

type 't coconusfromt = ('t, 't paths) total2

val coconusfromtpair : 'a1 -> 'a1 -> 'a1 paths -> 'a1 coconusfromt

type 't coconustot = ('t, 't paths) total2

val coconustotpair : 'a1 -> 'a1 -> 'a1 paths -> 'a1 coconustot

val coconustot_isProofIrrelevant :
  'a1 -> 'a1 coconustot -> 'a1 coconustot -> 'a1 coconustot paths

val iscontrcoconusfromt : 'a1 -> 'a1 coconusfromt iscontr

type ('x, 'y) isweq = 'y -> ('x, 'y) hfiber iscontr

val idisweq : ('a1, 'a1) isweq

type ('x, 'y) weq = ('x -> 'y, ('x, 'y) isweq) total2

val pr1weq : ('a1, 'a2) weq -> 'a1 -> 'a2

val weqproperty : ('a1, 'a2) weq -> ('a1, 'a2) isweq

val weqccontrhfiber : ('a1, 'a2) weq -> 'a2 -> ('a1, 'a2) hfiber

val weqccontrhfiber2 :
  ('a1, 'a2) weq -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber paths

val make_weq : ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) weq

val invmap : ('a1, 'a2) weq -> 'a2 -> 'a1

val homotweqinvweq : ('a1, 'a2) weq -> 'a2 -> 'a2 paths

val homotinvweqweq0 : ('a1, 'a2) weq -> 'a1 -> 'a1 paths

val homotinvweqweq : ('a1, 'a2) weq -> 'a1 -> 'a1 paths

val invmaponpathsweq : ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 paths -> 'a1 paths

val diaglemma2 :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths ->
  'a2 paths paths

val homotweqinvweqweq : ('a1, 'a2) weq -> 'a1 -> 'a2 paths paths

val iscontrweqb : ('a1, 'a2) weq -> 'a2 iscontr -> 'a1 iscontr

val isProofIrrelevantUnit : coq_unit -> coq_unit -> coq_unit paths

val unitl0 : coq_unit paths -> coq_unit coconustot

val unitl1 : coq_unit coconustot -> coq_unit paths

val unitl2 : coq_unit paths -> coq_unit paths paths

val unitl3 : coq_unit paths -> coq_unit paths paths

val iscontrunit : coq_unit iscontr

val iscontrpathsinunit : coq_unit -> coq_unit -> coq_unit paths iscontr

val ifcontrthenunitl0 :
  coq_unit paths -> coq_unit paths -> coq_unit paths paths

val isweqcontrtounit : 'a1 iscontr -> ('a1, coq_unit) isweq

val hfibersgftog :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a3) hfiber -> ('a2, 'a3)
  hfiber

val constr2 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 -> ('a2, 'a1)
  hfiber -> (('a1, 'a1) hfiber, ('a2, 'a1) hfiber paths) total2

val iscontrhfiberl1 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 -> ('a1, 'a1)
  hfiber iscontr -> ('a2, 'a1) hfiber iscontr

val homothfiber1 :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber

val homothfiber2 :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber

val homothfiberretr :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber paths

val iscontrhfiberl2 :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber iscontr -> ('a1, 'a2) hfiber iscontr

val isweqhomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) isweq ->
  ('a1, 'a2) isweq

val isweq_iso :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a2 -> 'a2 paths) ->
  ('a1, 'a2) isweq

val isweqinvmap : ('a1, 'a2) weq -> ('a2, 'a1) isweq

val invweq : ('a1, 'a2) weq -> ('a2, 'a1) weq

val iscontrweqf : ('a1, 'a2) weq -> 'a1 iscontr -> 'a2 iscontr

val weqhfibershomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> (('a1, 'a2)
  hfiber, ('a1, 'a2) hfiber) weq

val twooutof3a :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) isweq -> ('a2, 'a3) isweq ->
  ('a1, 'a2) isweq

val twooutof3c :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a2, 'a3) isweq ->
  ('a1, 'a3) isweq

val isweqcontrcontr :
  ('a1 -> 'a2) -> 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) isweq

val weqcomp : ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq

val coprodf :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) coprod -> ('a3, 'a4) coprod

type ('p, 'q) equality_cases = __

val equality_by_case :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths -> ('a1,
  'a2) equality_cases

val ii1_injectivity : 'a1 -> 'a1 -> ('a1, 'a2) coprod paths -> 'a1 paths

val negpathsii1ii2 : 'a1 -> 'a2 -> ('a1, 'a2) coprod paths neg

val negpathsii2ii1 : 'a1 -> 'a2 -> ('a1, 'a2) coprod paths neg

val boolascoprod : ((coq_unit, coq_unit) coprod, bool) weq

type ('x, 'y) boolsumfun = __

val coprodtoboolsum :
  ('a1, 'a2) coprod -> (bool, ('a1, 'a2) boolsumfun) total2

val boolsumtocoprod :
  (bool, ('a1, 'a2) boolsumfun) total2 -> ('a1, 'a2) coprod

val isweqcoprodtoboolsum :
  (('a1, 'a2) coprod, (bool, ('a1, 'a2) boolsumfun) total2) isweq

val weqcoprodtoboolsum :
  (('a1, 'a2) coprod, (bool, ('a1, 'a2) boolsumfun) total2) weq

val nopathstruetofalse : bool paths -> empty

val nopathsfalsetotrue : bool paths -> empty

val onefiber :
  'a1 -> ('a1 -> ('a1 paths, 'a2 neg) coprod) -> ('a2, ('a1, 'a2) total2)
  isweq

type ('x, 'y, 'z) complxstr = 'x -> 'z paths

val ezmap :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> 'a1 ->
  ('a2, 'a3) hfiber

type ('x, 'y, 'z) isfibseq = ('x, ('y, 'z) hfiber) isweq

type ('x, 'y, 'z) fibseqstr =
  (('x, 'y, 'z) complxstr, ('x, 'y, 'z) isfibseq) total2

val make_fibseqstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> ('a1,
  'a2, 'a3) isfibseq -> (('a1, 'a2, 'a3) complxstr, ('a1, 'a2, 'a3) isfibseq)
  total2

val fibseqstrtocomplxstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> ('a1,
  'a2, 'a3) complxstr

val ezweq :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> ('a1,
  ('a2, 'a3) hfiber) weq

val d1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a3 paths -> 'a1

val ezmap1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a3 paths -> ('a1, 'a2) hfiber

val invezmap1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr -> 'a2 ->
  ('a1, 'a2) hfiber -> 'a3 paths

val isweqezmap1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  ('a3 paths, ('a1, 'a2) hfiber) isweq

val ezweq1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  ('a3 paths, ('a1, 'a2) hfiber) weq

val fibseq1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  ('a3 paths, 'a1, 'a2) fibseqstr

val ezweq2 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a1 -> ('a2 paths, ('a3 paths, 'a1) hfiber) weq

val ezmappr1 : 'a1 -> 'a2 -> (('a1, 'a2) total2, 'a1) hfiber

val invezmappr1 : 'a1 -> (('a1, 'a2) total2, 'a1) hfiber -> 'a2

val isweqezmappr1 : 'a1 -> ('a2, (('a1, 'a2) total2, 'a1) hfiber) isweq

val isfibseqpr1 : 'a1 -> ('a2, ('a1, 'a2) total2, 'a1) isfibseq

val fibseqpr1 : 'a1 -> ('a2, ('a1, 'a2) total2, 'a1) fibseqstr

val ezweq1pr1 :
  'a1 -> ('a1, 'a2) total2 -> ('a1 paths, ('a2, ('a1, 'a2) total2) hfiber) weq

val isfibseqg : ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, 'a1, 'a2) isfibseq

val fibseqg : ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, 'a1, 'a2) fibseqstr

val d1g : ('a1 -> 'a2) -> 'a2 -> 'a1 -> 'a2 paths -> ('a1, 'a2) hfiber

val ezweq1g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a2 paths, (('a1, 'a2) hfiber, 'a1) hfiber)
  weq

val fibseq1g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a2 paths, ('a1, 'a2) hfiber, 'a1) fibseqstr

val d2g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a1 paths -> 'a2 paths

val ezweq3g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> (('a1, 'a2)
  hfiber paths, ('a1 paths, 'a2 paths) hfiber) weq

val hfibersftogf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ('a1, 'a2)
  hfiber -> ('a1, 'a3) hfiber

val ezmaphf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ('a1, 'a2)
  hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber

val invezmaphf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
  hfiber, ('a2, 'a3) hfiber) hfiber -> ('a1, 'a2) hfiber

val ffgg :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
  hfiber, ('a2, 'a3) hfiber) hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3) hfiber)
  hfiber

val homotffggid :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a3)
  hfiber, ('a2, 'a3) hfiber) hfiber -> (('a1, 'a3) hfiber, ('a2, 'a3) hfiber)
  hfiber paths

val isweqezmaphf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
  hfiber, (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber) isweq

val ezweqhf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
  hfiber, (('a1, 'a3) hfiber, ('a2, 'a3) hfiber) hfiber) weq

val fibseqhf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> (('a1, 'a2)
  hfiber, ('a1, 'a3) hfiber, ('a2, 'a3) hfiber) fibseqstr

val isweqinvezmaphf :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a2, 'a3) hfiber -> ((('a1, 'a3)
  hfiber, ('a2, 'a3) hfiber) hfiber, ('a1, 'a2) hfiber) isweq

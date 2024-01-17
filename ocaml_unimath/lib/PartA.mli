open Preamble

type __ = Obj.t

val fromempty : empty -> 'a1

val tounit : 'a1 -> coq_unit

val termfun : 'a1 -> coq_unit -> 'a1

val idfun : 'a1 -> 'a1

val funcomp : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3

val curry : (('a1, 'a2) total2 -> 'a3) -> 'a1 -> 'a2 -> 'a3

val uncurry : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> 'a3

type 'x binop = 'x -> 'x -> 'x

val iteration : ('a1 -> 'a1) -> nat -> 'a1 -> 'a1

val adjev : 'a1 -> ('a1 -> 'a2) -> 'a2

val adjev2 : ((('a1 -> 'a2) -> 'a2) -> 'a2) -> 'a1 -> 'a2

type ('x, 'y) dirprod = ('x, 'y) total2

val dirprod_pr1 : ('a1, 'a2) dirprod -> 'a1

val dirprod_pr2 : ('a1, 'a2) dirprod -> 'a2

val make_dirprod : 'a1 -> 'a2 -> ('a1, 'a2) dirprod

val dirprodadj : (('a1, 'a2) dirprod -> 'a3) -> 'a1 -> 'a2 -> 'a3

val dirprodf :
  ('a1 -> 'a2) -> ('a3 -> 'a4) -> ('a1, 'a3) dirprod -> ('a2, 'a4) dirprod

val ddualand :
  (('a1 -> 'a3) -> 'a3) -> (('a2 -> 'a3) -> 'a3) -> (('a1, 'a2) dirprod ->
  'a3) -> 'a3

type 'x neg = 'x -> empty

val negf : ('a1 -> 'a2) -> 'a2 neg -> 'a1 neg

type 'x dneg = 'x neg neg

val dnegf : ('a1 -> 'a2) -> 'a1 dneg -> 'a2 dneg

val todneg : 'a1 -> 'a1 dneg

val dnegnegtoneg : 'a1 neg dneg -> 'a1 neg

val dneganddnegl1 : 'a1 dneg -> 'a2 dneg -> ('a1 -> 'a2 neg) neg

val dneganddnegimpldneg : 'a1 dneg -> 'a2 dneg -> ('a1, 'a2) dirprod dneg

type ('x, 'y) logeq = ('x -> 'y, 'y -> 'x) dirprod

val isrefl_logeq : ('a1, 'a1) logeq

val issymm_logeq : ('a1, 'a2) logeq -> ('a2, 'a1) logeq

val logeqnegs : ('a1, 'a2) logeq -> ('a1 neg, 'a2 neg) logeq

val logeq_both_true : 'a1 -> 'a2 -> ('a1, 'a2) logeq

val logeq_both_false : 'a1 neg -> 'a2 neg -> ('a1, 'a2) logeq

val logeq_trans : ('a1, 'a2) logeq -> ('a2, 'a3) logeq -> ('a1, 'a3) logeq

val funcomp_assoc :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1 -> 'a4) paths

val uncurry_curry :
  (('a1, 'a3) total2 -> 'a2) -> ('a1, 'a3) total2 -> 'a2 paths

val curry_uncurry : ('a1 -> 'a3 -> 'a2) -> 'a1 -> 'a3 -> 'a2 paths

val pathscomp0 : 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths

val pathscomp0rid : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathsinv0 : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths

val path_assoc :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1
  paths paths

val pathsinv0l : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathsinv0r : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathsinv0inv0 : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathscomp_cancel_left :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths paths
  -> 'a1 paths paths

val pathscomp_cancel_right :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths paths
  -> 'a1 paths paths

val pathscomp_inv :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths

val pathsdirprod :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) dirprod
  paths

val dirprodeq :
  ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod -> 'a1 paths -> 'a2 paths -> ('a1,
  'a2) dirprod paths

val maponpaths : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths

val map_on_two_paths :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths
  -> 'a3 paths

val maponpathscomp0 :
  'a1 -> 'a1 -> 'a1 -> ('a1 -> 'a2) -> 'a1 paths -> 'a1 paths -> 'a2 paths
  paths

val maponpathsinv0 :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths paths

val maponpathsidfun : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val maponpathscomp :
  'a1 -> 'a1 -> ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 paths -> 'a3 paths paths

type ('x, 'p) homot = 'x -> 'p paths

val homotrefl : ('a1 -> 'a2) -> ('a1, 'a2) homot

val homotcomp :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1,
  'a2) homot -> ('a1, 'a2) homot

val invhomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) homot

val funhomot :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a2, 'a3) homot -> ('a1,
  'a3) homot

val funhomotsec :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2 -> 'a3) -> ('a2, 'a3) homot -> ('a1,
  'a3) homot

val homotfun :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a2 -> 'a3) -> ('a1,
  'a3) homot

val toforallpaths :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1, 'a2) homot

val eqtohomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1 -> 'a2) paths -> ('a1, 'a2) homot

val maponpathshomidinv :
  ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths

val maponpathshomid1 :
  ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths
  paths

val maponpathshomid2 :
  ('a1 -> 'a1) -> ('a1 -> 'a1 paths) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths
  paths

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

val transportf_eq : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) total2 paths

val transportb : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2

val idpath_transportf : 'a1 -> 'a2 -> 'a2 paths

val functtransportf :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 -> 'a3 paths

val functtransportb :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a3 -> 'a3 paths

val transport_f_b :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths

val transport_b_f :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths

val transport_f_f :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths

val transport_b_b :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 paths

val transport_map :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 paths

val transport_section : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths

val transportf_fun :
  'a1 -> 'a1 -> 'a1 paths -> ('a3 -> 'a2) -> ('a3 -> 'a2) paths

val transportb_fun' :
  'a1 -> 'a1 -> ('a2 -> 'a3) -> 'a1 paths -> 'a2 -> 'a3 paths

val transportf_const : 'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a2) paths

val transportb_const : 'a1 -> 'a1 -> 'a1 paths -> ('a2 -> 'a2) paths

val transportf_paths :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 paths

val transportbfinv : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 paths

val transportfbinv : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 paths

val base_paths :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths -> 'a1
  paths

val two_arg_paths :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
  -> 'a3 paths

val two_arg_paths_f :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
  -> 'a3 paths

val two_arg_paths_b :
  ('a1 -> 'a2 -> 'a3) -> 'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths
  -> 'a3 paths

val dirprod_paths :
  ('a1, 'a2) dirprod -> ('a1, 'a2) dirprod -> 'a1 paths -> 'a2 paths -> ('a1,
  'a2) dirprod paths

val total2_paths_f :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> ('a1,
  'a2) total2 paths

val total2_paths_b :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> ('a1,
  'a2) total2 paths

val total2_paths2 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) total2
  paths

val total2_paths2_f :
  'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) total2
  paths

val total2_paths2_b :
  'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths -> ('a1, 'a2) total2
  paths

val pair_path_in2 : 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) total2 paths

val fiber_paths :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths -> 'a2
  paths

val total2_fiber_paths :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> ('a1, 'a2) total2 paths -> ('a1,
  'a2) total2 paths paths

val base_total2_paths :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> 'a1
  paths paths

val transportf_fiber_total2_paths :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> 'a1 paths -> 'a2 paths -> 'a2
  paths paths

val total2_base_map : ('a1 -> 'a2) -> ('a1, 'a3) total2 -> ('a2, 'a3) total2

val total2_section_path :
  'a1 -> 'a2 -> ('a1 -> 'a2) -> ('a1, 'a2) total2 paths -> 'a2 paths

val transportD : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a3 -> 'a3

val transportf_total2 :
  'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a3) total2 -> ('a2, 'a3) total2 paths

val transportf_dirprod :
  ('a1, ('a2, 'a3) dirprod) total2 -> ('a1, ('a2, 'a3) dirprod) total2 -> 'a1
  paths -> ('a2, 'a3) dirprod paths

val transportb_dirprod :
  ('a1, ('a2, 'a3) dirprod) total2 -> ('a1, ('a2, 'a3) dirprod) total2 -> 'a1
  paths -> ('a2, 'a3) dirprod paths

val transportf_id1 :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths

val transportf_id2 :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths

val transportf_id3 : 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths

val famhomotfun :
  ('a1, coq_UU) homot -> ('a1, 'a2) total2 -> ('a1, 'a3) total2

val famhomothomothomot :
  ('a1, coq_UU) homot -> ('a1, coq_UU) homot -> ('a1, coq_UU paths) homot ->
  (('a1, 'a2) total2, ('a1, 'a3) total2) homot

type 't iscontr = ('t, 't -> 't paths) total2

val make_iscontr : 'a1 -> ('a1 -> 'a1 paths) -> 'a1 iscontr

val iscontrpr1 : 'a1 iscontr -> 'a1

val iscontr_uniqueness : 'a1 iscontr -> 'a1 -> 'a1 paths

val iscontrretract :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2 paths) -> 'a1 iscontr -> 'a2
  iscontr

val proofirrelevancecontr : 'a1 iscontr -> 'a1 -> 'a1 -> 'a1 paths

val path_to_ctr : ('a1, 'a2) total2 iscontr -> 'a1 -> 'a2 -> 'a1 paths

type ('x, 'y) hfiber = ('x, 'y paths) total2

val make_hfiber : ('a1 -> 'a2) -> 'a2 -> 'a1 -> 'a2 paths -> ('a1, 'a2) hfiber

val hfiberpr1 : ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> 'a1

val hfiberpr2 : ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> 'a2 paths

val hfibershomotftog :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber

val hfibershomotgtof :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> ('a1, 'a2)
  hfiber -> ('a1, 'a2) hfiber

val hfibertriangle1 :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> ('a1, 'a2)
  hfiber paths -> 'a2 paths paths

val hfibertriangle1' :
  ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber paths -> 'a2
  paths paths

val hfibertriangle1inv0 :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> ('a1, 'a2)
  hfiber paths -> 'a2 paths paths

val hfibertriangle1inv0' :
  ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) hfiber -> ('a1, 'a2 paths) total2 paths
  -> 'a2 paths paths

val hfibertriangle2 :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber -> 'a1 paths
  -> 'a2 paths paths -> ('a1, 'a2) hfiber paths

type 't coconusfromt = ('t, 't paths) total2

val coconusfromtpair : 'a1 -> 'a1 -> 'a1 paths -> 'a1 coconusfromt

val coconusfromtpr1 : 'a1 -> 'a1 coconusfromt -> 'a1

type 't coconustot = ('t, 't paths) total2

val coconustotpair : 'a1 -> 'a1 -> 'a1 paths -> 'a1 coconustot

val coconustotpr1 : 'a1 -> 'a1 coconustot -> 'a1

val coconustot_isProofIrrelevant :
  'a1 -> 'a1 coconustot -> 'a1 coconustot -> 'a1 coconustot paths

val iscontrcoconustot : 'a1 -> 'a1 coconustot iscontr

val coconusfromt_isProofIrrelevant :
  'a1 -> 'a1 coconusfromt -> 'a1 coconusfromt -> 'a1 coconusfromt paths

val iscontrcoconusfromt : 'a1 -> 'a1 coconusfromt iscontr

type 't pathsspace = ('t, 't coconusfromt) total2

val pathsspacetriple : 'a1 -> 'a1 -> 'a1 paths -> 'a1 pathsspace

val deltap : 'a1 -> 'a1 pathsspace

type 't pathsspace' = (('t, 't) dirprod, 't paths) total2

type ('x, 'y) coconusf = ('y, ('x, 'y) hfiber) total2

val fromcoconusf : ('a1 -> 'a2) -> ('a1, 'a2) coconusf -> 'a1

val tococonusf : ('a1 -> 'a2) -> 'a1 -> ('a1, 'a2) coconusf

val homottofromcoconusf :
  ('a1 -> 'a2) -> ('a1, 'a2) coconusf -> ('a1, 'a2) coconusf paths

val homotfromtococonusf : ('a1 -> 'a2) -> 'a1 -> 'a1 paths

type ('x, 'y) isweq = 'y -> ('x, 'y) hfiber iscontr

val idisweq : ('a1, 'a1) isweq

type ('x, 'y) weq = ('x -> 'y, ('x, 'y) isweq) total2

val pr1weq : ('a1, 'a2) weq -> 'a1 -> 'a2

val weqproperty : ('a1, 'a2) weq -> ('a1, 'a2) isweq

val weqccontrhfiber : ('a1, 'a2) weq -> 'a2 -> ('a1, 'a2) hfiber

val weqccontrhfiber2 :
  ('a1, 'a2) weq -> 'a2 -> ('a1, 'a2) hfiber -> ('a1, 'a2) hfiber paths

val make_weq : ('a1 -> 'a2) -> ('a1, 'a2) isweq -> ('a1, 'a2) weq

val idweq : ('a1, 'a1) weq

val isweqtoempty : ('a1 -> empty) -> ('a1, empty) isweq

val weqtoempty : ('a1 -> empty) -> ('a1, empty) weq

val isweqtoempty2 : ('a1 -> 'a2) -> 'a2 neg -> ('a1, 'a2) isweq

val weqtoempty2 : ('a1 -> 'a2) -> 'a2 neg -> ('a1, 'a2) weq

val weqempty : 'a1 neg -> 'a2 neg -> ('a1, 'a2) weq

val invmap : ('a1, 'a2) weq -> 'a2 -> 'a1

val homotweqinvweq : ('a1, 'a2) weq -> 'a2 -> 'a2 paths

val homotinvweqweq0 : ('a1, 'a2) weq -> 'a1 -> 'a1 paths

val homotinvweqweq : ('a1, 'a2) weq -> 'a1 -> 'a1 paths

val invmaponpathsweq : ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 paths -> 'a1 paths

val invmaponpathsweqid : ('a1, 'a2) weq -> 'a1 -> 'a1 paths paths

val pathsweq1 : ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a2 paths -> 'a1 paths

val pathsweq1' : ('a1, 'a2) weq -> 'a1 -> 'a2 -> 'a1 paths -> 'a2 paths

val pathsweq3 : ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths paths

val pathsweq4 : ('a1, 'a2) weq -> 'a1 -> 'a1 -> 'a2 paths -> 'a2 paths paths

val homotweqinv :
  ('a1 -> 'a3) -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a1, 'a3) homot -> ('a2,
  'a3) homot

val homotweqinv' :
  ('a1 -> 'a3) -> ('a1, 'a2) weq -> ('a2 -> 'a3) -> ('a2, 'a3) homot -> ('a1,
  'a3) homot

val internal_paths_rew : 'a1 -> 'a2 -> 'a1 -> 'a1 paths -> 'a2

val internal_paths_rew_r : 'a1 -> 'a1 -> 'a2 -> 'a1 paths -> 'a2

val isinjinvmap :
  ('a1, 'a2) weq -> ('a1, 'a2) weq -> ('a2, 'a1) homot -> ('a1, 'a2) homot

val isinjinvmap' :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a1) -> ('a2, 'a2)
  homot -> ('a1, 'a1) homot -> ('a2, 'a1) homot -> ('a1, 'a2) homot

val diaglemma2 :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 paths -> 'a2 paths paths ->
  'a2 paths paths

val homotweqinvweqweq : ('a1, 'a2) weq -> 'a1 -> 'a2 paths paths

val weq_transportf_adjointness : ('a1, 'a2) weq -> 'a1 -> 'a3 -> 'a3 paths

val weq_transportb_adjointness : ('a1, 'a2) weq -> 'a1 -> 'a3 -> 'a3 paths

val isweqtransportf : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq

val isweqtransportb : 'a1 -> 'a1 -> 'a1 paths -> ('a2, 'a2) isweq

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

val weqcontrtounit : 'a1 iscontr -> ('a1, coq_unit) weq

val iscontrifweqtounit : ('a1, coq_unit) weq -> 'a1 iscontr

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

val remakeweq :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1, 'a2) weq

val remakeweq_eq :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a1 -> 'a2) paths

val remakeweq_eq' :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> ('a2 -> 'a1) paths

val iscontr_move_point : 'a1 -> 'a1 iscontr -> 'a1 iscontr

val iscontr_move_point_eq : 'a1 -> 'a1 iscontr -> 'a1 paths

val remakeweqinv :
  ('a1, 'a2) weq -> ('a2 -> 'a1) -> ('a2, 'a1) homot -> ('a1, 'a2) weq

val remakeweqinv_eq :
  ('a1, 'a2) weq -> ('a2 -> 'a1) -> ('a2, 'a1) homot -> ('a1 -> 'a2) paths

val remakeweqinv_eq' :
  ('a1, 'a2) weq -> ('a2 -> 'a1) -> ('a2, 'a1) homot -> ('a2 -> 'a1) paths

val remakeweqboth :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a2) homot -> ('a2,
  'a1) homot -> ('a1, 'a2) weq

val remakeweqboth_eq :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a2) homot -> ('a2,
  'a1) homot -> ('a1 -> 'a2) paths

val remakeweqboth_eq' :
  ('a1, 'a2) weq -> ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1, 'a2) homot -> ('a2,
  'a1) homot -> ('a2 -> 'a1) paths

val isweqhomot_iff :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> (('a1, 'a2) isweq,
  ('a1, 'a2) isweq) logeq

val isweq_to_isweq_unit :
  ('a1 -> coq_unit) -> ('a1 -> coq_unit) -> ('a1, coq_unit) isweq -> ('a1,
  coq_unit) isweq

val isweq_iso :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a2 -> 'a2 paths) ->
  ('a1, 'a2) isweq

val weq_iso :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a2 -> 'a2 paths) ->
  ('a1, 'a2) weq

type ('x, 'y) coq_UniqueConstruction =
  ('y -> ('x, 'y paths) total2, 'x -> 'x -> 'y paths -> 'x paths) dirprod

val coq_UniqueConstruction_to_weq :
  ('a1 -> 'a2) -> ('a1, 'a2) coq_UniqueConstruction -> ('a1, 'a2) isweq

val isweqinvmap : ('a1, 'a2) weq -> ('a2, 'a1) isweq

val invweq : ('a1, 'a2) weq -> ('a2, 'a1) weq

val invinv : ('a1, 'a2) weq -> 'a1 -> 'a2 paths

val pr1_invweq : ('a1, 'a2) weq -> ('a2 -> 'a1) paths

val iscontrweqf : ('a1, 'a2) weq -> 'a1 iscontr -> 'a2 iscontr

type ('a, 'b) coq_PathPair = ('a paths, 'b paths) total2

val total2_paths_equiv :
  ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths, ('a1,
  'a2) coq_PathPair) weq

val wequnittocontr : 'a1 iscontr -> (coq_unit, 'a1) weq

val isweqmaponpaths :
  ('a1, 'a2) weq -> 'a1 -> 'a1 -> ('a1 paths, 'a2 paths) isweq

val weqonpaths : ('a1, 'a2) weq -> 'a1 -> 'a1 -> ('a1 paths, 'a2 paths) weq

val isweqpathsinv0 : 'a1 -> 'a1 -> ('a1 paths, 'a1 paths) isweq

val weqpathsinv0 : 'a1 -> 'a1 -> ('a1 paths, 'a1 paths) weq

val isweqpathscomp0r :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) isweq

val isweqtococonusf : ('a1 -> 'a2) -> ('a1, ('a1, 'a2) coconusf) isweq

val weqtococonusf : ('a1 -> 'a2) -> ('a1, ('a1, 'a2) coconusf) weq

val isweqfromcoconusf : ('a1 -> 'a2) -> (('a1, 'a2) coconusf, 'a1) isweq

val weqfromcoconusf : ('a1 -> 'a2) -> (('a1, 'a2) coconusf, 'a1) weq

val isweqdeltap : ('a1, 'a1 pathsspace) isweq

val isweqpr1pr1 : ('a1 pathsspace', 'a1) isweq

val weqhfibershomot :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> ('a1, 'a2) homot -> 'a2 -> (('a1, 'a2)
  hfiber, ('a1, 'a2) hfiber) weq

val twooutof3a :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a3) isweq -> ('a2, 'a3) isweq ->
  ('a1, 'a2) isweq

val twooutof3b :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a1, 'a3) isweq ->
  ('a2, 'a3) isweq

val isweql3 :
  ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a1 -> 'a1 paths) -> ('a1, 'a2) isweq ->
  ('a2, 'a1) isweq

val twooutof3c :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> ('a2, 'a3) isweq ->
  ('a1, 'a3) isweq

val twooutof3c_iff_2 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1, 'a2) isweq -> (('a2, 'a3) isweq,
  ('a1, 'a3) isweq) logeq

val twooutof3c_iff_1 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a2, 'a3) isweq -> (('a1, 'a2) isweq,
  ('a1, 'a3) isweq) logeq

val twooutof3c_iff_1_homot :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1, 'a3) homot -> ('a2,
  'a3) isweq -> (('a1, 'a2) isweq, ('a1, 'a3) isweq) logeq

val twooutof3c_iff_2_homot :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a1 -> 'a3) -> ('a1, 'a3) homot -> ('a1,
  'a2) isweq -> (('a2, 'a3) isweq, ('a1, 'a3) isweq) logeq

val isweqcontrcontr :
  ('a1 -> 'a2) -> 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) isweq

val weqcontrcontr : 'a1 iscontr -> 'a2 iscontr -> ('a1, 'a2) weq

val weqcomp : ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1, 'a3) weq

val weqcomp_to_funcomp_app :
  'a1 -> ('a1, 'a2) weq -> ('a2, 'a3) weq -> 'a3 paths

val weqcomp_to_funcomp :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a1 -> 'a3) paths

val invmap_weqcomp_expand :
  ('a1, 'a2) weq -> ('a2, 'a3) weq -> ('a3 -> 'a1) paths

val twooutofsixu :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1, 'a3) isweq -> ('a2,
  'a4) isweq -> ('a1, 'a2) isweq

val twooutofsixv :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1, 'a3) isweq -> ('a2,
  'a4) isweq -> ('a2, 'a3) isweq

val twooutofsixw :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> ('a3 -> 'a4) -> ('a1, 'a3) isweq -> ('a2,
  'a4) isweq -> ('a3, 'a4) isweq

val isweqdirprodf :
  ('a1, 'a2) weq -> ('a3, 'a4) weq -> (('a1, 'a3) dirprod, ('a2, 'a4)
  dirprod) isweq

val weqdirprodf :
  ('a1, 'a2) weq -> ('a3, 'a4) weq -> (('a1, 'a3) dirprod, ('a2, 'a4)
  dirprod) weq

(* val weqtodirprodwithunit : ('a1, ('a1, coq_unit) dirprod) weq  *)

(* val weqtodirprodwithunit : ('a1, ('a1, coq_unit) dirprod) weq  *)

val total2asstor :
  (('a1, 'a2) total2, 'a3) total2 -> ('a1, ('a2, 'a3) total2) total2

val total2asstol :
  ('a1, ('a2, 'a3) total2) total2 -> (('a1, 'a2) total2, 'a3) total2

(* val weqtotal2asstor : *)
(*   ((('a1, 'a2) total2, 'a3) total2, ('a1, ('a2, 'a3) total2) total2) weq *)

(* val weqtotal2asstol : *)
(*   (('a1, ('a2, 'a3) total2) total2, (('a1, 'a2) total2, 'a3) total2) weq *)

(* val weqdirprodasstor : *)
(*   ((('a1, 'a2) dirprod, 'a3) dirprod, ('a1, ('a2, 'a3) dirprod) dirprod) weq *)

(* val weqdirprodasstol : *)
(*   (('a1, ('a2, 'a3) dirprod) dirprod, (('a1, 'a2) dirprod, 'a3) dirprod) weq *)

(* val weqdirprodcomm : (('a1, 'a2) dirprod, ('a2, 'a1) dirprod) weq *)

(* val weqtotal2dirprodcomm : *)
(*   ((('a1, 'a2) dirprod, 'a3) total2, (('a2, 'a1) dirprod, 'a3) total2) weq *)

(* val weqtotal2dirprodassoc : *)
(*   ((('a1, 'a2) dirprod, 'a3) total2, ('a1, ('a2, 'a3) total2) total2) weq *)

(* val weqtotal2dirprodassoc' : *)
(*   ((('a1, 'a2) dirprod, 'a3) total2, ('a2, ('a1, 'a3) total2) total2) weq *)

(* val weqtotal2comm12 : *)
(*   ((('a1, 'a2) total2, 'a3) total2, (('a1, 'a3) total2, 'a2) total2) weq *)

val rdistrtocoprod :
  ('a1, ('a2, 'a3) coprod) dirprod -> (('a1, 'a2) dirprod, ('a1, 'a3)
  dirprod) coprod

val rdistrtoprod :
  (('a1, 'a2) dirprod, ('a1, 'a3) dirprod) coprod -> ('a1, ('a2, 'a3) coprod)
  dirprod

val isweqrdistrtoprod :
  ((('a1, 'a2) dirprod, ('a1, 'a3) dirprod) coprod, ('a1, ('a2, 'a3) coprod)
  dirprod) isweq

(* val weqrdistrtoprod : *)
(*   ((('a1, 'a2) dirprod, ('a1, 'a3) dirprod) coprod, ('a1, ('a2, 'a3) coprod) *)
(*   dirprod) weq *)

(* val isweqrdistrtocoprod : *)
(*   (('a1, ('a2, 'a3) coprod) dirprod, (('a1, 'a2) dirprod, ('a1, 'a3) dirprod) *)
(*   coprod) isweq *)

(* val weqrdistrtocoprod : *)
(*   (('a1, ('a2, 'a3) coprod) dirprod, (('a1, 'a2) dirprod, ('a1, 'a3) dirprod) *)
(*   coprod) weq *)

val fromtotal2overcoprod :
  (('a1, 'a2) coprod, 'a3) total2 -> (('a1, 'a3) total2, ('a2, 'a3) total2)
  coprod

val tototal2overcoprod :
  (('a1, 'a3) total2, ('a2, 'a3) total2) coprod -> (('a1, 'a2) coprod, 'a3)
  total2

(* val weqtotal2overcoprod : *)
(*   ((('a1, 'a2) coprod, 'a3) total2, (('a1, 'a3) total2, ('a2, 'a3) total2) *)
(*   coprod) weq *)

val sumofmaps : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2) coprod -> 'a3

val coprodasstor :
  (('a1, 'a2) coprod, 'a3) coprod -> ('a1, ('a2, 'a3) coprod) coprod

val coprodasstol :
  ('a1, ('a2, 'a3) coprod) coprod -> (('a1, 'a2) coprod, 'a3) coprod

val sumofmaps_assoc_left :
  ('a1 -> 'a4) -> ('a2 -> 'a4) -> ('a3 -> 'a4) -> (('a1, ('a2, 'a3) coprod)
  coprod, 'a4) homot

val sumofmaps_assoc_right :
  ('a1 -> 'a4) -> ('a2 -> 'a4) -> ('a3 -> 'a4) -> ((('a1, 'a2) coprod, 'a3)
  coprod, 'a4) homot

val isweqcoprodasstor :
  ((('a1, 'a2) coprod, 'a3) coprod, ('a1, ('a2, 'a3) coprod) coprod) isweq

(* val weqcoprodasstor : *)
(*   ((('a1, 'a2) coprod, 'a3) coprod, ('a1, ('a2, 'a3) coprod) coprod) weq *)

(* val isweqcoprodasstol : *)
(*   (('a1, ('a2, 'a3) coprod) coprod, (('a1, 'a2) coprod, 'a3) coprod) isweq *)

(* val weqcoprodasstol : *)
(*   (('a1, ('a2, 'a3) coprod) coprod, (('a1, 'a2) coprod, 'a3) coprod) weq *)

val coprodcomm : ('a1, 'a2) coprod -> ('a2, 'a1) coprod

val isweqcoprodcomm : (('a1, 'a2) coprod, ('a2, 'a1) coprod) isweq

val weqcoprodcomm : (('a1, 'a2) coprod, ('a2, 'a1) coprod) weq

val isweqii1withneg : ('a2 -> empty) -> ('a1, ('a1, 'a2) coprod) isweq

val weqii1withneg : 'a2 neg -> ('a1, ('a1, 'a2) coprod) weq

val isweqii2withneg : ('a1 -> empty) -> ('a2, ('a1, 'a2) coprod) isweq

val weqii2withneg : 'a1 neg -> ('a2, ('a1, 'a2) coprod) weq

val coprodf :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a1, 'a2) coprod -> ('a3, 'a4) coprod

val coprodf1 : ('a1 -> 'a3) -> ('a1, 'a2) coprod -> ('a3, 'a2) coprod

val coprodf2 : ('a2 -> 'a3) -> ('a1, 'a2) coprod -> ('a1, 'a3) coprod

val homotcoprodfcomp :
  ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a3 -> 'a5) -> ('a4 -> 'a6) -> (('a1, 'a2)
  coprod, ('a5, 'a6) coprod) homot

val homotcoprodfhomot :
  ('a1 -> 'a3) -> ('a1 -> 'a3) -> ('a2 -> 'a4) -> ('a2 -> 'a4) -> ('a1, 'a3)
  homot -> ('a2, 'a4) homot -> (('a1, 'a2) coprod, ('a3, 'a4) coprod) homot

val isweqcoprodf :
  ('a1, 'a3) weq -> ('a2, 'a4) weq -> (('a1, 'a2) coprod, ('a3, 'a4) coprod)
  isweq

val weqcoprodf :
  ('a1, 'a3) weq -> ('a2, 'a4) weq -> (('a1, 'a2) coprod, ('a3, 'a4) coprod)
  weq

val weqcoprodf1 : ('a1, 'a3) weq -> (('a1, 'a2) coprod, ('a3, 'a2) coprod) weq

val weqcoprodf2 : ('a2, 'a3) weq -> (('a1, 'a2) coprod, ('a1, 'a3) coprod) weq

type ('p, 'q) equality_cases = __

val equality_by_case :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) coprod paths -> ('a1,
  'a2) equality_cases

val inv_equality_by_case :
  ('a1, 'a2) coprod -> ('a1, 'a2) coprod -> ('a1, 'a2) equality_cases ->
  ('a1, 'a2) coprod paths

val ii1_injectivity : 'a1 -> 'a1 -> ('a1, 'a2) coprod paths -> 'a1 paths

val ii2_injectivity : 'a2 -> 'a2 -> ('a1, 'a2) coprod paths -> 'a2 paths

val negpathsii1ii2 : 'a1 -> 'a2 -> ('a1, 'a2) coprod paths neg

val negpathsii2ii1 : 'a1 -> 'a2 -> ('a1, 'a2) coprod paths neg

val boolascoprod : ((coq_unit, coq_unit) coprod, bool) weq

val coprodtobool : ('a1, 'a2) coprod -> bool

type ('x, 'y) boolsumfun = __

val coprodtoboolsum :
  ('a1, 'a2) coprod -> (bool, ('a1, 'a2) boolsumfun) total2

val boolsumtocoprod :
  (bool, ('a1, 'a2) boolsumfun) total2 -> ('a1, 'a2) coprod

val isweqcoprodtoboolsum :
  (('a1, 'a2) coprod, (bool, ('a1, 'a2) boolsumfun) total2) isweq

val weqcoprodtoboolsum :
  (('a1, 'a2) coprod, (bool, ('a1, 'a2) boolsumfun) total2) weq

val isweqboolsumtocoprod :
  ((bool, ('a1, 'a2) boolsumfun) total2, ('a1, 'a2) coprod) isweq

val weqboolsumtocoprod :
  ((bool, ('a1, 'a2) boolsumfun) total2, ('a1, 'a2) coprod) weq

val weqcoprodsplit :
  ('a1 -> ('a2, 'a3) coprod) -> ('a1, (('a2, ('a1, ('a2, 'a3) coprod) hfiber)
  total2, ('a3, ('a1, ('a2, 'a3) coprod) hfiber) total2) coprod) weq

val boolchoice : bool -> (bool paths, bool paths) coprod

type bool_to_type = __

val nopathstruetofalse : bool paths -> empty

val nopathsfalsetotrue : bool paths -> empty

val truetonegfalse : bool -> bool paths -> bool paths neg

val falsetonegtrue : bool -> bool paths -> bool paths neg

val negtruetofalse : bool -> bool paths neg -> bool paths

val negfalsetotrue : bool -> bool paths neg -> bool paths

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

val d2 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a1 -> 'a2 paths -> 'a3 paths

val ezweq2 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a1 -> ('a2 paths, ('a3 paths, 'a1) hfiber) weq

val fibseq2 :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr -> 'a2 ->
  'a1 -> ('a2 paths, 'a3 paths, 'a1) fibseqstr

val ezmappr1 : 'a1 -> 'a2 -> (('a1, 'a2) total2, 'a1) hfiber

val invezmappr1 : 'a1 -> (('a1, 'a2) total2, 'a1) hfiber -> 'a2

val isweqezmappr1 : 'a1 -> ('a2, (('a1, 'a2) total2, 'a1) hfiber) isweq

val ezweqpr1 : 'a1 -> ('a2, (('a1, 'a2) total2, 'a1) hfiber) weq

val isfibseqpr1 : 'a1 -> ('a2, ('a1, 'a2) total2, 'a1) isfibseq

val fibseqpr1 : 'a1 -> ('a2, ('a1, 'a2) total2, 'a1) fibseqstr

val ezweq1pr1 :
  'a1 -> ('a1, 'a2) total2 -> ('a1 paths, ('a2, ('a1, 'a2) total2) hfiber) weq

val isfibseqg : ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, 'a1, 'a2) isfibseq

val ezweqg : ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, ('a1, 'a2) hfiber) weq

val fibseqg : ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, 'a1, 'a2) fibseqstr

val d1g : ('a1 -> 'a2) -> 'a2 -> 'a1 -> 'a2 paths -> ('a1, 'a2) hfiber

val ezweq1g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a2 paths, (('a1, 'a2) hfiber, 'a1) hfiber)
  weq

val fibseq1g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a2 paths, ('a1, 'a2) hfiber, 'a1) fibseqstr

val d2g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a1 paths -> 'a2 paths

val ezweq2g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> ('a1 paths, ('a2 paths,
  ('a1, 'a2) hfiber) hfiber) weq

val fibseq2g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> ('a1 paths, 'a2 paths,
  ('a1, 'a2) hfiber) fibseqstr

val d3g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> ('a1, 'a2)
  hfiber paths -> 'a1 paths

val homotd3g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> ('a1, 'a2)
  hfiber paths -> 'a1 paths paths

val ezweq3g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> (('a1, 'a2)
  hfiber paths, ('a1 paths, 'a2 paths) hfiber) weq

val fibseq3g :
  ('a1 -> 'a2) -> 'a2 -> 'a1 -> ('a1, 'a2) hfiber -> 'a2 paths -> (('a1, 'a2)
  hfiber paths, 'a1 paths, 'a2 paths) fibseqstr

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

val weqhfibersgwtog :
  ('a1, 'a2) weq -> ('a2 -> 'a3) -> 'a3 -> (('a1, 'a3) hfiber, ('a2, 'a3)
  hfiber) weq

val totalfun : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) total2 -> ('a1, 'a3) total2

val isweqtotaltofib :
  ('a1 -> 'a2 -> 'a3) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq -> 'a1
  -> ('a2, 'a3) isweq

val weqtotaltofib :
  ('a1 -> 'a2 -> 'a3) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq -> 'a1
  -> ('a2, 'a3) weq

val isweqfibtototal :
  ('a1 -> ('a2, 'a3) weq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq

val isweqfibtototal' :
  ('a1 -> ('a2, 'a3) weq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) isweq

val weqfibtototal :
  ('a1 -> ('a2, 'a3) weq) -> (('a1, 'a2) total2, ('a1, 'a3) total2) weq

val fpmap : ('a1 -> 'a2) -> ('a1, 'a3) total2 -> ('a2, 'a3) total2

val hffpmap2 :
  ('a1 -> 'a2) -> ('a1, 'a3) total2 -> (('a2, 'a3) total2, ('a1, 'a2) hfiber)
  total2

val centralfiber : 'a1 -> ('a2, ('a1 coconusfromt, 'a2) total2) isweq

val isweqhff :
  ('a1 -> 'a2) -> (('a1, 'a3) total2, (('a2, 'a3) total2, ('a1, 'a2) hfiber)
  total2) isweq

val hfiberfpmap :
  ('a1 -> 'a2) -> ('a2, 'a3) total2 -> (('a1, 'a3) total2, ('a2, 'a3) total2)
  hfiber -> ('a1, 'a2) hfiber

val isweqhfiberfp :
  ('a1 -> 'a2) -> ('a2, 'a3) total2 -> ((('a1, 'a3) total2, ('a2, 'a3)
  total2) hfiber, ('a1, 'a2) hfiber) isweq

val isweqfpmap :
  ('a1, 'a2) weq -> (('a1, 'a3) total2, ('a2, 'a3) total2) isweq

val weqfp_map : ('a1, 'a2) weq -> ('a1, 'a3) total2 -> ('a2, 'a3) total2

val weqfp_invmap : ('a1, 'a2) weq -> ('a2, 'a3) total2 -> ('a1, 'a3) total2

val weqfp : ('a1, 'a2) weq -> (('a1, 'a3) total2, ('a2, 'a3) total2) weq

val weqfp_compute_1 :
  ('a1, 'a2) weq -> (('a1, 'a3) total2, ('a2, 'a3) total2) homot

val weqfp_compute_2 :
  ('a1, 'a2) weq -> (('a2, 'a3) total2, ('a1, 'a3) total2) homot

val weqtotal2overcoprod' :
  (('a2, 'a3) coprod, 'a1) weq -> (('a1, 'a4) total2, (('a2, 'a4) total2,
  ('a3, 'a4) total2) coprod) weq

val fromtotal2overunit : (coq_unit, 'a1) total2 -> 'a1

val tototal2overunit : 'a1 -> (coq_unit, 'a1) total2

val weqtotal2overunit : ((coq_unit, 'a1) total2, 'a1) weq

val bandfmap :
  ('a1 -> 'a2) -> ('a1 -> 'a3 -> 'a4) -> ('a1, 'a3) total2 -> ('a2, 'a4)
  total2

val isweqbandfmap :
  ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> (('a1, 'a3) total2, ('a2, 'a4)
  total2) isweq

val weqbandf :
  ('a1, 'a2) weq -> ('a1 -> ('a3, 'a4) weq) -> (('a1, 'a3) total2, ('a2, 'a4)
  total2) weq

type ('x, 'x0, 'y, 'z) commsqstr = 'z -> 'y paths

val hfibersgtof' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> 'a1 -> ('a4, 'a1) hfiber -> ('a2, 'a3) hfiber

val hfibersg'tof :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> 'a2 -> ('a4, 'a2) hfiber -> ('a1, 'a3) hfiber

val transposcommsqstr :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> ('a2, 'a1, 'a3, 'a4) commsqstr

val complxstrtocommsqstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) complxstr ->
  (coq_unit, 'a2, 'a3, 'a1) commsqstr

val commsqstrtocomplxstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> (coq_unit, 'a2, 'a3, 'a1) commsqstr
  -> ('a1, 'a2, 'a3) complxstr

type ('x, 'x0, 'y) hfp = (('x, 'x0) dirprod, 'y paths) total2

val hfpg : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> 'a1

val hfpg' : ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3) hfp -> 'a2

val commsqZtohfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> 'a4 -> ('a1, 'a2, 'a3) hfp

val commsqZtohfphomot :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> 'a4 -> 'a1 paths

val commsqZtohfphomot' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> 'a4 -> 'a2 paths

type ('x, 'x0, 'y) hfpoverX = ('x, ('x0, 'y) hfiber) total2

type ('x, 'x0, 'y) hfpoverX' = ('x0, ('x, 'y) hfiber) total2

val weqhfptohfpoverX :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a1, 'a2, 'a3)
  hfpoverX) weq

val weqhfptohfpoverX' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a1, 'a2, 'a3)
  hfpoverX') weq

val weqhfpcomm :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a2, 'a1, 'a3) hfp)
  weq

val commhfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3, ('a1, 'a2, 'a3) hfp)
  commsqstr

val hfibertohfp :
  ('a1 -> 'a2) -> 'a2 -> ('a1, 'a2) hfiber -> (coq_unit, 'a1, 'a2) hfp

val hfptohfiber :
  ('a1 -> 'a2) -> 'a2 -> (coq_unit, 'a1, 'a2) hfp -> ('a1, 'a2) hfiber

val weqhfibertohfp :
  ('a1 -> 'a2) -> 'a2 -> (('a1, 'a2) hfiber, (coq_unit, 'a1, 'a2) hfp) weq

val hfp_left :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a1, ('a2, 'a3)
  hfiber) total2) weq

val hfp_right :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, 'a2, 'a3) hfp, ('a2, ('a1, 'a3)
  hfiber) total2) weq

val hfiber_comm :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> (('a1, ('a2, 'a3) hfiber) total2, ('a2,
  ('a1, 'a3) hfiber) total2) weq

type ('x, 'x0, 'y, 'z) ishfsq = ('z, ('x, 'x0, 'y) hfp) isweq

type ('x, 'x0, 'y, 'z) hfsqstr =
  (('x, 'x0, 'y, 'z) commsqstr, ('z, ('x, 'x0, 'y) hfp) isweq) total2

val make_hfsqstr :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> ('a4, ('a1, 'a2, 'a3) hfp) isweq -> (('a1, 'a2, 'a3,
  'a4) commsqstr, ('a4, ('a1, 'a2, 'a3) hfp) isweq) total2

val hfsqstrtocommsqstr :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> ('a1, 'a2, 'a3, 'a4) commsqstr

val weqZtohfp :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> ('a4, ('a1, 'a2, 'a3) hfp) weq

val isweqhfibersgtof' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> 'a1 -> (('a4, 'a1) hfiber, ('a2, 'a3) hfiber) isweq

val weqhfibersgtof' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> 'a1 -> (('a4, 'a1) hfiber, ('a2, 'a3) hfiber) weq

val ishfsqweqhfibersgtof' :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> ('a1 -> (('a4, 'a1) hfiber, ('a2, 'a3) hfiber)
  isweq) -> ('a1, 'a2, 'a3, 'a4) hfsqstr

val isweqhfibersg'tof :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> 'a2 -> (('a4, 'a2) hfiber, ('a1, 'a3) hfiber) isweq

val weqhfibersg'tof :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> 'a2 -> (('a4, 'a2) hfiber, ('a1, 'a3) hfiber) weq

val ishfsqweqhfibersg'tof :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) commsqstr -> ('a2 -> (('a4, 'a2) hfiber, ('a1, 'a3) hfiber)
  isweq) -> ('a1, 'a2, 'a3, 'a4) hfsqstr

val transposhfpsqstr :
  ('a1 -> 'a3) -> ('a2 -> 'a3) -> ('a4 -> 'a1) -> ('a4 -> 'a2) -> ('a1, 'a2,
  'a3, 'a4) hfsqstr -> ('a2, 'a1, 'a3, 'a4) hfsqstr

val fibseqstrtohfsqstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> ('a1, 'a2, 'a3) fibseqstr ->
  (coq_unit, 'a2, 'a3, 'a1) hfsqstr

val hfsqstrtofibseqstr :
  ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a3 -> (coq_unit, 'a2, 'a3, 'a1) hfsqstr ->
  ('a1, 'a2, 'a3) fibseqstr

val transitive_paths_weq :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> ('a1 paths, 'a1 paths) weq

(* val weqtotal2comm : *)
(*   (('a1, ('a2, 'a3) total2) total2, ('a2, ('a1, 'a3) total2) total2) weq *)

val pathsdirprodweq :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> (('a1, 'a2) dirprod paths, ('a1 paths, 'a2
  paths) dirprod) weq

(* val dirprod_with_contr_r : 'a1 iscontr -> ('a2, ('a2, 'a1) dirprod) weq *)

(* val dirprod_with_contr_l : 'a1 iscontr -> ('a2, ('a1, 'a2) dirprod) weq *)

(* val total2_assoc_fun_left : *)
(*   (('a1 -> ('a2, 'a3) total2, 'a4) total2, ('a1 -> 'a2, ('a1 -> 'a3, 'a4) *)
(*   total2) total2) weq *)

(* val sec_total2_distributivity : *)
(*   ('a1 -> ('a2, 'a3) total2, ('a1 -> 'a2, 'a1 -> 'a3) total2) weq *)

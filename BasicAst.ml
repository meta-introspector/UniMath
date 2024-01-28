open All_Forall
open BinInt
open BinNums
open Byte
open CRelationClasses
open Classes
open Datatypes
open EqDecInstances
open Kernames
open List
open MCList
open MCOption
open MCReflect
open MCString
open Nat
open ReflectEq
open SpecFloat
open Specif
open Bytestring

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type name =
| Coq_nAnon
| Coq_nNamed of ident

(** val name_rect : 'a1 -> (ident -> 'a1) -> name -> 'a1 **)

let name_rect f f0 = function
| Coq_nAnon -> f
| Coq_nNamed i -> f0 i

(** val name_rec : 'a1 -> (ident -> 'a1) -> name -> 'a1 **)

let name_rec f f0 = function
| Coq_nAnon -> f
| Coq_nNamed i -> f0 i

(** val coq_NoConfusionPackage_name : name coq_NoConfusionPackage **)

let coq_NoConfusionPackage_name =
  Build_NoConfusionPackage

(** val name_eqdec : name -> name -> name dec_eq **)

let name_eqdec x y =
  match x with
  | Coq_nAnon ->
    (match y with
     | Coq_nAnon -> Coq_left
     | Coq_nNamed _ -> Coq_right)
  | Coq_nNamed i ->
    (match y with
     | Coq_nAnon -> Coq_right
     | Coq_nNamed i0 ->
       eq_dec_point i
         (coq_EqDec_EqDecPoint
           (coq_ReflectEq_EqDec IdentOT.reflect_eq_string) i) i0)

(** val name_EqDec : name coq_EqDec **)

let name_EqDec =
  name_eqdec

type relevance =
| Relevant
| Irrelevant

(** val relevance_rect : 'a1 -> 'a1 -> relevance -> 'a1 **)

let relevance_rect f f0 = function
| Relevant -> f
| Irrelevant -> f0

(** val relevance_rec : 'a1 -> 'a1 -> relevance -> 'a1 **)

let relevance_rec f f0 = function
| Relevant -> f
| Irrelevant -> f0

(** val coq_NoConfusionPackage_relevance :
    relevance coq_NoConfusionPackage **)

let coq_NoConfusionPackage_relevance =
  Build_NoConfusionPackage

(** val relevance_eqdec : relevance -> relevance -> relevance dec_eq **)

let relevance_eqdec x y =
  match x with
  | Relevant -> (match y with
                 | Relevant -> Coq_left
                 | Irrelevant -> Coq_right)
  | Irrelevant ->
    (match y with
     | Relevant -> Coq_right
     | Irrelevant -> Coq_left)

(** val relevance_EqDec : relevance coq_EqDec **)

let relevance_EqDec =
  relevance_eqdec

type 'a binder_annot = { binder_name : 'a; binder_relevance : relevance }

(** val binder_name : 'a1 binder_annot -> 'a1 **)

let binder_name b =
  b.binder_name

(** val binder_relevance : 'a1 binder_annot -> relevance **)

let binder_relevance b =
  b.binder_relevance

(** val coq_NoConfusionPackage_binder_annot :
    'a1 binder_annot coq_NoConfusionPackage **)

let coq_NoConfusionPackage_binder_annot =
  Build_NoConfusionPackage

(** val eqdec_binder_annot : 'a1 coq_EqDec -> 'a1 binder_annot coq_EqDec **)

let eqdec_binder_annot e x y =
  let { binder_name = binder_name0; binder_relevance = binder_relevance0 } = x
  in
  let { binder_name = binder_name1; binder_relevance = binder_relevance1 } = y
  in
  (match eq_dec_point binder_name0 (coq_EqDec_EqDecPoint e binder_name0)
           binder_name1 with
   | Coq_left ->
     eq_dec_point binder_relevance0
       (coq_EqDec_EqDecPoint relevance_EqDec binder_relevance0)
       binder_relevance1
   | Coq_right -> Coq_right)

(** val map_binder_annot :
    ('a1 -> 'a2) -> 'a1 binder_annot -> 'a2 binder_annot **)

let map_binder_annot f b =
  { binder_name = (f b.binder_name); binder_relevance = b.binder_relevance }

type aname = name binder_annot

(** val anqme_eqdec : aname coq_EqDec **)

let anqme_eqdec =
  eqdec_binder_annot name_EqDec

(** val eqb_binder_annot : 'a1 binder_annot -> 'a1 binder_annot -> bool **)

let eqb_binder_annot b b' =
  match eq_dec relevance_EqDec b.binder_relevance b'.binder_relevance with
  | Coq_left -> Coq_true
  | Coq_right -> Coq_false

(** val string_of_name : name -> String.t **)

let string_of_name = function
| Coq_nAnon -> String.String (Coq_x5f, String.EmptyString)
| Coq_nNamed n -> n

(** val string_of_relevance : relevance -> String.t **)

let string_of_relevance = function
| Relevant ->
  String.String (Coq_x52, (String.String (Coq_x65, (String.String (Coq_x6c,
    (String.String (Coq_x65, (String.String (Coq_x76, (String.String
    (Coq_x61, (String.String (Coq_x6e, (String.String (Coq_x74,
    String.EmptyString)))))))))))))))
| Irrelevant ->
  String.String (Coq_x49, (String.String (Coq_x72, (String.String (Coq_x72,
    (String.String (Coq_x65, (String.String (Coq_x6c, (String.String
    (Coq_x65, (String.String (Coq_x76, (String.String (Coq_x61,
    (String.String (Coq_x6e, (String.String (Coq_x74,
    String.EmptyString)))))))))))))))))))

type cast_kind =
| VmCast
| NativeCast
| Cast

(** val cast_kind_rect : 'a1 -> 'a1 -> 'a1 -> cast_kind -> 'a1 **)

let cast_kind_rect f f0 f1 = function
| VmCast -> f
| NativeCast -> f0
| Cast -> f1

(** val cast_kind_rec : 'a1 -> 'a1 -> 'a1 -> cast_kind -> 'a1 **)

let cast_kind_rec f f0 f1 = function
| VmCast -> f
| NativeCast -> f0
| Cast -> f1

(** val coq_NoConfusionPackage_cast_kind :
    cast_kind coq_NoConfusionPackage **)

let coq_NoConfusionPackage_cast_kind =
  Build_NoConfusionPackage

(** val cast_kind_eqdec : cast_kind -> cast_kind -> cast_kind dec_eq **)

let cast_kind_eqdec x y =
  match x with
  | VmCast -> (match y with
               | VmCast -> Coq_left
               | _ -> Coq_right)
  | NativeCast -> (match y with
                   | NativeCast -> Coq_left
                   | _ -> Coq_right)
  | Cast -> (match y with
             | Cast -> Coq_left
             | _ -> Coq_right)

(** val cast_kind_EqDec : cast_kind coq_EqDec **)

let cast_kind_EqDec =
  cast_kind_eqdec

type case_info = { ci_ind : inductive; ci_npar : nat; ci_relevance : relevance }

(** val ci_ind : case_info -> inductive **)

let ci_ind c =
  c.ci_ind

(** val ci_npar : case_info -> nat **)

let ci_npar c =
  c.ci_npar

(** val ci_relevance : case_info -> relevance **)

let ci_relevance c =
  c.ci_relevance

(** val coq_NoConfusionPackage_case_info :
    case_info coq_NoConfusionPackage **)

let coq_NoConfusionPackage_case_info =
  Build_NoConfusionPackage

(** val case_info_eqdec : case_info -> case_info -> case_info dec_eq **)

let case_info_eqdec x y =
  let { ci_ind = ci_ind0; ci_npar = ci_npar0; ci_relevance =
    ci_relevance0 } = x
  in
  let { ci_ind = ci_ind1; ci_npar = ci_npar1; ci_relevance =
    ci_relevance1 } = y
  in
  (match eq_dec_point ci_ind0
           (coq_EqDec_EqDecPoint (coq_ReflectEq_EqDec reflect_eq_inductive)
             ci_ind0) ci_ind1 with
   | Coq_left ->
     (match eq_dec_point ci_npar0 (coq_EqDec_EqDecPoint nat_EqDec ci_npar0)
              ci_npar1 with
      | Coq_left ->
        eq_dec_point ci_relevance0
          (coq_EqDec_EqDecPoint relevance_EqDec ci_relevance0) ci_relevance1
      | Coq_right -> Coq_right)
   | Coq_right -> Coq_right)

(** val case_info_EqDec : case_info coq_EqDec **)

let case_info_EqDec =
  case_info_eqdec

(** val string_of_case_info : case_info -> String.t **)

let string_of_case_info ci =
  String.append (String.String (Coq_x28, String.EmptyString))
    (String.append (string_of_inductive ci.ci_ind)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_nat ci.ci_npar)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (string_of_relevance ci.ci_relevance)
              (String.String (Coq_x29, String.EmptyString)))))))

type recursivity_kind =
| Finite
| CoFinite
| BiFinite

(** val recursivity_kind_rect :
    'a1 -> 'a1 -> 'a1 -> recursivity_kind -> 'a1 **)

let recursivity_kind_rect f f0 f1 = function
| Finite -> f
| CoFinite -> f0
| BiFinite -> f1

(** val recursivity_kind_rec :
    'a1 -> 'a1 -> 'a1 -> recursivity_kind -> 'a1 **)

let recursivity_kind_rec f f0 f1 = function
| Finite -> f
| CoFinite -> f0
| BiFinite -> f1

(** val coq_NoConfusionPackage_recursivity_kind :
    recursivity_kind coq_NoConfusionPackage **)

let coq_NoConfusionPackage_recursivity_kind =
  Build_NoConfusionPackage

(** val recursivity_kind_eqdec :
    recursivity_kind -> recursivity_kind -> recursivity_kind dec_eq **)

let recursivity_kind_eqdec x y =
  match x with
  | Finite -> (match y with
               | Finite -> Coq_left
               | _ -> Coq_right)
  | CoFinite -> (match y with
                 | CoFinite -> Coq_left
                 | _ -> Coq_right)
  | BiFinite -> (match y with
                 | BiFinite -> Coq_left
                 | _ -> Coq_right)

(** val recursivity_kind_EqDec : recursivity_kind coq_EqDec **)

let recursivity_kind_EqDec =
  recursivity_kind_eqdec

type conv_pb =
| Conv
| Cumul

(** val conv_pb_rect : 'a1 -> 'a1 -> conv_pb -> 'a1 **)

let conv_pb_rect f f0 = function
| Conv -> f
| Cumul -> f0

(** val conv_pb_rec : 'a1 -> 'a1 -> conv_pb -> 'a1 **)

let conv_pb_rec f f0 = function
| Conv -> f
| Cumul -> f0

(** val coq_NoConfusionPackage_conv_pb : conv_pb coq_NoConfusionPackage **)

let coq_NoConfusionPackage_conv_pb =
  Build_NoConfusionPackage

(** val conv_pb_eqdec : conv_pb -> conv_pb -> conv_pb dec_eq **)

let conv_pb_eqdec x y =
  match x with
  | Conv -> (match y with
             | Conv -> Coq_left
             | Cumul -> Coq_right)
  | Cumul -> (match y with
              | Conv -> Coq_right
              | Cumul -> Coq_left)

(** val conv_pb_EqDec : conv_pb coq_EqDec **)

let conv_pb_EqDec =
  conv_pb_eqdec

(** val conv_pb_leqb : conv_pb -> conv_pb -> bool **)

let conv_pb_leqb pb1 pb2 =
  match pb1 with
  | Conv -> Coq_true
  | Cumul -> (match pb2 with
              | Conv -> Coq_false
              | Cumul -> Coq_true)

(** val fresh_evar_id : nat **)

let fresh_evar_id =
  O

type 'term def = { dname : aname; dtype : 'term; dbody : 'term; rarg : nat }

(** val dname : 'a1 def -> aname **)

let dname d =
  d.dname

(** val dtype : 'a1 def -> 'a1 **)

let dtype d =
  d.dtype

(** val dbody : 'a1 def -> 'a1 **)

let dbody d =
  d.dbody

(** val rarg : 'a1 def -> nat **)

let rarg d =
  d.rarg

(** val coq_NoConfusionPackage_def : 'a1 def coq_NoConfusionPackage **)

let coq_NoConfusionPackage_def =
  Build_NoConfusionPackage

(** val def_eq_dec : 'a1 coq_EqDec -> 'a1 def coq_EqDec **)

let def_eq_dec x x0 y =
  let { dname = dname0; dtype = dtype0; dbody = dbody0; rarg = rarg0 } = x0 in
  let { dname = dname1; dtype = dtype1; dbody = dbody1; rarg = rarg1 } = y in
  (match eq_dec_point dname0 (coq_EqDec_EqDecPoint anqme_eqdec dname0) dname1 with
   | Coq_left ->
     (match eq_dec_point dtype0 (coq_EqDec_EqDecPoint x dtype0) dtype1 with
      | Coq_left ->
        (match eq_dec_point dbody0 (coq_EqDec_EqDecPoint x dbody0) dbody1 with
         | Coq_left ->
           eq_dec_point rarg0 (coq_EqDec_EqDecPoint nat_EqDec rarg0) rarg1
         | Coq_right -> Coq_right)
      | Coq_right -> Coq_right)
   | Coq_right -> Coq_right)

(** val string_of_def : ('a1 -> String.t) -> 'a1 def -> String.t **)

let string_of_def f def0 =
  String.append (String.String (Coq_x28, String.EmptyString))
    (String.append (string_of_name def0.dname.binder_name)
      (String.append (String.String (Coq_x2c, String.EmptyString))
        (String.append (string_of_relevance def0.dname.binder_relevance)
          (String.append (String.String (Coq_x2c, String.EmptyString))
            (String.append (f def0.dtype)
              (String.append (String.String (Coq_x2c, String.EmptyString))
                (String.append (f def0.dbody)
                  (String.append (String.String (Coq_x2c,
                    String.EmptyString))
                    (String.append (string_of_nat def0.rarg) (String.String
                      (Coq_x29, String.EmptyString)))))))))))

(** val print_def :
    ('a1 -> String.t) -> ('a1 -> String.t) -> 'a1 def -> String.t **)

let print_def f g def0 =
  String.append (string_of_name def0.dname.binder_name)
    (String.append (String.String (Coq_x20, (String.String (Coq_x7b,
      (String.String (Coq_x20, (String.String (Coq_x73, (String.String
      (Coq_x74, (String.String (Coq_x72, (String.String (Coq_x75,
      (String.String (Coq_x63, (String.String (Coq_x74, (String.String
      (Coq_x20, String.EmptyString))))))))))))))))))))
      (String.append (string_of_nat def0.rarg)
        (String.append (String.String (Coq_x20, (String.String (Coq_x7d,
          String.EmptyString))))
          (String.append (String.String (Coq_x20, (String.String (Coq_x3a,
            (String.String (Coq_x20, String.EmptyString))))))
            (String.append (f def0.dtype)
              (String.append (String.String (Coq_x20, (String.String
                (Coq_x3a, (String.String (Coq_x3d, (String.String (Coq_x20,
                String.EmptyString)))))))) (String.append nl (g def0.dbody))))))))

(** val map_def : ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 def -> 'a2 def **)

let map_def tyf bodyf d =
  { dname = d.dname; dtype = (tyf d.dtype); dbody = (bodyf d.dbody); rarg =
    d.rarg }

type 'term mfixpoint = 'term def list

(** val test_def : ('a1 -> bool) -> ('a1 -> bool) -> 'a1 def -> bool **)

let test_def tyf bodyf d =
  match tyf d.dtype with
  | Coq_true -> bodyf d.dbody
  | Coq_false -> Coq_false

type ('a, 'p, 'x) tFixProp = ('a def, ('p, 'x) prod) coq_All

type 'term typ_or_sort_ =
| Typ of 'term
| Sort

(** val typ_or_sort_map :
    ('a1 -> 'a2) -> 'a1 typ_or_sort_ -> 'a2 typ_or_sort_ **)

let typ_or_sort_map f = function
| Typ t1 -> Typ (f t1)
| Sort -> Sort

(** val typ_or_sort_default :
    ('a1 -> 'a2) -> 'a1 typ_or_sort_ -> 'a2 -> 'a2 **)

let typ_or_sort_default f t0 d =
  match t0 with
  | Typ t1 -> f t1
  | Sort -> d

type 'term context_decl = { decl_name : aname; decl_body : 'term option;
                            decl_type : 'term }

(** val decl_name : 'a1 context_decl -> aname **)

let decl_name c =
  c.decl_name

(** val decl_body : 'a1 context_decl -> 'a1 option **)

let decl_body c =
  c.decl_body

(** val decl_type : 'a1 context_decl -> 'a1 **)

let decl_type c =
  c.decl_type

(** val coq_NoConfusionPackage_context_decl :
    'a1 context_decl coq_NoConfusionPackage **)

let coq_NoConfusionPackage_context_decl =
  Build_NoConfusionPackage

(** val map_decl : ('a1 -> 'a2) -> 'a1 context_decl -> 'a2 context_decl **)

let map_decl f d =
  { decl_name = d.decl_name; decl_body = (option_map f d.decl_body);
    decl_type = (f d.decl_type) }

(** val map_context :
    ('a1 -> 'a2) -> 'a1 context_decl list -> 'a2 context_decl list **)

let map_context f c =
  map (map_decl f) c

(** val test_decl : ('a1 -> bool) -> 'a1 context_decl -> bool **)

let test_decl f d =
  match option_default f d.decl_body Coq_true with
  | Coq_true -> f d.decl_type
  | Coq_false -> Coq_false

(** val snoc : 'a1 list -> 'a1 -> 'a1 list **)

let snoc _UU0393_ d =
  Coq_cons (d, _UU0393_)

type ('a, 'p) ondecl = ('p, __) prod

(** val mapi_context :
    (nat -> 'a1 -> 'a2) -> 'a1 context_decl list -> 'a2 context_decl list **)

let rec mapi_context f = function
| Coq_nil -> Coq_nil
| Coq_cons (d, _UU0393_) ->
  Coq_cons ((map_decl (f (length _UU0393_)) d), (mapi_context f _UU0393_))

(** val test_context : ('a1 -> bool) -> 'a1 context_decl list -> bool **)

let rec test_context f = function
| Coq_nil -> Coq_true
| Coq_cons (d, _UU0393_) ->
  (match test_context f _UU0393_ with
   | Coq_true -> test_decl f d
   | Coq_false -> Coq_false)

(** val test_context_k :
    (nat -> 'a1 -> bool) -> nat -> 'a1 context_decl list -> bool **)

let rec test_context_k f k = function
| Coq_nil -> Coq_true
| Coq_cons (d, _UU0393_) ->
  (match test_context_k f k _UU0393_ with
   | Coq_true -> test_decl (f (add (length _UU0393_) k)) d
   | Coq_false -> Coq_false)

type ('term, 'p) onctx_k = ('term context_decl, ('term, 'p) ondecl) coq_Alli

(** val ondeclP :
    ('a1 -> bool) -> 'a1 context_decl -> ('a1 -> 'a2 reflectT) -> ('a1, 'a2)
    ondecl reflectT **)

let ondeclP p d hr =
  let { decl_name = _; decl_body = decl_body0; decl_type = decl_type0 } = d in
  let r = hr decl_type0 in
  (match r with
   | ReflectT p0 ->
     let r0 = reflect_option_default p hr decl_body0 in
     (match r0 with
      | ReflectT o -> ReflectT (Coq_pair (p0, o))
      | ReflectF -> ReflectF)
   | ReflectF -> ReflectF)

(** val onctxP :
    ('a1 -> bool) -> 'a1 context_decl list -> ('a1 context_decl, ('a1, __)
    ondecl) coq_All reflectT **)

let onctxP p ctx =
  equiv_reflectT (test_context p ctx) (fun _ ->
    let rec f = function
    | Coq_nil -> All_nil
    | Coq_cons (y, l0) ->
      All_cons (y, l0,
        (elimT (test_decl p y) (ondeclP p y (reflectT_pred p))), (f l0))
    in f ctx)

(** val fold_context_k :
    (nat -> 'a1 -> 'a2) -> 'a1 context_decl list -> 'a2 context_decl list **)

let fold_context_k f _UU0393_ =
  List.rev (mapi (fun k' decl -> map_decl (f k') decl) (List.rev _UU0393_))

(** val mapi_context_In :
    'a1 context_decl list -> (nat -> 'a1 context_decl -> __ -> 'a1
    context_decl) -> 'a1 context_decl list **)

let rec mapi_context_In ctx f =
  match ctx with
  | Coq_nil -> Coq_nil
  | Coq_cons (c, l) ->
    Coq_cons ((f (length l) c __),
      (mapi_context_In l (fun n x _ -> f n x __)))

type 'term mapi_context_In_graph =
| Coq_mapi_context_In_graph_equation_1 of (nat -> 'term context_decl -> __ ->
                                          'term context_decl)
| Coq_mapi_context_In_graph_equation_2 of 'term context_decl
   * 'term context_decl list
   * (nat -> 'term context_decl -> __ -> 'term context_decl)
   * 'term mapi_context_In_graph

(** val mapi_context_In_graph_rect :
    ((nat -> 'a1 context_decl -> __ -> 'a1 context_decl) -> 'a2) -> ('a1
    context_decl -> 'a1 context_decl list -> (nat -> 'a1 context_decl -> __
    -> 'a1 context_decl) -> 'a1 mapi_context_In_graph -> 'a2 -> 'a2) -> 'a1
    context_decl list -> (nat -> 'a1 context_decl -> __ -> 'a1 context_decl)
    -> 'a1 context_decl list -> 'a1 mapi_context_In_graph -> 'a2 **)

let rec mapi_context_In_graph_rect f f0 _ _ _ = function
| Coq_mapi_context_In_graph_equation_1 f1 -> f f1
| Coq_mapi_context_In_graph_equation_2 (x, xs, f1, hind) ->
  f0 x xs f1 hind
    (mapi_context_In_graph_rect f f0 xs (fun n x0 _ -> f1 n x0 __)
      (mapi_context_In xs (fun n x0 _ -> f1 n x0 __)) hind)

(** val mapi_context_In_graph_correct :
    'a1 context_decl list -> (nat -> 'a1 context_decl -> __ -> 'a1
    context_decl) -> 'a1 mapi_context_In_graph **)

let rec mapi_context_In_graph_correct ctx f =
  match ctx with
  | Coq_nil -> Coq_mapi_context_In_graph_equation_1 f
  | Coq_cons (c, l) ->
    Coq_mapi_context_In_graph_equation_2 (c, l, f,
      (mapi_context_In_graph_correct l (fun n x _ -> f n x __)))

(** val mapi_context_In_elim :
    ((nat -> 'a1 context_decl -> __ -> 'a1 context_decl) -> 'a2) -> ('a1
    context_decl -> 'a1 context_decl list -> (nat -> 'a1 context_decl -> __
    -> 'a1 context_decl) -> 'a2 -> 'a2) -> 'a1 context_decl list -> (nat ->
    'a1 context_decl -> __ -> 'a1 context_decl) -> 'a2 **)

let mapi_context_In_elim f f0 ctx f1 =
  let rec f2 _ _ _ = function
  | Coq_mapi_context_In_graph_equation_1 f3 -> f f3
  | Coq_mapi_context_In_graph_equation_2 (x, xs, f3, hind) ->
    f0 x xs f3
      (f2 xs (fun n x0 _ -> f3 n x0 __)
        (mapi_context_In xs (fun n x0 _ -> f3 n x0 __)) hind)
  in f2 ctx f1 (mapi_context_In ctx f1) (mapi_context_In_graph_correct ctx f1)

(** val coq_FunctionalElimination_mapi_context_In :
    ((nat -> 'a1 context_decl -> __ -> 'a1 context_decl) -> __) -> ('a1
    context_decl -> 'a1 context_decl list -> (nat -> 'a1 context_decl -> __
    -> 'a1 context_decl) -> __ -> __) -> 'a1 context_decl list -> (nat -> 'a1
    context_decl -> __ -> 'a1 context_decl) -> __ **)

let coq_FunctionalElimination_mapi_context_In =
  mapi_context_In_elim

(** val coq_FunctionalInduction_mapi_context_In :
    ('a1 context_decl list -> (nat -> 'a1 context_decl -> __ -> 'a1
    context_decl) -> 'a1 context_decl list) coq_FunctionalInduction **)

let coq_FunctionalInduction_mapi_context_In =
  Obj.magic mapi_context_In_graph_correct

(** val fold_context_In :
    'a1 context_decl list -> ('a1 context_decl list -> 'a1 context_decl -> __
    -> 'a1 context_decl) -> 'a1 context_decl list **)

let rec fold_context_In ctx f =
  match ctx with
  | Coq_nil -> Coq_nil
  | Coq_cons (c, l) ->
    let xs' = fold_context_In l (fun n x _ -> f n x __) in
    Coq_cons ((f xs' c __), xs')

type 'term fold_context_In_graph =
| Coq_fold_context_In_graph_equation_1 of ('term context_decl list -> 'term
                                          context_decl -> __ -> 'term
                                          context_decl)
| Coq_fold_context_In_graph_equation_2 of 'term context_decl
   * 'term context_decl list
   * ('term context_decl list -> 'term context_decl -> __ -> 'term
     context_decl) * 'term fold_context_In_graph

(** val fold_context_In_graph_rect :
    (('a1 context_decl list -> 'a1 context_decl -> __ -> 'a1 context_decl) ->
    'a2) -> ('a1 context_decl -> 'a1 context_decl list -> ('a1 context_decl
    list -> 'a1 context_decl -> __ -> 'a1 context_decl) -> 'a1
    fold_context_In_graph -> 'a2 -> 'a2) -> 'a1 context_decl list -> ('a1
    context_decl list -> 'a1 context_decl -> __ -> 'a1 context_decl) -> 'a1
    context_decl list -> 'a1 fold_context_In_graph -> 'a2 **)

let rec fold_context_In_graph_rect f f0 _ _ _ = function
| Coq_fold_context_In_graph_equation_1 f2 -> f f2
| Coq_fold_context_In_graph_equation_2 (x, xs, f2, hind) ->
  f0 x xs f2 hind
    (fold_context_In_graph_rect f f0 xs (fun n x0 _ -> f2 n x0 __)
      (fold_context_In xs (fun n x0 _ -> f2 n x0 __)) hind)

(** val fold_context_In_graph_correct :
    'a1 context_decl list -> ('a1 context_decl list -> 'a1 context_decl -> __
    -> 'a1 context_decl) -> 'a1 fold_context_In_graph **)

let rec fold_context_In_graph_correct ctx f =
  match ctx with
  | Coq_nil -> Coq_fold_context_In_graph_equation_1 f
  | Coq_cons (c, l) ->
    Coq_fold_context_In_graph_equation_2 (c, l, f,
      (fold_context_In_graph_correct l (fun n x _ -> f n x __)))

(** val fold_context_In_elim :
    (('a1 context_decl list -> 'a1 context_decl -> __ -> 'a1 context_decl) ->
    'a2) -> ('a1 context_decl -> 'a1 context_decl list -> ('a1 context_decl
    list -> 'a1 context_decl -> __ -> 'a1 context_decl) -> 'a2 -> 'a2) -> 'a1
    context_decl list -> ('a1 context_decl list -> 'a1 context_decl -> __ ->
    'a1 context_decl) -> 'a2 **)

let fold_context_In_elim f f0 ctx f1 =
  let rec f2 _ _ _ = function
  | Coq_fold_context_In_graph_equation_1 f4 -> f f4
  | Coq_fold_context_In_graph_equation_2 (x, xs, f4, hind) ->
    f0 x xs f4
      (f2 xs (fun n x0 _ -> f4 n x0 __)
        (fold_context_In xs (fun n x0 _ -> f4 n x0 __)) hind)
  in f2 ctx f1 (fold_context_In ctx f1) (fold_context_In_graph_correct ctx f1)

(** val coq_FunctionalElimination_fold_context_In :
    (('a1 context_decl list -> 'a1 context_decl -> __ -> 'a1 context_decl) ->
    __) -> ('a1 context_decl -> 'a1 context_decl list -> ('a1 context_decl
    list -> 'a1 context_decl -> __ -> 'a1 context_decl) -> __ -> __) -> 'a1
    context_decl list -> ('a1 context_decl list -> 'a1 context_decl -> __ ->
    'a1 context_decl) -> __ **)

let coq_FunctionalElimination_fold_context_In =
  fold_context_In_elim

(** val coq_FunctionalInduction_fold_context_In :
    ('a1 context_decl list -> ('a1 context_decl list -> 'a1 context_decl ->
    __ -> 'a1 context_decl) -> 'a1 context_decl list) coq_FunctionalInduction **)

let coq_FunctionalInduction_fold_context_In =
  Obj.magic fold_context_In_graph_correct

(** val fold_context :
    ('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
    context_decl list -> 'a1 context_decl list **)

let rec fold_context f = function
| Coq_nil -> Coq_nil
| Coq_cons (c, l) -> let xs' = fold_context f l in Coq_cons ((f xs' c), xs')

type 'term fold_context_graph =
| Coq_fold_context_graph_equation_1 of ('term context_decl list -> 'term
                                       context_decl -> 'term context_decl)
| Coq_fold_context_graph_equation_2 of ('term context_decl list -> 'term
                                       context_decl -> 'term context_decl)
   * 'term context_decl * 'term context_decl list * 'term fold_context_graph

(** val fold_context_graph_rect :
    (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a2)
    -> (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) ->
    'a1 context_decl -> 'a1 context_decl list -> 'a1 fold_context_graph ->
    'a2 -> 'a2) -> ('a1 context_decl list -> 'a1 context_decl -> 'a1
    context_decl) -> 'a1 context_decl list -> 'a1 context_decl list -> 'a1
    fold_context_graph -> 'a2 **)

let rec fold_context_graph_rect f f0 _ _ _ = function
| Coq_fold_context_graph_equation_1 f2 -> f f2
| Coq_fold_context_graph_equation_2 (f2, x, xs, hind) ->
  f0 f2 x xs hind
    (fold_context_graph_rect f f0 f2 xs (fold_context f2 xs) hind)

(** val fold_context_graph_correct :
    ('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
    context_decl list -> 'a1 fold_context_graph **)

let rec fold_context_graph_correct f = function
| Coq_nil -> Coq_fold_context_graph_equation_1 f
| Coq_cons (c, l) ->
  Coq_fold_context_graph_equation_2 (f, c, l,
    (fold_context_graph_correct f l))

(** val fold_context_elim :
    (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a2)
    -> (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) ->
    'a1 context_decl -> 'a1 context_decl list -> 'a2 -> 'a2) -> ('a1
    context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
    context_decl list -> 'a2 **)

let fold_context_elim f f0 f1 ctx =
  let rec f2 _ _ _ = function
  | Coq_fold_context_graph_equation_1 f4 -> f f4
  | Coq_fold_context_graph_equation_2 (f4, x, xs, hind) ->
    f0 f4 x xs (f2 f4 xs (fold_context f4 xs) hind)
  in f2 f1 ctx (fold_context f1 ctx) (fold_context_graph_correct f1 ctx)

(** val coq_FunctionalElimination_fold_context :
    (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> __)
    -> (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) ->
    'a1 context_decl -> 'a1 context_decl list -> __ -> __) -> ('a1
    context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
    context_decl list -> __ **)

let coq_FunctionalElimination_fold_context =
  fold_context_elim

(** val coq_FunctionalInduction_fold_context :
    (('a1 context_decl list -> 'a1 context_decl -> 'a1 context_decl) -> 'a1
    context_decl list -> 'a1 context_decl list) coq_FunctionalInduction **)

let coq_FunctionalInduction_fold_context =
  Obj.magic fold_context_graph_correct

(** val forget_types : 'a1 context_decl list -> aname list **)

let forget_types c =
  map (fun c0 -> c0.decl_name) c

(** val coq_All2_fold_impl_onctx :
    'a1 context_decl list -> 'a1 context_decl list -> ('a1 context_decl,
    ('a1, 'a4) ondecl) coq_All -> ('a1 context_decl, 'a2) coq_All2_fold ->
    ('a1 context_decl list -> 'a1 context_decl list -> 'a1 context_decl ->
    'a1 context_decl -> ('a1 context_decl, 'a2) coq_All2_fold -> 'a2 -> ('a1,
    'a4) ondecl -> 'a3) -> ('a1 context_decl, 'a3) coq_All2_fold **)

let rec coq_All2_fold_impl_onctx _ _ onc cr hcr =
  match cr with
  | All2_fold_nil ->
    let onc0 = Coq_nil,onc in
    let onc2 = let _,pr2 = onc0 in pr2 in
    (match onc2 with
     | All_nil -> All2_fold_nil
     | All_cons (_, _, _, _) -> assert false (* absurd case *))
  | All2_fold_cons (d, d', _UU0393_, _UU0393_', a, y) ->
    let onc0 = (Coq_cons (d, _UU0393_)),onc in
    let onc2 = let _,pr2 = onc0 in pr2 in
    (match onc2 with
     | All_nil -> assert false (* absurd case *)
     | All_cons (_, _, o, a0) ->
       All2_fold_cons (d, d', _UU0393_, _UU0393_',
         (coq_All2_fold_impl_onctx _UU0393_ _UU0393_' a0 a hcr),
         (hcr _UU0393_ _UU0393_' d d' a y o)))

(** val coq_All2_fold_mapi :
    'a1 context_decl list -> 'a1 context_decl list -> (nat -> 'a1 -> 'a1) ->
    (nat -> 'a1 -> 'a1) -> (('a1 context_decl, 'a2) coq_All2_fold, ('a1
    context_decl, 'a2) coq_All2_fold) iffT **)

let coq_All2_fold_mapi _UU0393_ _UU0394_ f g =
  Coq_pair ((fun x ->
    let rec f0 _ _ = function
    | All2_fold_nil -> All2_fold_nil
    | All2_fold_cons (d, d', _UU0393_0, _UU0393_', a0, y) ->
      All2_fold_cons ((map_decl (f (length _UU0393_0)) d),
        (map_decl (g (length _UU0393_')) d'), (mapi_context f _UU0393_0),
        (mapi_context g _UU0393_'), (f0 _UU0393_0 _UU0393_' a0), y)
    in f0 _UU0393_ _UU0394_ x),
    (let rec f0 l _UU0394_0 h =
       match l with
       | Coq_nil ->
         (match _UU0394_0 with
          | Coq_nil ->
            let h0 = (Coq_nil,Coq_nil),h in
            let h2 = let _,pr2 = h0 in pr2 in
            (match h2 with
             | All2_fold_nil -> All2_fold_nil
             | All2_fold_cons (_, _, _, _, _, _) ->
               assert false (* absurd case *))
          | Coq_cons (_, _) -> assert false (* absurd case *))
       | Coq_cons (y, l0) ->
         (match _UU0394_0 with
          | Coq_nil -> assert false (* absurd case *)
          | Coq_cons (c, l1) ->
            let h0 = ((Coq_cons ((map_decl (f (length l0)) y),
              (mapi_context f l0))),(Coq_cons ((map_decl (g (length l1)) c),
              (mapi_context g l1)))),h
            in
            let h2 = let _,pr2 = h0 in pr2 in
            (match h2 with
             | All2_fold_nil -> assert false (* absurd case *)
             | All2_fold_cons (_, _, _, _, a, p) ->
               All2_fold_cons (y, c, l0, l1, (f0 l0 l1 a), p)))
     in f0 _UU0393_ _UU0394_))

(** val coq_All2_fold_map :
    'a1 context_decl list -> 'a1 context_decl list -> ('a1 -> 'a1) -> ('a1 ->
    'a1) -> (('a1 context_decl, 'a2) coq_All2_fold, ('a1 context_decl, 'a2)
    coq_All2_fold) iffT **)

let coq_All2_fold_map _UU0393_ _UU0394_ f g =
  Coq_pair ((fun x ->
    let rec f0 _ _ = function
    | All2_fold_nil -> All2_fold_nil
    | All2_fold_cons (d, d', _UU0393_0, _UU0393_', a0, y) ->
      All2_fold_cons ((map_decl f d), (map_decl g d'),
        (map_context f _UU0393_0), (map_context g _UU0393_'),
        (f0 _UU0393_0 _UU0393_' a0), y)
    in f0 _UU0393_ _UU0394_ x),
    (let rec f0 l _UU0394_0 h =
       match l with
       | Coq_nil ->
         (match _UU0394_0 with
          | Coq_nil ->
            let h0 = (Coq_nil,Coq_nil),h in
            let h2 = let _,pr2 = h0 in pr2 in
            (match h2 with
             | All2_fold_nil -> All2_fold_nil
             | All2_fold_cons (_, _, _, _, _, _) ->
               assert false (* absurd case *))
          | Coq_cons (_, _) -> assert false (* absurd case *))
       | Coq_cons (y, l0) ->
         (match _UU0394_0 with
          | Coq_nil -> assert false (* absurd case *)
          | Coq_cons (c, l1) ->
            let h0 = ((Coq_cons ((map_decl f y),
              (map_context f l0))),(Coq_cons ((map_decl g c),
              (map_context g l1)))),h
            in
            let h2 = let _,pr2 = h0 in pr2 in
            (match h2 with
             | All2_fold_nil -> assert false (* absurd case *)
             | All2_fold_cons (_, _, _, _, a, p) ->
               All2_fold_cons (y, c, l0, l1, (f0 l0 l1 a), p)))
     in f0 _UU0393_ _UU0394_))

(** val coq_All2_fold_cst_map :
    'a1 context_decl list -> 'a1 context_decl list -> ('a1 context_decl ->
    'a1 context_decl) -> ('a1 context_decl -> 'a1 context_decl) -> (('a1
    context_decl, 'a2) coq_All2_fold, ('a1 context_decl, 'a2) coq_All2_fold)
    iffT **)

let coq_All2_fold_cst_map _UU0393_ _UU0394_ f g =
  Coq_pair ((fun x ->
    let rec f0 _ _ = function
    | All2_fold_nil -> All2_fold_nil
    | All2_fold_cons (d, d', _UU0393_0, _UU0393_', a0, y) ->
      All2_fold_cons ((f d), (g d'), (map f _UU0393_0), (map g _UU0393_'),
        (f0 _UU0393_0 _UU0393_' a0), y)
    in f0 _UU0393_ _UU0394_ x),
    (let rec f0 l _UU0394_0 h =
       match l with
       | Coq_nil ->
         (match _UU0394_0 with
          | Coq_nil ->
            let h0 = (Coq_nil,Coq_nil),h in
            let h2 = let _,pr2 = h0 in pr2 in
            (match h2 with
             | All2_fold_nil -> All2_fold_nil
             | All2_fold_cons (_, _, _, _, _, _) ->
               assert false (* absurd case *))
          | Coq_cons (_, _) -> assert false (* absurd case *))
       | Coq_cons (y, l0) ->
         (match _UU0394_0 with
          | Coq_nil -> assert false (* absurd case *)
          | Coq_cons (c, l1) ->
            let h0 = ((Coq_cons ((f y), (map f l0))),(Coq_cons ((g c),
              (map g l1)))),h
            in
            let h2 = let _,pr2 = h0 in pr2 in
            (match h2 with
             | All2_fold_nil -> assert false (* absurd case *)
             | All2_fold_cons (_, _, _, _, a, p) ->
               All2_fold_cons (y, c, l0, l1, (f0 l0 l1 a), p)))
     in f0 _UU0393_ _UU0394_))

(** val uint_size : nat **)

let uint_size =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val uint_wB : coq_Z **)

let uint_wB =
  Z.pow (Zpos (Coq_xO Coq_xH)) (Z.of_nat uint_size)

type uint63_model = coq_Z

(** val string_of_uint63_model : uint63_model -> String.t **)

let string_of_uint63_model =
  string_of_Z

(** val prec : coq_Z **)

let prec =
  Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))

(** val emax : coq_Z **)

let emax =
  Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO Coq_xH))))))))))

type float64_model = spec_float

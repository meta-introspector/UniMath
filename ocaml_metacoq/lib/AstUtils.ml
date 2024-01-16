open All_Forall
open Ast
open BasicAst
open Byte
open Datatypes
open Kernames
open List
open MCString
open Nat
open Primitive
open ReflectEq
open Universes
open Bytestring
open Monad_utils

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Coq_string_of_term_tree =
 struct
  (** val string_of_predicate :
      ('a1 -> Tree.t) -> 'a1 predicate -> Tree.t **)

  let string_of_predicate f p =
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28,
      String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x28, String.EmptyString))), (Tree.Coq_append
      ((Tree.concat (Tree.Coq_string (String.String (Coq_x2c,
         String.EmptyString))) (map f p.pparams)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x29, String.EmptyString))),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_universe_instance p.puinst)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, (String.String (Coq_x28,
      String.EmptyString))))), (Tree.Coq_append ((Tree.Coq_string
      (String.concat (String.String (Coq_x2c, String.EmptyString))
        (map
          (let f0 = fun b -> b.binder_name in fun x -> string_of_name (f0 x))
          p.pcontext))), (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x29, String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
      ((f p.preturn), (Tree.Coq_string (String.String (Coq_x29,
      String.EmptyString))))))))))))))))))))))))

  (** val string_of_branch : (term -> Tree.t) -> term branch -> Tree.t **)

  let string_of_branch f b =
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28, (String.String
      (Coq_x5b, String.EmptyString))))), (Tree.Coq_append ((Tree.Coq_string
      (String.concat (String.String (Coq_x2c, String.EmptyString))
        (map
          (let f0 = fun b0 -> b0.binder_name in fun x -> string_of_name (f0 x))
          b.bcontext))), (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x5d, (String.String (Coq_x2c, (String.String (Coq_x20,
      String.EmptyString))))))), (Tree.Coq_append ((f b.bbody),
      (Tree.Coq_string (String.String (Coq_x29, String.EmptyString))))))))))

  (** val string_of_def : ('a1 -> Tree.t) -> 'a1 def -> Tree.t **)

  let string_of_def f def0 =
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x28,
      String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_name def0.dname.binder_name)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append ((Tree.Coq_string
      (string_of_relevance def0.dname.binder_relevance)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append ((f def0.dtype), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
      ((f def0.dbody), (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x2c, String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_nat def0.rarg)), (Tree.Coq_string (String.String (Coq_x29,
      String.EmptyString))))))))))))))))))))))

  (** val string_of_term : term -> Tree.t **)

  let rec string_of_term = function
  | Coq_tRel n ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x52, (String.String
      (Coq_x65, (String.String (Coq_x6c, (String.String (Coq_x28,
      String.EmptyString))))))))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_nat n)), (Tree.Coq_string (String.String (Coq_x29,
      String.EmptyString))))))
  | Coq_tVar n ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x56, (String.String
      (Coq_x61, (String.String (Coq_x72, (String.String (Coq_x28,
      String.EmptyString))))))))), (Tree.Coq_append ((Tree.Coq_string n),
      (Tree.Coq_string (String.String (Coq_x29, String.EmptyString))))))
  | Coq_tEvar (ev, args) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x45, (String.String
      (Coq_x76, (String.String (Coq_x61, (String.String (Coq_x72,
      (String.String (Coq_x28, String.EmptyString))))))))))),
      (Tree.Coq_append ((Tree.Coq_string (string_of_nat ev)),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append
      ((Tree.string_of_list string_of_term args), (Tree.Coq_string
      (String.String (Coq_x29, String.EmptyString))))))))))
  | Coq_tSort s ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x53, (String.String
      (Coq_x6f, (String.String (Coq_x72, (String.String (Coq_x74,
      (String.String (Coq_x28, String.EmptyString))))))))))),
      (Tree.Coq_append ((Tree.Coq_string (string_of_sort s)),
      (Tree.Coq_string (String.String (Coq_x29, String.EmptyString))))))
  | Coq_tCast (c, _, t1) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x43, (String.String
      (Coq_x61, (String.String (Coq_x73, (String.String (Coq_x74,
      (String.String (Coq_x28, String.EmptyString))))))))))),
      (Tree.Coq_append ((string_of_term c), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append ((string_of_term t1), (Tree.Coq_string (String.String
      (Coq_x29, String.EmptyString))))))))))
  | Coq_tProd (na, b, t1) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x50, (String.String
      (Coq_x72, (String.String (Coq_x6f, (String.String (Coq_x64,
      (String.String (Coq_x28, String.EmptyString))))))))))),
      (Tree.Coq_append ((Tree.Coq_string (string_of_name na.binder_name)),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_relevance na.binder_relevance)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append ((string_of_term b), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append ((string_of_term t1), (Tree.Coq_string (String.String
      (Coq_x29, String.EmptyString))))))))))))))))))
  | Coq_tLambda (na, b, t1) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x4c, (String.String
      (Coq_x61, (String.String (Coq_x6d, (String.String (Coq_x62,
      (String.String (Coq_x64, (String.String (Coq_x61, (String.String
      (Coq_x28, String.EmptyString))))))))))))))), (Tree.Coq_append
      ((Tree.Coq_string (string_of_name na.binder_name)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append ((string_of_term b), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append ((Tree.Coq_string
      (string_of_relevance na.binder_relevance)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append ((string_of_term t1), (Tree.Coq_string (String.String
      (Coq_x29, String.EmptyString))))))))))))))))))
  | Coq_tLetIn (na, b, t', t1) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x4c, (String.String
      (Coq_x65, (String.String (Coq_x74, (String.String (Coq_x49,
      (String.String (Coq_x6e, (String.String (Coq_x28,
      String.EmptyString))))))))))))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_name na.binder_name)), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
      ((Tree.Coq_string (string_of_relevance na.binder_relevance)),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append ((string_of_term b),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append ((string_of_term t'),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append ((string_of_term t1),
      (Tree.Coq_string (String.String (Coq_x29,
      String.EmptyString))))))))))))))))))))))
  | Coq_tApp (f, l) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x41, (String.String
      (Coq_x70, (String.String (Coq_x70, (String.String (Coq_x28,
      String.EmptyString))))))))), (Tree.Coq_append ((string_of_term f),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append
      ((Tree.string_of_list string_of_term l), (Tree.Coq_string
      (String.String (Coq_x29, String.EmptyString))))))))))
  | Coq_tConst (c, u) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x43, (String.String
      (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x73,
      (String.String (Coq_x74, (String.String (Coq_x28,
      String.EmptyString))))))))))))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_kername c)), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
      ((Tree.Coq_string (string_of_universe_instance u)), (Tree.Coq_string
      (String.String (Coq_x29, String.EmptyString))))))))))
  | Coq_tInd (i, u) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x49, (String.String
      (Coq_x6e, (String.String (Coq_x64, (String.String (Coq_x28,
      String.EmptyString))))))))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_inductive i)), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
      ((Tree.Coq_string (string_of_universe_instance u)), (Tree.Coq_string
      (String.String (Coq_x29, String.EmptyString))))))))))
  | Coq_tConstruct (i, n, u) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x43, (String.String
      (Coq_x6f, (String.String (Coq_x6e, (String.String (Coq_x73,
      (String.String (Coq_x74, (String.String (Coq_x72, (String.String
      (Coq_x75, (String.String (Coq_x63, (String.String (Coq_x74,
      (String.String (Coq_x28, String.EmptyString))))))))))))))))))))),
      (Tree.Coq_append ((Tree.Coq_string (string_of_inductive i)),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_nat n)), (Tree.Coq_append ((Tree.Coq_string (String.String
      (Coq_x2c, String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_universe_instance u)), (Tree.Coq_string (String.String
      (Coq_x29, String.EmptyString))))))))))))))
  | Coq_tCase (ci, p, t1, brs) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x43, (String.String
      (Coq_x61, (String.String (Coq_x73, (String.String (Coq_x65,
      (String.String (Coq_x28, String.EmptyString))))))))))),
      (Tree.Coq_append ((Tree.Coq_string (string_of_case_info ci)),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append
      ((string_of_predicate string_of_term p), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append ((string_of_term t1), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append
      ((Tree.string_of_list (string_of_branch string_of_term) brs),
      (Tree.Coq_string (String.String (Coq_x29,
      String.EmptyString))))))))))))))))))
  | Coq_tProj (p, c) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x50, (String.String
      (Coq_x72, (String.String (Coq_x6f, (String.String (Coq_x6a,
      (String.String (Coq_x28, String.EmptyString))))))))))),
      (Tree.Coq_append ((Tree.Coq_string (string_of_inductive p.proj_ind)),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_nat p.proj_npars)), (Tree.Coq_append ((Tree.Coq_string
      (String.String (Coq_x2c, String.EmptyString))), (Tree.Coq_append
      ((Tree.Coq_string (string_of_nat p.proj_arg)), (Tree.Coq_append
      ((Tree.Coq_string (String.String (Coq_x2c, String.EmptyString))),
      (Tree.Coq_append ((string_of_term c), (Tree.Coq_string (String.String
      (Coq_x29, String.EmptyString))))))))))))))))))
  | Coq_tFix (l, n) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x46, (String.String
      (Coq_x69, (String.String (Coq_x78, (String.String (Coq_x28,
      String.EmptyString))))))))), (Tree.Coq_append
      ((Tree.string_of_list (string_of_def string_of_term) l),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_nat n)), (Tree.Coq_string (String.String (Coq_x29,
      String.EmptyString))))))))))
  | Coq_tCoFix (l, n) ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x43, (String.String
      (Coq_x6f, (String.String (Coq_x46, (String.String (Coq_x69,
      (String.String (Coq_x78, (String.String (Coq_x28,
      String.EmptyString))))))))))))), (Tree.Coq_append
      ((Tree.string_of_list (string_of_def string_of_term) l),
      (Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x2c,
      String.EmptyString))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_nat n)), (Tree.Coq_string (String.String (Coq_x29,
      String.EmptyString))))))))))
  | Coq_tInt i ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x49, (String.String
      (Coq_x6e, (String.String (Coq_x74, (String.String (Coq_x28,
      String.EmptyString))))))))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_prim_int i)), (Tree.Coq_string (String.String (Coq_x29,
      String.EmptyString))))))
  | Coq_tFloat f ->
    Tree.Coq_append ((Tree.Coq_string (String.String (Coq_x46, (String.String
      (Coq_x6c, (String.String (Coq_x6f, (String.String (Coq_x61,
      (String.String (Coq_x74, (String.String (Coq_x28,
      String.EmptyString))))))))))))), (Tree.Coq_append ((Tree.Coq_string
      (string_of_float f)), (Tree.Coq_string (String.String (Coq_x29,
      String.EmptyString))))))
 end

(** val string_of_term : term -> String.t **)

let string_of_term x =
  Tree.to_string (Coq_string_of_term_tree.string_of_term x)

(** val decompose_app : term -> (term, term list) prod **)

let decompose_app t0 = match t0 with
| Coq_tApp (f, l) -> Coq_pair (f, l)
| _ -> Coq_pair (t0, Coq_nil)

type mkApps_spec =
| Coq_mkApps_intro of term * term list * nat

(** val mkApps_spec_rect :
    (term -> term list -> nat -> __ -> 'a1) -> term -> term list -> term ->
    term list -> term -> mkApps_spec -> 'a1 **)

let mkApps_spec_rect f _ _ _ _ _ = function
| Coq_mkApps_intro (f0, l, n) -> f f0 l n __

(** val mkApps_spec_rec :
    (term -> term list -> nat -> __ -> 'a1) -> term -> term list -> term ->
    term list -> term -> mkApps_spec -> 'a1 **)

let mkApps_spec_rec f _ _ _ _ _ = function
| Coq_mkApps_intro (f0, l, n) -> f f0 l n __

(** val is_empty : 'a1 list -> bool **)

let is_empty = function
| Coq_nil -> Coq_true
| Coq_cons (_, _) -> Coq_false

(** val decompose_prod : term -> ((aname list, term list) prod, term) prod **)

let rec decompose_prod t0 = match t0 with
| Coq_tProd (n, a, b) ->
  let Coq_pair (nAs, b0) = decompose_prod b in
  let Coq_pair (ns, as0) = nAs in
  Coq_pair ((Coq_pair ((Coq_cons (n, ns)), (Coq_cons (a, as0)))), b0)
| _ -> Coq_pair ((Coq_pair (Coq_nil, Coq_nil)), t0)

(** val remove_arity : nat -> term -> term **)

let rec remove_arity n t0 =
  match n with
  | O -> t0
  | S n0 -> (match t0 with
             | Coq_tProd (_, _, b) -> remove_arity n0 b
             | _ -> t0)

(** val lookup_mind_decl :
    kername -> Env.global_declarations -> Env.mutual_inductive_body option **)

let rec lookup_mind_decl id0 = function
| Coq_nil -> None
| Coq_cons (p, tl) ->
  let Coq_pair (kn, g) = p in
  (match g with
   | Env.ConstantDecl _ -> lookup_mind_decl id0 tl
   | Env.InductiveDecl d ->
     (match eqb Kername.reflect_kername kn id0 with
      | Coq_true -> Some d
      | Coq_false -> lookup_mind_decl id0 tl))

(** val mind_body_to_entry :
    Env.mutual_inductive_body -> mutual_inductive_entry **)

let mind_body_to_entry decl =
  { mind_entry_record = None; mind_entry_finite = Finite; mind_entry_params =
    (match hd_error (Env.ind_bodies decl) with
     | Some i0 ->
       rev
         (let typ = decompose_prod (Env.ind_type i0) in
          let Coq_pair (p, _) = typ in
          let Coq_pair (l, l0) = p in
          let names = firstn (Env.ind_npars decl) l in
          let types = firstn (Env.ind_npars decl) l0 in
          map (fun pat -> let Coq_pair (x, ty) = pat in Env.vass x ty)
            (combine names types))
     | None -> Coq_nil); mind_entry_inds =
    (map (fun x ->
      let { Env.ind_name = ind_name0; Env.ind_indices = _; Env.ind_sort = _;
        Env.ind_type = ind_type0; Env.ind_kelim = _; Env.ind_ctors =
        ind_ctors0; Env.ind_projs = _; Env.ind_relevance = _ } = x
      in
      { mind_entry_typename = ind_name0; mind_entry_arity =
      (remove_arity (Env.ind_npars decl) ind_type0); mind_entry_consnames =
      (map Env.cstr_name ind_ctors0); mind_entry_lc =
      (map (fun x0 -> remove_arity (Env.ind_npars decl) (Env.cstr_type x0))
        ind_ctors0) }) (Env.ind_bodies decl)); mind_entry_universes =
    (universes_entry_of_decl (Env.ind_universes decl)); mind_entry_template =
    Coq_false; mind_entry_variance =
    (option_map (map (fun x -> Some x)) (Env.ind_variance decl));
    mind_entry_private = None }

(** val strip_casts : term -> term **)

let rec strip_casts t0 = match t0 with
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map strip_casts args))
| Coq_tCast (c, _, _) -> strip_casts c
| Coq_tProd (na, a, b) -> Coq_tProd (na, (strip_casts a), (strip_casts b))
| Coq_tLambda (na, t1, m) ->
  Coq_tLambda (na, (strip_casts t1), (strip_casts m))
| Coq_tLetIn (na, b, t1, b') ->
  Coq_tLetIn (na, (strip_casts b), (strip_casts t1), (strip_casts b'))
| Coq_tApp (u, v) -> mkApps (strip_casts u) (map strip_casts v)
| Coq_tCase (ind, p, c, brs) ->
  let p' = map_predicate (Obj.magic id) strip_casts strip_casts p in
  let brs' = map (map_branch strip_casts) brs in
  Coq_tCase (ind, p', (strip_casts c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (strip_casts c))
| Coq_tFix (mfix, idx) ->
  let mfix' = map (map_def strip_casts strip_casts) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' = map (map_def strip_casts strip_casts) mfix in
  Coq_tCoFix (mfix', idx)
| _ -> t0

(** val decompose_prod_assum :
    Env.context -> term -> (Env.context, term) prod **)

let rec decompose_prod_assum _UU0393_ t0 = match t0 with
| Coq_tProd (n, a, b) -> decompose_prod_assum (snoc _UU0393_ (Env.vass n a)) b
| Coq_tLetIn (na, b, bty, b') ->
  decompose_prod_assum (snoc _UU0393_ (Env.vdef na b bty)) b'
| _ -> Coq_pair (_UU0393_, t0)

(** val strip_outer_cast : term -> term **)

let rec strip_outer_cast t0 = match t0 with
| Coq_tCast (t1, _, _) -> strip_outer_cast t1
| _ -> t0

(** val decompose_prod_n_assum :
    Env.context -> nat -> term -> (Env.context, term) prod option **)

let rec decompose_prod_n_assum _UU0393_ n t0 =
  match n with
  | O -> Some (Coq_pair (_UU0393_, t0))
  | S n0 ->
    (match strip_outer_cast t0 with
     | Coq_tProd (na, a, b) ->
       decompose_prod_n_assum (snoc _UU0393_ (Env.vass na a)) n0 b
     | Coq_tLetIn (na, b, bty, b') ->
       decompose_prod_n_assum (snoc _UU0393_ (Env.vdef na b bty)) n0 b'
     | _ -> None)

(** val decompose_lam_n_assum :
    Env.context -> nat -> term -> (Env.context, term) prod option **)

let rec decompose_lam_n_assum _UU0393_ n t0 =
  match n with
  | O -> Some (Coq_pair (_UU0393_, t0))
  | S n0 ->
    (match strip_outer_cast t0 with
     | Coq_tLambda (na, a, b) ->
       decompose_lam_n_assum (snoc _UU0393_ (Env.vass na a)) n0 b
     | Coq_tLetIn (na, b, bty, b') ->
       decompose_lam_n_assum (snoc _UU0393_ (Env.vdef na b bty)) n0 b'
     | _ -> None)

(** val is_ind_app_head : term -> bool **)

let is_ind_app_head = function
| Coq_tApp (f, _) ->
  (match f with
   | Coq_tInd (_, _) -> Coq_true
   | _ -> Coq_false)
| Coq_tInd (_, _) -> Coq_true
| _ -> Coq_false

(** val isConstruct_app : term -> bool **)

let isConstruct_app t0 =
  match fst (decompose_app t0) with
  | Coq_tConstruct (_, _, _) -> Coq_true
  | _ -> Coq_false

(** val lookup_minductive :
    Env.global_env -> kername -> Env.mutual_inductive_body option **)

let lookup_minductive _UU03a3_ mind =
  match Env.lookup_env _UU03a3_ mind with
  | Some g ->
    (match g with
     | Env.ConstantDecl _ -> None
     | Env.InductiveDecl decl -> Some decl)
  | None -> None

(** val lookup_inductive :
    Env.global_env -> inductive -> (Env.mutual_inductive_body,
    Env.one_inductive_body) prod option **)

let lookup_inductive _UU03a3_ ind =
  match lookup_minductive _UU03a3_ ind.inductive_mind with
  | Some mdecl ->
    (match nth_error (Env.ind_bodies mdecl) ind.inductive_ind with
     | Some idecl -> Some (Coq_pair (mdecl, idecl))
     | None -> None)
  | None -> None

(** val destInd : term -> (inductive, Instance.t) prod option **)

let destInd = function
| Coq_tInd (ind, u) -> Some (Coq_pair (ind, u))
| _ -> None

(** val forget_types : 'a1 context_decl list -> aname list **)

let forget_types c =
  map (fun c0 -> c0.decl_name) c

(** val mkCase_old :
    Env.global_env -> case_info -> term -> term -> (nat, term) prod list ->
    term option **)

let mkCase_old _UU03a3_ ci p c brs =
  bind (Obj.magic option_monad)
    (Obj.magic lookup_inductive _UU03a3_ ci.ci_ind) (fun x ->
    let Coq_pair (mib, oib) = x in
    bind (Obj.magic option_monad)
      (Obj.magic decompose_lam_n_assum Coq_nil (S
        (length (Env.ind_indices oib))) p) (fun x0 ->
      let Coq_pair (pctx, preturn0) = x0 in
      bind (Obj.magic option_monad)
        (match pctx with
         | Coq_nil -> raise (Obj.magic option_monad_exc) Coq_tt
         | Coq_cons (y, indices) ->
           let { decl_name = _; decl_body = decl_body0; decl_type = tind } = y
           in
           (match decl_body0 with
            | Some _ -> raise (Obj.magic option_monad_exc) Coq_tt
            | None ->
              let Coq_pair (hd, args) = decompose_app tind in
              (match destInd hd with
               | Some p0 ->
                 let Coq_pair (_, u) = p0 in
                 ret (Obj.magic option_monad) (Coq_pair ((Coq_pair (u,
                   (firstn (Env.ind_npars mib) args))),
                   (forget_types indices)))
               | None -> raise (Obj.magic option_monad_exc) Coq_tt)))
        (fun x1 ->
        let Coq_pair (p0, pctx0) = x1 in
        let Coq_pair (puinst0, pparams0) = p0 in
        let p' = { puinst = puinst0; pparams = pparams0; pcontext = pctx0;
          preturn = preturn0 }
        in
        bind (Obj.magic option_monad)
          (monad_map2 (Obj.magic option_monad) (Obj.magic option_monad_exc)
            (fun cdecl br ->
            bind (Obj.magic option_monad)
              (Obj.magic decompose_lam_n_assum Coq_nil
                (length (Env.cstr_args cdecl)) (snd br)) (fun x2 ->
              let Coq_pair (bctx, bbody0) = x2 in
              ret (Obj.magic option_monad) { bcontext = (forget_types bctx);
                bbody = bbody0 })) Coq_tt (Env.ind_ctors oib) brs)
          (fun brs' ->
          ret (Obj.magic option_monad) (Coq_tCase (ci, p', c, brs'))))))

(** val default_sort_family : Universe.t -> allowed_eliminations **)

let default_sort_family u =
  match Universe.is_sprop u with
  | Coq_true -> IntoAny
  | Coq_false ->
    (match Universe.is_prop u with
     | Coq_true -> IntoPropSProp
     | Coq_false -> IntoAny)

(** val default_relevance : Universe.t -> relevance **)

let default_relevance u =
  match Universe.is_sprop u with
  | Coq_true -> Irrelevant
  | Coq_false -> Relevant

(** val make_constructor_body :
    ident -> nat -> Env.context -> Env.context -> term list ->
    Env.constructor_body **)

let make_constructor_body id0 indrel params args index_terms =
  { Env.cstr_name = id0; Env.cstr_args = args; Env.cstr_indices =
    index_terms; Env.cstr_type =
    (Env.it_mkProd_or_LetIn (Env.app_context params args)
      (mkApps (Coq_tRel (add (add (length args) (length params)) indrel))
        (app (Env.to_extended_list_k params (length args)) index_terms)));
    Env.cstr_arity = (Env.context_assumptions args) }

(** val make_inductive_body :
    ident -> Env.context -> Env.context -> Universe.t -> Env.constructor_body
    list -> Env.one_inductive_body **)

let make_inductive_body id0 params indices u ind_ctors0 =
  { Env.ind_name = id0; Env.ind_indices = indices; Env.ind_sort = u;
    Env.ind_type =
    (Env.it_mkProd_or_LetIn (Env.app_context params indices) (Coq_tSort u));
    Env.ind_kelim = (default_sort_family u); Env.ind_ctors = ind_ctors0;
    Env.ind_projs = Coq_nil; Env.ind_relevance = (default_relevance u) }

type ('a, 'p) tCaseBrsType = ('a branch, 'p) coq_All

type ('a, 'p, 'x) tFixType = ('a def, ('p, 'x) prod) coq_All

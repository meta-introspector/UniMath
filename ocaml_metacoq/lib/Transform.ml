open Byte
open Datatypes
open Bytestring

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val time : String.t -> ('a1 -> 'a2) -> 'a1 -> 'a2 **)

let time = (fun c f x -> let s = Caml_bytestring.caml_string_of_bytestring c in Tm_util.time (Pp.str s) f x)

module Transform =
 struct
  type ('env, 'term) program = ('env, 'term) prod

  type ('env, 'x1, 'term, 'x0, 'value, 'x) t = { name : String.t;
                                                 transform : (('env, 'term)
                                                             program -> __ ->
                                                             ('x1, 'x0)
                                                             program) }

  (** val name : ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) t -> String.t **)

  let name t0 =
    t0.name

  (** val transform :
      ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) t -> ('a1, 'a3) program -> ('a2, 'a4)
      program **)

  let transform t0 p =
    t0.transform p __

  (** val run :
      ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) t -> ('a1, 'a3) program -> ('a2, 'a4)
      program **)

  let run x p =
    time x.name (fun _ -> transform x p) Coq_tt

  type ('env, 'term) self_transform =
    ('env, 'env, 'term, 'term, 'term, 'term) t

  (** val compose :
      ('a1, 'a2, 'a4, 'a5, 'a7, 'a8) t -> ('a2, 'a3, 'a5, 'a6, 'a8, 'a9) t ->
      ('a1, 'a3, 'a4, 'a6, 'a7, 'a9) t **)

  let compose o o' =
    { name =
      (String.append o.name
        (String.append (String.String (Coq_x20, (String.String (Coq_x2d,
          (String.String (Coq_x3e, (String.String (Coq_x20,
          String.EmptyString)))))))) o'.name)); transform = (fun p _ ->
      run o' (run o p)) }
 end

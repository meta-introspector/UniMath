open Byte
open Datatypes
open Bytestring

type __ = Obj.t

val time : String.t -> ('a1 -> 'a2) -> 'a1 -> 'a2

module Transform :
 sig
  type ('env, 'term) program = ('env, 'term) prod

  type ('env, 'x1, 'term, 'x0, 'value, 'x) t = { name : String.t;
                                                 transform : (('env, 'term)
                                                             program -> __ ->
                                                             ('x1, 'x0)
                                                             program) }

  val name : ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) t -> String.t

  val transform :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) t -> ('a1, 'a3) program -> ('a2, 'a4)
    program

  val run :
    ('a1, 'a2, 'a3, 'a4, 'a5, 'a6) t -> ('a1, 'a3) program -> ('a2, 'a4)
    program

  type ('env, 'term) self_transform =
    ('env, 'env, 'term, 'term, 'term, 'term) t

  val compose :
    ('a1, 'a2, 'a4, 'a5, 'a7, 'a8) t -> ('a2, 'a3, 'a5, 'a6, 'a8, 'a9) t ->
    ('a1, 'a3, 'a4, 'a6, 'a7, 'a9) t
 end

open Datatypes
open Kernames
open ReflectEq

type __ = Obj.t

module EnvMap :
 sig
  type 'a t = 'a KernameMap.t

  val empty : 'a1 t

  val lookup : kername -> 'a1 t -> 'a1 option

  val add : kername -> 'a1 -> 'a1 t -> 'a1 t

  val remove : kername -> 'a1 t -> 'a1 t

  val fresh_globals_sig_pack :
    (kername, 'a1) prod list -> (kername, 'a1) prod list * __

  val fresh_globals_Signature :
    (kername, 'a1) prod list -> (kername, 'a1) prod list * __

  val of_global_env : (kername, 'a1) prod list -> 'a1 t

  val lookup_global : (kername, 'a1) prod list -> kername -> 'a1 option
 end

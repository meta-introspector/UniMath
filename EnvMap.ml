open Datatypes
open Kernames
open ReflectEq

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module EnvMap =
 struct
  type 'a t = 'a KernameMap.t

  (** val empty : 'a1 t **)

  let empty =
    KernameMap.empty

  (** val lookup : kername -> 'a1 t -> 'a1 option **)

  let lookup =
    KernameMap.find

  (** val add : kername -> 'a1 -> 'a1 t -> 'a1 t **)

  let add =
    KernameMap.add

  (** val remove : kername -> 'a1 t -> 'a1 t **)

  let remove =
    KernameMap.remove

  (** val fresh_globals_sig_pack :
      (kername, 'a1) prod list -> (kername, 'a1) prod list * __ **)

  let fresh_globals_sig_pack x =
    x,__

  (** val fresh_globals_Signature :
      (kername, 'a1) prod list -> (kername, 'a1) prod list * __ **)

  let fresh_globals_Signature x =
    x,__

  (** val of_global_env : (kername, 'a1) prod list -> 'a1 t **)

  let of_global_env =
    KernameMapFact.of_list

  (** val lookup_global :
      (kername, 'a1) prod list -> kername -> 'a1 option **)

  let rec lookup_global _UU03a3_ kn =
    match _UU03a3_ with
    | Coq_nil -> None
    | Coq_cons (d, tl) ->
      (match eqb Kername.reflect_kername kn (fst d) with
       | Coq_true -> Some (snd d)
       | Coq_false -> lookup_global tl kn)
 end

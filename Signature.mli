
type ('fam, 'signature_index, 'signature) coq_Signature =
  'fam -> 'signature_index * 'signature

val signature_pack : ('a1, 'a2, 'a3) coq_Signature -> 'a1 -> 'a2 * 'a3

type ('fam, 'index, 'sig0) signature = 'sig0

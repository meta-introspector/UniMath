open PartA
open PartA0
open PartB
open Preamble

type __ = Obj.t

type ('x, 'y) coq_PathOver = __

val coq_PathOverToPathPair :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathPair

val apd : ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a1 paths -> ('a1, 'a2) coq_PathOver

val coq_PathOverToTotalPath :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) total2 paths

val coq_PathOverUniqueness :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a2, ('a1, 'a2) coq_PathOver) total2
  iscontr

val stdPathOver : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) coq_PathOver

val stdPathOver' : 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) coq_PathOver

val identityPathOver : 'a1 -> 'a2 -> ('a1, 'a2) coq_PathOver

val pathOverIdpath : 'a1 -> 'a2 -> 'a2 -> __ paths

val toPathOverIdpath :
  'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) coq_PathOver

val fromPathOverIdpath :
  'a1 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> 'a2 paths

val inductionPathOver :
  'a1 -> 'a2 -> 'a3 -> 'a1 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver ->
  'a3

val transportPathOver :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> 'a3 ->
  'a3

val transportPathOver' :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> 'a3 ->
  'a3

val composePathOver :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1,
  'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver

val composePathOverPath :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver ->
  'a2 paths -> ('a1, 'a2) coq_PathOver

val composePathOverIdpath :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val composePathPathOver :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
  coq_PathOver -> ('a1, 'a2) coq_PathOver

val composeIdpathPathOver :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val composePathPathOverRotate :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 -> ('a1, 'a2)
  coq_PathOver -> ('a1, 'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver paths,
  ('a1, 'a2) coq_PathOver paths) logeq

val composePathOverPathRotate :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver ->
  'a2 paths -> ('a1, 'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver paths,
  ('a1, 'a2) coq_PathOver paths) logeq

val composePathPathOverPath :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1,
  'a2) coq_PathOver -> 'a2 paths -> ('a1, 'a2) coq_PathOver paths

val composePathOverLeftUnit :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val composePathOverRightUnit :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val assocPathOver :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a2 ->
  'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val inversePathOver :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver

val inversePathOver' :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver

val inverseInversePathOver1 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val inverseInversePathOver2 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val inversePathOverIdpath :
  'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) coq_PathOver paths

val inversePathOverIdpath' :
  'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2) coq_PathOver paths

val inverseInversePathOver :
  'a1 -> 'a2 -> 'a1 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val inversePathOverWeq :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> (('a1, 'a2) coq_PathOver, ('a1,
  'a2) coq_PathOver) weq

val inversePathOverWeq' :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> (('a1, 'a2) coq_PathOver, ('a1,
  'a2) coq_PathOver) weq

val coq_PathOverConstant_id :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> coq_UU paths

val coq_PathOverConstant_map1 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
  coq_PathOver

val coq_PathOverConstant_map1_eq1 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths ->
  ('a1, 'a2) coq_PathOver paths

val coq_PathOverConstant_map1_eq2 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths ->
  ('a1, 'a2) coq_PathOver paths

val coq_PathOverConstant_map2 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> 'a2
  paths

val coq_PathOverConstant_map2_apd :
  'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2) -> 'a2 paths paths

val coq_PathOverConstant_map2_eq1 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver ->
  'a2 paths -> 'a2 paths paths

val coq_PathOverConstant_map2_eq2 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
  coq_PathOver -> 'a2 paths paths

val coq_PathOverConstant_map1_map2 :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths paths

val coq_Lemma023 :
  'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> ('a1,
  'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver)
  isweq

val composePathOver_weq :
  'a1 -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> ('a1,
  'a2) coq_PathOver -> (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver) weq

val coq_Lemma0_2_4 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver) isweq

val cp :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
  (('a1, 'a2) coq_PathOver, ('a1, 'a2) coq_PathOver) weq

val composePathOverPath_compute :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver ->
  'a2 paths -> ('a1, 'a2) coq_PathOver paths

val composePathPathOver_compute :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
  coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val cp_idpath :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val cp_left :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
  'a2 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2)
  coq_PathOver paths

val cp_right :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
  'a2 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2)
  coq_PathOver paths

val cp_in_family :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> ('a2 -> 'a1 paths) -> 'a3 -> 'a3
  -> ('a2 -> ('a1, 'a3) coq_PathOver) -> ('a1, 'a3) coq_PathOver paths

val cp_irrelevance :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  'a1 paths paths -> 'a1 isofhlevel -> (('a1, 'a2) coq_PathOver, ('a1, 'a2)
  coq_PathOver) weq paths

val coq_Unnamed_thm :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> coq_UU paths

val inverse_cp_p :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val inverse_cp_p' :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1 paths, ('a1,
  'a2) coq_PathOver) coq_PathOver -> ('a1 paths, ('a1, 'a2) coq_PathOver)
  coq_PathOver

val inverse_cp_p'' :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1 paths, ('a1,
  'a2) coq_PathOver) coq_PathOver -> ('a1 paths, ('a1, 'a2) coq_PathOver)
  coq_PathOver

val inverse_cp_p_compare :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1 paths, ('a1,
  'a2) coq_PathOver) coq_PathOver -> ('a1 paths, ('a1, 'a2) coq_PathOver)
  coq_PathOver paths

val cp_inverse_cp :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val composePathOverRightInverse :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val composePathOverLeftInverse :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> ('a1, 'a2) coq_PathOver -> ('a1,
  'a2) coq_PathOver paths

val cp_pathscomp0 :
  'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1
  paths paths -> 'a1 paths paths -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2)
  coq_PathOver paths

val apstar :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths ->
  'a1 paths paths -> 'a1 paths paths -> 'a1 paths paths

val cp_apstar :
  'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> 'a1 paths ->
  'a1 paths paths -> 'a1 paths paths -> 'a2 -> 'a2 -> 'a2 -> ('a1, 'a2)
  coq_PathOver -> ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val cp_apstar' :
  'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths paths -> 'a2 -> 'a2 ->
  ('a1, 'a2) coq_PathOver -> ('a1, 'a2) coq_PathOver paths

val pathOverEquations :
  ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 paths -> 'a2 paths -> 'a1
  paths -> __ paths

val pathOverEquations1 :
  ('a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 paths -> 'a1 paths -> 'a1 paths -> __
  paths

val mapPathOver :
  'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a2 -> ('a1, 'a2)
  coq_PathOver -> ('a1, 'a3) coq_PathOver

val binopPathOver :
  'a1 -> 'a1 -> 'a1 paths -> ('a1 -> 'a2 -> 'a3 -> 'a4) -> 'a2 -> 'a2 -> 'a3
  -> 'a3 -> ('a1, 'a2) coq_PathOver -> ('a1, 'a3) coq_PathOver -> ('a1, 'a4)
  coq_PathOver

type ('x, 'x0, 'y) pullBackFamily = 'y

val pullBackSection : ('a1 -> 'a2) -> ('a2 -> 'a3) -> 'a1 -> 'a3

val pullBackPointOver :
  ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> ('a1, 'a2, 'a3)
  pullBackFamily

val pullBackPointOverWithSection :
  ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> ('a2 -> 'a3) -> ('a1, 'a2, 'a3)
  pullBackFamily paths

val pullBackPointOverWithSection' :
  ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> ('a2 -> 'a3) -> 'a3 paths
  -> ('a1, 'a2, 'a3) pullBackFamily paths

val pullBackPathOverPoint :
  ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a2 paths -> 'a3 -> 'a3 -> 'a3 paths -> ('a1,
  'a2, 'a3) pullBackFamily paths

val pullBackPathOver :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths -> 'a1
  paths -> 'a2 paths -> 'a2 paths paths -> 'a3 -> 'a3 -> ('a2, 'a3)
  coq_PathOver -> ('a1, ('a1, 'a2, 'a3) pullBackFamily) coq_PathOver

val pullBackPathOverPath :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths -> 'a1
  paths -> 'a2 paths -> 'a2 paths paths -> 'a3 -> 'a3 -> 'a3 -> ('a2, 'a3)
  coq_PathOver -> 'a3 paths -> ('a1, ('a1, 'a2, 'a3) pullBackFamily)
  coq_PathOver paths

val pullBackPathPathOver :
  ('a1 -> 'a2) -> 'a1 -> 'a1 -> 'a2 -> 'a2 -> 'a2 paths -> 'a2 paths -> 'a1
  paths -> 'a2 paths -> 'a2 paths paths -> 'a3 -> 'a3 -> 'a3 -> ('a2, 'a3)
  coq_PathOver -> 'a3 paths -> ('a1, ('a1, 'a2, 'a3) pullBackFamily)
  coq_PathOver paths

val transportf_to_pathover :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> 'a2 paths -> ('a1, 'a2)
  coq_PathOver

val isweq_transportf_to_pathover :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a2 paths, ('a1, 'a2)
  coq_PathOver) isweq

val transportf_weq_pathover :
  'a1 -> 'a1 -> 'a1 paths -> 'a2 -> 'a2 -> ('a2 paths, ('a1, 'a2)
  coq_PathOver) weq

module PathsOverNotations :
 sig
 end

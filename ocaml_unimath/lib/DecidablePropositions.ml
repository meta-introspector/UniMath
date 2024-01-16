open PartA
open PartB
open Preamble

(** val retract_dec :
    ('a1 -> 'a2) -> ('a2 -> 'a1) -> ('a2, 'a2) homot -> 'a1 isdeceq -> 'a2
    isdeceq **)

let retract_dec f g h i y y' =
  let d = i (g y) (g y') in
  (match d with
   | Coq_ii1 a ->
     Coq_ii1
       (pathscomp0 (idfun y) (funcomp g f y) (idfun y')
         (pathsinv0 (funcomp g f y) (idfun y) (h y))
         (pathscomp0 (f (g y)) (f (g y')) (idfun y')
           (maponpaths f (g y) (g y') a) (h y')))
   | Coq_ii2 b -> Coq_ii2 (fun p -> b (maponpaths g y y' p)))

(** val logeq_dec : ('a1, 'a2) logeq -> 'a1 decidable -> 'a2 decidable **)

let logeq_dec iff decX =
  let xtoY = iff.pr1 in
  let ytoX = iff.pr2 in
  (match decX with
   | Coq_ii1 a -> Coq_ii1 (xtoY a)
   | Coq_ii2 b -> Coq_ii2 (negf ytoX b))

open PartA
open Preamble

(** val total2_paths_equiv' :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths, ('a1,
    'a2) coq_PathPair) weq **)

let total2_paths_equiv' x y =
  weqtotaltofib (fun z p -> { pr1 = (maponpaths (fun t -> t.pr1) x z p);
    pr2 = Coq_paths_refl })
    (isweqcontrcontr
      (totalfun (fun z p -> { pr1 = (maponpaths (fun t -> t.pr1) x z p);
        pr2 = Coq_paths_refl })) (iscontrcoconusfromt x) { pr1 = { pr1 = x;
      pr2 = { pr1 = Coq_paths_refl; pr2 = Coq_paths_refl } }; pr2 = (fun _ ->
      Coq_paths_refl) }) y

(** val total2_paths_equiv'_compute :
    ('a1, 'a2) total2 -> ('a1, 'a2) total2 -> (('a1, 'a2) total2 paths ->
    ('a1, 'a2) coq_PathPair) paths **)

let total2_paths_equiv'_compute _ _ =
  Coq_paths_refl

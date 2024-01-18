open NaturalNumbers
open PartA
open PartD
open Preamble
open Propositions
open Propositions0
open Univalence
open UnivalenceAxiom

type __ = Obj.t

type ('x, 'lt, 'p) hereditary = 'x -> ('x -> 'lt -> 'p) -> 'p

type ('x, 'lt) strongly_well_founded =
  __ -> ('x, 'lt, __) hereditary -> ('x -> __, 'x -> __ paths) total2

type ('x, 'lt) weakly_well_founded =
  ('x -> hProp) -> ('x, 'lt, hProptoType) hereditary -> 'x -> hProptoType

type ('x, 'lt) chain = __

type ('x, 'lt) le = (nat, ('x, 'lt) chain) total2

(** val nil : 'a1 -> ('a1, 'a2) le **)

let nil _ =
  { pr1 = O; pr2 = (Obj.magic Coq_paths_refl) }

(** val cons' :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> ('a1, 'a2) le -> 'a2 -> 'a1 paths -> ('a1,
    'a2) le **)

let cons' _ x' y _ p l e =
  let n = p.pr1 in
  let c = p.pr2 in
  { pr1 = (S n); pr2 =
  (Obj.magic { pr1 = y; pr2 = { pr1 = x'; pr2 = { pr1 = c; pr2 = { pr1 = l;
    pr2 = e } } } }) }

(** val cons1 :
    nat -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) chain
    -> ('a1, 'a2) chain **)

let rec cons1 n y z z' _ e l c =
  match n with
  | O ->
    Obj.magic { pr1 = z'; pr2 = { pr1 = y; pr2 = { pr1 = e; pr2 = { pr1 = l;
      pr2 = c } } } }
  | S n0 ->
    let s = (Obj.magic c).pr1 in
    let pr3 = (Obj.magic c).pr2 in
    let t = pr3.pr1 in
    let pr4 = pr3.pr2 in
    let c' = pr4.pr1 in
    let pr5 = pr4.pr2 in
    let l' = pr5.pr1 in
    let e' = pr5.pr2 in
    Obj.magic { pr1 = s; pr2 = { pr1 = t; pr2 = { pr1 =
      (cons1 n0 y z z' s e l c'); pr2 = { pr1 = l'; pr2 = e' } } } }

(** val cons :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2) le -> ('a1,
    'a2) le **)

let cons x y z z' e l p =
  let n = p.pr1 in
  let c = p.pr2 in { pr1 = (S n); pr2 = (cons1 n y z z' x e l c) }

(** val coq_Unnamed_thm :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 paths -> 'a2 -> ('a1, 'a2)
    le -> 'a2 -> 'a1 paths -> ('a1, 'a2) le paths **)

let coq_Unnamed_thm _ _ _ _ _ _ _ _ _ _ _ =
  Coq_paths_refl

type ('x, 'lt, 'p) guided_by = 'x -> ('x, 'lt) le -> 'p paths

type ('x, 'lt, 'p) attempt =
  ('x -> ('x, 'lt) le -> 'p, ('x, 'lt, 'p) guided_by) total2

(** val attempt_fun :
    ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> 'a1 ->
    ('a1, 'a2) le -> 'a3 **)

let attempt_fun _ _ t =
  t.pr1

(** val attempt_comp :
    ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1,
    'a2, 'a3) guided_by **)

let attempt_comp _ _ t =
  t.pr2

(** val disassemble_attempt :
    ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> 'a1 ->
    'a1 -> 'a2 -> 'a1 paths -> ('a1, 'a2, 'a3) attempt **)

let disassemble_attempt h x f y' y l e =
  { pr1 = (fun t p -> attempt_fun h x f t (cons' x y y' t p l e)); pr2 =
    (fun z p -> attempt_comp h x f z (cons' x y y' z p l e)) }

(** val assemble_attempt :
    ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1 -> 'a1 -> 'a2 -> 'a1 paths ->
    ('a1, 'a2, 'a3) attempt) -> ('a1, 'a2, 'a3) attempt **)

let assemble_attempt h _ fs =
  { pr1 = (fun y x0 ->
    let pr3 = x0.pr1 in
    let c = x0.pr2 in
    (match pr3 with
     | O ->
       h y (fun z lzy -> attempt_fun h z (Obj.magic fs z y lzy c) z (nil z))
     | S n ->
       let s = (Obj.magic c).pr1 in
       let pr4 = (Obj.magic c).pr2 in
       let t = pr4.pr1 in
       let pr5 = pr4.pr2 in
       let c' = pr5.pr1 in
       let pr6 = pr5.pr2 in
       let l' = pr6.pr1 in
       let e' = pr6.pr2 in
       attempt_fun h s (fs s t l' e') y { pr1 = n; pr2 = c' })); pr2 =
    (fun y pyx ->
    let pr3 = pyx.pr1 in
    let c = pyx.pr2 in
    (match pr3 with
     | O -> Coq_paths_refl
     | S n ->
       attempt_comp h (Obj.magic c).pr1
         (fs (Obj.magic c).pr1 (Obj.magic c).pr2.pr1
           (Obj.magic c).pr2.pr2.pr2.pr1 (Obj.magic c).pr2.pr2.pr2.pr2) y
         { pr1 = n; pr2 = (Obj.magic c).pr2.pr2.pr1 })) }

(** val attempt_lemma :
    ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1,
    'a2, 'a3) attempt -> (('a1 -> ('a1, 'a2) le -> 'a3) paths -> 'a4) -> ('a1
    -> ('a1, 'a2) le -> 'a3 paths) -> 'a4 **)

let attempt_lemma h x f g hT e =
  transportf (fun y ->
    Obj.magic (fun pyx ->
      eqtohomot (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
        (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y)
        (eqtohomot (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f))
          (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g))
          (Obj.magic funextsec
            (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f))
            (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g))
            (fun y0 ->
            Obj.magic funextsec
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y0)
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y0)
              (Obj.magic e y0))) y) pyx)) (Obj.magic e)
    (funextsec (fun y ->
      Obj.magic (fun pyx ->
        eqtohomot (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
          (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y)
          (eqtohomot (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f))
            (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g))
            (Obj.magic funextsec
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f))
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g))
              (fun y0 ->
              Obj.magic funextsec
                (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y0)
                (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y0)
                (Obj.magic e y0))) y) pyx)) (Obj.magic e) (fun y ->
      Obj.magic funextsec (fun pyx ->
        Obj.magic eqtohomot
          (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
          (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y)
          (eqtohomot (Obj.magic attempt_fun h x f)
            (Obj.magic attempt_fun h x g)
            (Obj.magic funextsec
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f))
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g))
              (fun y0 ->
              Obj.magic funextsec
                (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y0)
                (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y0)
                (Obj.magic e y0))) y) pyx) (Obj.magic e y) (fun pyx ->
        pathscomp0
          (Obj.magic eqtohomot
            (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
            (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y)
            (eqtohomot (Obj.magic attempt_fun h x f)
              (Obj.magic attempt_fun h x g)
              (Obj.magic funextsec
                (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f))
                (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g))
                (fun y0 ->
                Obj.magic funextsec
                  (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y0)
                  (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y0)
                  (Obj.magic e y0))) y) pyx)
          (Obj.magic eqtohomot
            (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
            (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y)
            (funextsec (Obj.magic attempt_fun h x f y)
              (Obj.magic attempt_fun h x g y) (Obj.magic e y)) pyx)
          (Obj.magic e y pyx)
          (eqtohomot
            (Obj.magic eqtohomot
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y)
              (eqtohomot (Obj.magic attempt_fun h x f)
                (Obj.magic attempt_fun h x g)
                (Obj.magic funextsec
                  (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f))
                  (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g))
                  (fun y0 ->
                  Obj.magic funextsec
                    (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y0)
                    (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y0)
                    (Obj.magic e y0))) y))
            (Obj.magic eqtohomot
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y)
              (funextsec (Obj.magic attempt_fun h x f y)
                (Obj.magic attempt_fun h x g y) (Obj.magic e y)))
            (maponpaths
              (Obj.magic eqtohomot
                (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
                (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y))
              (eqtohomot (Obj.magic attempt_fun h x f)
                (Obj.magic attempt_fun h x g)
                (Obj.magic funextsec
                  (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f))
                  (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g))
                  (fun y0 ->
                  Obj.magic funextsec
                    (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y0)
                    (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y0)
                    (Obj.magic e y0))) y)
              (funextsec (Obj.magic attempt_fun h x f y)
                (Obj.magic attempt_fun h x g y) (Obj.magic e y))
              (eqtohomot
                (eqtohomot (Obj.magic attempt_fun h x f)
                  (Obj.magic attempt_fun h x g)
                  (Obj.magic funextsec
                    (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f))
                    (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g))
                    (fun y0 ->
                    Obj.magic funextsec
                      (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f)
                        y0)
                      (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g)
                        y0) (Obj.magic e y0)))) (fun y0 ->
                funextsec (Obj.magic attempt_fun h x f y0)
                  (Obj.magic attempt_fun h x g y0) (Obj.magic e y0))
                (toforallpaths_funextsec (Obj.magic attempt_fun h x f)
                  (Obj.magic attempt_fun h x g) (fun y0 ->
                  funextsec (Obj.magic attempt_fun h x f y0)
                    (Obj.magic attempt_fun h x g y0) (Obj.magic e y0))) y))
            pyx)
          (eqtohomot
            (Obj.magic eqtohomot
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y)
              (funextsec (Obj.magic attempt_fun h x f y)
                (Obj.magic attempt_fun h x g y) (Obj.magic e y)))
            (Obj.magic e y)
            (Obj.magic toforallpaths_funextsec
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
              (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y)
              (Obj.magic e y)) pyx))))
    (Obj.magic hT
      (funextsec (Obj.magic attempt_fun h x f) (Obj.magic attempt_fun h x g)
        (fun y ->
        Obj.magic funextsec
          (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) y)
          (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic g) y)
          (Obj.magic e y))))

(** val attempt_paths :
    ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1,
    'a2, 'a3) attempt -> ('a1 -> ('a1, 'a2) le -> 'a3 paths) -> ('a1 -> ('a1,
    'a2) le -> 'a3 paths paths) -> ('a1, 'a2, 'a3) attempt paths **)

let attempt_paths h x f g =
  attempt_lemma h x f g (fun _ ->
    let f0 = f.pr1 in
    let f1 = f.pr2 in
    let g1 = g.pr2 in
    (fun e_comp ->
    maponpaths (Obj.magic (fun x0 -> { pr1 = f0; pr2 = x0 })) (Obj.magic f1)
      (Obj.magic g1)
      (funextsec (Obj.magic f1) (Obj.magic g1) (fun y ->
        Obj.magic funextsec (Obj.magic f1 y) (Obj.magic g1 y) (fun pyx ->
          pathscomp0 (Obj.magic f1 y pyx)
            (Obj.magic pathscomp0 (Obj.magic f0 y pyx)
              (Obj.magic h y (fun z l ->
                Obj.magic f0 z
                  (cons (Obj.magic x) y z z Coq_paths_refl l (Obj.magic pyx))))
              (Obj.magic h y (fun z lzy ->
                Obj.magic f0 z
                  (cons (Obj.magic x) y z z Coq_paths_refl lzy
                    (Obj.magic pyx)))) (Obj.magic f1 y pyx)
              (maponpaths (Obj.magic h y) (fun z ->
                Obj.magic (fun lzy ->
                  Obj.magic f0 z
                    (cons (Obj.magic x) y z z Coq_paths_refl lzy
                      (Obj.magic pyx)))) (fun z ->
                Obj.magic (fun lzy ->
                  Obj.magic f0 z
                    (cons (Obj.magic x) y z z Coq_paths_refl lzy
                      (Obj.magic pyx))))
                (funextsec (fun z ->
                  Obj.magic (fun lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx)))) (fun z ->
                  Obj.magic (fun lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx)))) (fun z ->
                  Obj.magic funextsec (fun lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx))) (fun lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx))) (fun _ -> Coq_paths_refl)))))
            (Obj.magic g1 y pyx)
            (pathsinv0
              (Obj.magic pathscomp0 (Obj.magic f0 y pyx)
                (Obj.magic h y (fun z l ->
                  Obj.magic f0 z
                    (cons (Obj.magic x) y z z Coq_paths_refl l
                      (Obj.magic pyx))))
                (Obj.magic h y (fun z lzy ->
                  Obj.magic f0 z
                    (cons (Obj.magic x) y z z Coq_paths_refl lzy
                      (Obj.magic pyx)))) (Obj.magic f1 y pyx)
                (maponpaths (Obj.magic h y) (fun z ->
                  Obj.magic (fun lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx)))) (fun z ->
                  Obj.magic (fun lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx))))
                  (funextsec (fun z ->
                    Obj.magic (fun lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx)))) (fun z ->
                    Obj.magic (fun lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx)))) (fun z ->
                    Obj.magic funextsec (fun lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx))) (fun lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx))) (fun _ -> Coq_paths_refl)))))
              (Obj.magic f1 y pyx)
              (pathscomp0
                (Obj.magic pathscomp0 (Obj.magic f0 y pyx)
                  (Obj.magic h y (fun z lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx))))
                  (Obj.magic h y (fun z lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx)))) (Obj.magic f1 y pyx)
                  (maponpaths (Obj.magic h y) (fun z ->
                    Obj.magic (fun lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx)))) (fun z ->
                    Obj.magic (fun lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx))))
                    (funextsec (fun z ->
                      Obj.magic (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx)))) (fun z ->
                      Obj.magic (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx)))) (fun z ->
                      Obj.magic funextsec (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx))) (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx))) (fun _ -> Coq_paths_refl)))))
                (Obj.magic pathscomp0 (Obj.magic f0 y pyx)
                  (Obj.magic h y (fun z lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx))))
                  (Obj.magic h y (fun z lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx)))) (Obj.magic f1 y pyx)
                  Coq_paths_refl) (Obj.magic f1 y pyx)
                (maponpaths
                  (Obj.magic pathscomp0 (Obj.magic f0 y pyx)
                    (Obj.magic h y (fun z lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx))))
                    (Obj.magic h y (fun z lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx)))) (Obj.magic f1 y pyx))
                  (maponpaths (Obj.magic h y) (fun z ->
                    Obj.magic (fun lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx)))) (fun z ->
                    Obj.magic (fun lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx))))
                    (funextsec (fun z ->
                      Obj.magic (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx)))) (fun z ->
                      Obj.magic (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx)))) (fun z ->
                      Obj.magic funextsec (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx))) (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx))) (fun _ -> Coq_paths_refl))))
                  Coq_paths_refl
                  (maponpaths
                    (maponpaths (Obj.magic h y) (fun z lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx))) (fun z lzy ->
                      Obj.magic f0 z
                        (cons (Obj.magic x) y z z Coq_paths_refl lzy
                          (Obj.magic pyx))))
                    (Obj.magic funextsec (fun z ->
                      Obj.magic (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx)))) (fun z ->
                      Obj.magic (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx)))) (fun z ->
                      Obj.magic funextsec (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx))) (fun lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx))) (fun _ -> Coq_paths_refl)))
                    Coq_paths_refl
                    (pathscomp0
                      (Obj.magic funextsec (fun z ->
                        Obj.magic (fun lzy ->
                          Obj.magic f0 z
                            (cons (Obj.magic x) y z z Coq_paths_refl lzy
                              (Obj.magic pyx)))) (fun z ->
                        Obj.magic (fun lzy ->
                          Obj.magic f0 z
                            (cons (Obj.magic x) y z z Coq_paths_refl lzy
                              (Obj.magic pyx)))) (fun z ->
                        Obj.magic funextsec (fun lzy ->
                          Obj.magic f0 z
                            (cons (Obj.magic x) y z z Coq_paths_refl lzy
                              (Obj.magic pyx))) (fun lzy ->
                          Obj.magic f0 z
                            (cons (Obj.magic x) y z z Coq_paths_refl lzy
                              (Obj.magic pyx))) (fun _ -> Coq_paths_refl)))
                      (Obj.magic funextsec (fun z ->
                        Obj.magic (fun lzy ->
                          Obj.magic f0 z
                            (cons (Obj.magic x) y z z Coq_paths_refl lzy
                              (Obj.magic pyx)))) (fun z ->
                        Obj.magic (fun lzy ->
                          Obj.magic f0 z
                            (cons (Obj.magic x) y z z Coq_paths_refl lzy
                              (Obj.magic pyx))))
                        (toforallpaths (fun z ->
                          Obj.magic (fun lzy ->
                            Obj.magic f0 z
                              (cons (Obj.magic x) y z z Coq_paths_refl lzy
                                (Obj.magic pyx)))) (fun z ->
                          Obj.magic (fun lzy ->
                            Obj.magic f0 z
                              (cons (Obj.magic x) y z z Coq_paths_refl lzy
                                (Obj.magic pyx)))) Coq_paths_refl))
                      Coq_paths_refl
                      (maponpaths
                        (Obj.magic funextsec (fun z ->
                          Obj.magic (fun lzy ->
                            Obj.magic f0 z
                              (cons (Obj.magic x) y z z Coq_paths_refl lzy
                                (Obj.magic pyx)))) (fun z ->
                          Obj.magic (fun lzy ->
                            Obj.magic f0 z
                              (cons (Obj.magic x) y z z Coq_paths_refl lzy
                                (Obj.magic pyx))))) (fun z ->
                        Obj.magic funextsec (fun lzy ->
                          Obj.magic f0 z
                            (cons (Obj.magic x) y z z Coq_paths_refl lzy
                              (Obj.magic pyx))) (fun lzy ->
                          Obj.magic f0 z
                            (cons (Obj.magic x) y z z Coq_paths_refl lzy
                              (Obj.magic pyx))) (fun _ -> Coq_paths_refl))
                        (Obj.magic toforallpaths (fun z lzy ->
                          Obj.magic f0 z
                            (cons (Obj.magic x) y z z Coq_paths_refl lzy
                              (Obj.magic pyx))) (fun z lzy ->
                          Obj.magic f0 z
                            (cons (Obj.magic x) y z z Coq_paths_refl lzy
                              (Obj.magic pyx))) Coq_paths_refl)
                        (funextsec (fun z ->
                          Obj.magic funextsec (fun lzy ->
                            Obj.magic f0 z
                              (cons (Obj.magic x) y z z Coq_paths_refl lzy
                                (Obj.magic pyx))) (fun lzy ->
                            Obj.magic f0 z
                              (cons (Obj.magic x) y z z Coq_paths_refl lzy
                                (Obj.magic pyx))) (fun _ -> Coq_paths_refl))
                          (Obj.magic toforallpaths (fun z lzy ->
                            Obj.magic f0 z
                              (cons (Obj.magic x) y z z Coq_paths_refl lzy
                                (Obj.magic pyx))) (fun z lzy ->
                            Obj.magic f0 z
                              (cons (Obj.magic x) y z z Coq_paths_refl lzy
                                (Obj.magic pyx))) Coq_paths_refl) (fun z ->
                          Obj.magic funextsec_toforallpaths (fun lzy ->
                            Obj.magic f0 z
                              (cons (Obj.magic x) y z z Coq_paths_refl lzy
                                (Obj.magic pyx))) (fun lzy ->
                            Obj.magic f0 z
                              (cons (Obj.magic x) y z z Coq_paths_refl lzy
                                (Obj.magic pyx))) Coq_paths_refl)))
                      (funextsec_toforallpaths (fun z lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx))) (fun z lzy ->
                        Obj.magic f0 z
                          (cons (Obj.magic x) y z z Coq_paths_refl lzy
                            (Obj.magic pyx))) Coq_paths_refl))))
                (Obj.magic pathscomp0rid (Obj.magic f0 y pyx)
                  (Obj.magic h y (fun z lzy ->
                    Obj.magic f0 z
                      (cons (Obj.magic x) y z z Coq_paths_refl lzy
                        (Obj.magic pyx)))) (Obj.magic f1 y pyx))))
            (Obj.magic e_comp y pyx))))))

(** val assemble_disassemble :
    ('a1, 'a2, 'a3) hereditary -> 'a1 -> ('a1, 'a2, 'a3) attempt -> ('a1,
    'a2, 'a3) attempt paths **)

let assemble_disassemble h x f =
  attempt_paths h x (assemble_attempt h x (disassemble_attempt h x f)) f
    (fun y pyx0 ->
    let pr3 = pyx0.pr1 in
    let pyx = pyx0.pr2 in
    (match pr3 with
     | O ->
       pathsinv0 (attempt_fun h x f y { pr1 = O; pr2 = pyx })
         (attempt_fun h x (assemble_attempt h x (disassemble_attempt h x f))
           y { pr1 = O; pr2 = pyx })
         (attempt_comp h x f y { pr1 = O; pr2 = pyx })
     | S _ -> Coq_paths_refl)) (fun y pyx0 ->
    let pr3 = pyx0.pr1 in
    let pyx = pyx0.pr2 in
    (match pr3 with
     | O ->
       pathscomp0
         (maponpaths (Obj.magic h y) (fun z ->
           Obj.magic (fun lzy ->
             attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
               (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                 (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx))))
           (fun z ->
           Obj.magic (fun lzy ->
             attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
               (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                 { pr1 = O; pr2 = pyx })))
           (funextsec (fun z ->
             Obj.magic (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                 (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                   (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx))))
             (fun z ->
             Obj.magic (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                 (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                   { pr1 = O; pr2 = pyx }))) (fun z ->
             Obj.magic funextsec (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                 (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                   (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
               (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                 (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                   { pr1 = O; pr2 = pyx })) (fun _ -> Coq_paths_refl))))
         (maponpaths (h y) (fun z lzy ->
           attempt_fun h x f z
             (cons' x y z z { pr1 = O; pr2 = (Obj.magic Coq_paths_refl) } lzy
               (Obj.magic pyx))) (fun z lzy ->
           attempt_fun h x f z
             (cons x y z z Coq_paths_refl lzy { pr1 = O; pr2 = pyx }))
           Coq_paths_refl)
         (pathscomp0
           (h y (fun z lzy ->
             attempt_fun h x f z (cons' x y z z (nil z) lzy (Obj.magic pyx))))
           (attempt_fun h x f y { pr1 = O; pr2 = pyx })
           (h y (fun z lzy ->
             attempt_fun h x f z (cons' x y z z (nil z) lzy (Obj.magic pyx))))
           (pathsinv0 (attempt_fun h x f y { pr1 = O; pr2 = pyx })
             (h y (fun z lzy ->
               attempt_fun h x f z (cons' x y z z (nil z) lzy (Obj.magic pyx))))
             (attempt_comp h x f y { pr1 = O; pr2 = pyx }))
           (attempt_comp h x f y { pr1 = O; pr2 = pyx }))
         (maponpaths
           (maponpaths (h y) (fun z lzy ->
             attempt_fun h x f z
               (cons' x y z z { pr1 = O; pr2 = (Obj.magic Coq_paths_refl) }
                 lzy (Obj.magic pyx))) (fun z lzy ->
             attempt_fun h x f z
               (cons x y z z Coq_paths_refl lzy { pr1 = O; pr2 = pyx })))
           (Obj.magic funextsec (fun z ->
             Obj.magic (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                 (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                   (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx))))
             (fun z ->
             Obj.magic (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                 (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                   { pr1 = O; pr2 = pyx }))) (fun z ->
             Obj.magic funextsec (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                 (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                   (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
               (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                 (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                   { pr1 = O; pr2 = pyx })) (fun _ -> Coq_paths_refl)))
           Coq_paths_refl
           (pathscomp0
             (Obj.magic funextsec (fun z ->
               Obj.magic (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                     (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx))))
               (fun z ->
               Obj.magic (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                     (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx))))
               (fun z ->
               Obj.magic funextsec (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                     (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
                 (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = O; pr2 = pyx })) (fun _ -> Coq_paths_refl)))
             (Obj.magic funextsec (fun z ->
               Obj.magic (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                     (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx))))
               (fun z ->
               Obj.magic (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                     (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx))))
               (toforallpaths (fun z ->
                 Obj.magic (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                       (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx))))
                 (fun z ->
                 Obj.magic (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                       (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx))))
                 Coq_paths_refl)) Coq_paths_refl
             (maponpaths
               (Obj.magic funextsec (fun z ->
                 Obj.magic (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                       (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx))))
                 (fun z ->
                 Obj.magic (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                       (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))))
               (fun z ->
               Obj.magic funextsec (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                     (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
                 (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = O; pr2 = pyx })) (fun _ -> Coq_paths_refl))
               (Obj.magic toforallpaths (fun z lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                     (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
                 (fun z lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                     (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
                 Coq_paths_refl)
               (funextsec (fun z ->
                 Obj.magic funextsec (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                       (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
                   (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = O; pr2 = pyx })) (fun _ -> Coq_paths_refl))
                 (Obj.magic toforallpaths (fun z lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                       (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
                   (fun z lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                       (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
                   Coq_paths_refl) (fun z ->
                 Obj.magic funextsec_toforallpaths (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                       (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
                   (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons' (Obj.magic x) (Obj.magic y) z z { pr1 = O; pr2 =
                       (Obj.magic Coq_paths_refl) } lzy (Obj.magic pyx)))
                   Coq_paths_refl)))
             (funextsec_toforallpaths (fun z lzy ->
               attempt_fun h x f z
                 (cons' x y z z { pr1 = O; pr2 = (Obj.magic Coq_paths_refl) }
                   lzy (Obj.magic pyx))) (fun z lzy ->
               attempt_fun h x f z
                 (cons' x y z z { pr1 = O; pr2 = (Obj.magic Coq_paths_refl) }
                   lzy (Obj.magic pyx))) Coq_paths_refl)))
         (pathsinv0
           (pathscomp0
             (h y (fun z lzy ->
               attempt_fun h x f z (cons' x y z z (nil z) lzy (Obj.magic pyx))))
             (attempt_fun h x f y { pr1 = O; pr2 = pyx })
             (h y (fun z lzy ->
               attempt_fun h x f z (cons' x y z z (nil z) lzy (Obj.magic pyx))))
             (pathsinv0 (attempt_fun h x f y { pr1 = O; pr2 = pyx })
               (h y (fun z lzy ->
                 attempt_fun h x f z
                   (cons' x y z z (nil z) lzy (Obj.magic pyx))))
               (attempt_comp h x f y { pr1 = O; pr2 = pyx }))
             (attempt_comp h x f y { pr1 = O; pr2 = pyx })) Coq_paths_refl
           (pathsinv0l (attempt_fun h x f y { pr1 = O; pr2 = pyx })
             (h y (fun z lzy ->
               attempt_fun h x f z (cons' x y z z (nil z) lzy (Obj.magic pyx))))
             (attempt_comp h x f y { pr1 = O; pr2 = pyx })))
     | S n ->
       pathscomp0
         (pathscomp0
           ((assemble_attempt h x (disassemble_attempt h x f)).pr1 y { pr1 =
             (S n); pr2 = pyx })
           (h y (fun z lzy ->
             attempt_fun h x f z
               (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx })))
           (h y (fun z lzy ->
             attempt_fun h x f z
               (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx })))
           (attempt_comp h x
             (assemble_attempt h x (disassemble_attempt h x f)) y { pr1 = (S
             n); pr2 = pyx })
           (maponpaths (Obj.magic h y) (fun z ->
             Obj.magic (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x)
                 (assemble_attempt (Obj.magic h) (Obj.magic x)
                   (disassemble_attempt (Obj.magic h) (Obj.magic x)
                     (Obj.magic f))) z
                 (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                   { pr1 = (S n); pr2 = pyx }))) (fun z ->
             Obj.magic (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                 (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                   { pr1 = (S n); pr2 = pyx })))
             (funextsec (fun z ->
               Obj.magic (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x)
                   (assemble_attempt (Obj.magic h) (Obj.magic x)
                     (disassemble_attempt (Obj.magic h) (Obj.magic x)
                       (Obj.magic f))) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx }))) (fun z ->
               Obj.magic (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx }))) (fun z ->
               Obj.magic funextsec (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x)
                   (assemble_attempt (Obj.magic h) (Obj.magic x)
                     (disassemble_attempt (Obj.magic h) (Obj.magic x)
                       (Obj.magic f))) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                 let pyx1 =
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx }).pr2
                 in
                 (match (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                          lzy { pr1 = (S n); pr2 = pyx }).pr1 with
                  | O ->
                    pathsinv0
                      (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f)
                        z { pr1 = O; pr2 = pyx1 })
                      (attempt_fun (Obj.magic h) (Obj.magic x)
                        (assemble_attempt (Obj.magic h) (Obj.magic x)
                          (disassemble_attempt (Obj.magic h) (Obj.magic x)
                            (Obj.magic f))) z { pr1 = O; pr2 = pyx1 })
                      (attempt_comp (Obj.magic h) (Obj.magic x) (Obj.magic f)
                        z { pr1 = O; pr2 = pyx1 })
                  | S _ -> Coq_paths_refl))))))
         (pathscomp0
           ((assemble_attempt h x (disassemble_attempt h x f)).pr1 y { pr1 =
             (S n); pr2 = pyx })
           (h y (fun z lzy ->
             attempt_fun h x f z
               (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx })))
           (h y (fun z lzy ->
             attempt_fun h x f z
               (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx })))
           (attempt_comp h x
             (assemble_attempt h x (disassemble_attempt h x f)) y { pr1 = (S
             n); pr2 = pyx }) Coq_paths_refl)
         (attempt_comp h x (assemble_attempt h x (disassemble_attempt h x f))
           y { pr1 = (S n); pr2 = pyx })
         (maponpaths
           (pathscomp0
             ((assemble_attempt h x (disassemble_attempt h x f)).pr1 y
               { pr1 = (S n); pr2 = pyx })
             (h y (fun z lzy ->
               attempt_fun h x f z
                 (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx })))
             (h y (fun z lzy ->
               attempt_fun h x f z
                 (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx })))
             (attempt_comp h x
               (assemble_attempt h x (disassemble_attempt h x f)) y { pr1 =
               (S n); pr2 = pyx }))
           (maponpaths (Obj.magic h y) (fun z ->
             Obj.magic (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x)
                 (assemble_attempt (Obj.magic h) (Obj.magic x)
                   (disassemble_attempt (Obj.magic h) (Obj.magic x)
                     (Obj.magic f))) z
                 (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                   { pr1 = (S n); pr2 = pyx }))) (fun z ->
             Obj.magic (fun lzy ->
               attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                 (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                   { pr1 = (S n); pr2 = pyx })))
             (funextsec (fun z ->
               Obj.magic (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x)
                   (assemble_attempt (Obj.magic h) (Obj.magic x)
                     (disassemble_attempt (Obj.magic h) (Obj.magic x)
                       (Obj.magic f))) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx }))) (fun z ->
               Obj.magic (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx }))) (fun z ->
               Obj.magic funextsec (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x)
                   (assemble_attempt (Obj.magic h) (Obj.magic x)
                     (disassemble_attempt (Obj.magic h) (Obj.magic x)
                       (Obj.magic f))) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                 let pyx1 =
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx }).pr2
                 in
                 (match (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                          lzy { pr1 = (S n); pr2 = pyx }).pr1 with
                  | O ->
                    pathsinv0
                      (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f)
                        z { pr1 = O; pr2 = pyx1 })
                      (attempt_fun (Obj.magic h) (Obj.magic x)
                        (assemble_attempt (Obj.magic h) (Obj.magic x)
                          (disassemble_attempt (Obj.magic h) (Obj.magic x)
                            (Obj.magic f))) z { pr1 = O; pr2 = pyx1 })
                      (attempt_comp (Obj.magic h) (Obj.magic x) (Obj.magic f)
                        z { pr1 = O; pr2 = pyx1 })
                  | S _ -> Coq_paths_refl))))) Coq_paths_refl
           (maponpaths
             (maponpaths (h y) (fun z lzy ->
               attempt_fun h x
                 (assemble_attempt h x (disassemble_attempt h x f)) z
                 (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx }))
               (fun z lzy ->
               attempt_fun h x f z
                 (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx })))
             (Obj.magic funextsec (fun z ->
               Obj.magic (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x)
                   (assemble_attempt (Obj.magic h) (Obj.magic x)
                     (disassemble_attempt (Obj.magic h) (Obj.magic x)
                       (Obj.magic f))) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx }))) (fun z ->
               Obj.magic (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx }))) (fun z ->
               Obj.magic funextsec (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x)
                   (assemble_attempt (Obj.magic h) (Obj.magic x)
                     (disassemble_attempt (Obj.magic h) (Obj.magic x)
                       (Obj.magic f))) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                 attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                 let pyx1 =
                   (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                     { pr1 = (S n); pr2 = pyx }).pr2
                 in
                 (match (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                          lzy { pr1 = (S n); pr2 = pyx }).pr1 with
                  | O ->
                    pathsinv0
                      (attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f)
                        z { pr1 = O; pr2 = pyx1 })
                      (attempt_fun (Obj.magic h) (Obj.magic x)
                        (assemble_attempt (Obj.magic h) (Obj.magic x)
                          (disassemble_attempt (Obj.magic h) (Obj.magic x)
                            (Obj.magic f))) z { pr1 = O; pr2 = pyx1 })
                      (attempt_comp (Obj.magic h) (Obj.magic x) (Obj.magic f)
                        z { pr1 = O; pr2 = pyx1 })
                  | S _ -> Coq_paths_refl)))) Coq_paths_refl
             (pathscomp0
               (Obj.magic funextsec (fun z ->
                 Obj.magic (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x)
                     (assemble_attempt (Obj.magic h) (Obj.magic x)
                       (disassemble_attempt (Obj.magic h) (Obj.magic x)
                         (Obj.magic f))) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx }))) (fun z ->
                 Obj.magic (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x)
                     (assemble_attempt (Obj.magic h) (Obj.magic x)
                       (disassemble_attempt (Obj.magic h) (Obj.magic x)
                         (Obj.magic f))) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx }))) (fun z ->
                 Obj.magic funextsec (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x)
                     (assemble_attempt (Obj.magic h) (Obj.magic x)
                       (disassemble_attempt (Obj.magic h) (Obj.magic x)
                         (Obj.magic f))) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                   let pyx1 =
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx }).pr2
                   in
                   (match (cons (Obj.magic x) (Obj.magic y) z z
                            Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx }).pr1 with
                    | O ->
                      pathsinv0
                        (attempt_fun (Obj.magic h) (Obj.magic x)
                          (Obj.magic f) z { pr1 = O; pr2 = pyx1 })
                        (attempt_fun (Obj.magic h) (Obj.magic x)
                          (assemble_attempt (Obj.magic h) (Obj.magic x)
                            (disassemble_attempt (Obj.magic h) (Obj.magic x)
                              (Obj.magic f))) z { pr1 = O; pr2 = pyx1 })
                        (attempt_comp (Obj.magic h) (Obj.magic x)
                          (Obj.magic f) z { pr1 = O; pr2 = pyx1 })
                    | S _ -> Coq_paths_refl))))
               (Obj.magic funextsec (fun z ->
                 Obj.magic (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x)
                     (assemble_attempt (Obj.magic h) (Obj.magic x)
                       (disassemble_attempt (Obj.magic h) (Obj.magic x)
                         (Obj.magic f))) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx }))) (fun z ->
                 Obj.magic (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x)
                     (assemble_attempt (Obj.magic h) (Obj.magic x)
                       (disassemble_attempt (Obj.magic h) (Obj.magic x)
                         (Obj.magic f))) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx })))
                 (toforallpaths (fun z ->
                   Obj.magic (fun lzy ->
                     attempt_fun (Obj.magic h) (Obj.magic x)
                       (assemble_attempt (Obj.magic h) (Obj.magic x)
                         (disassemble_attempt (Obj.magic h) (Obj.magic x)
                           (Obj.magic f))) z
                       (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx }))) (fun z ->
                   Obj.magic (fun lzy ->
                     attempt_fun (Obj.magic h) (Obj.magic x)
                       (assemble_attempt (Obj.magic h) (Obj.magic x)
                         (disassemble_attempt (Obj.magic h) (Obj.magic x)
                           (Obj.magic f))) z
                       (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx }))) Coq_paths_refl))
               Coq_paths_refl
               (maponpaths
                 (Obj.magic funextsec (fun z ->
                   Obj.magic (fun lzy ->
                     attempt_fun (Obj.magic h) (Obj.magic x)
                       (assemble_attempt (Obj.magic h) (Obj.magic x)
                         (disassemble_attempt (Obj.magic h) (Obj.magic x)
                           (Obj.magic f))) z
                       (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx }))) (fun z ->
                   Obj.magic (fun lzy ->
                     attempt_fun (Obj.magic h) (Obj.magic x)
                       (assemble_attempt (Obj.magic h) (Obj.magic x)
                         (disassemble_attempt (Obj.magic h) (Obj.magic x)
                           (Obj.magic f))) z
                       (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx })))) (fun z ->
                 Obj.magic funextsec (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x)
                     (assemble_attempt (Obj.magic h) (Obj.magic x)
                       (disassemble_attempt (Obj.magic h) (Obj.magic x)
                         (Obj.magic f))) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                   let pyx1 =
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx }).pr2
                   in
                   (match (cons (Obj.magic x) (Obj.magic y) z z
                            Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx }).pr1 with
                    | O ->
                      pathsinv0
                        (attempt_fun (Obj.magic h) (Obj.magic x)
                          (Obj.magic f) z { pr1 = O; pr2 = pyx1 })
                        (attempt_fun (Obj.magic h) (Obj.magic x)
                          (assemble_attempt (Obj.magic h) (Obj.magic x)
                            (disassemble_attempt (Obj.magic h) (Obj.magic x)
                              (Obj.magic f))) z { pr1 = O; pr2 = pyx1 })
                        (attempt_comp (Obj.magic h) (Obj.magic x)
                          (Obj.magic f) z { pr1 = O; pr2 = pyx1 })
                    | S _ -> Coq_paths_refl)))
                 (Obj.magic toforallpaths (fun z lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x)
                     (assemble_attempt (Obj.magic h) (Obj.magic x)
                       (disassemble_attempt (Obj.magic h) (Obj.magic x)
                         (Obj.magic f))) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx })) (fun z lzy ->
                   attempt_fun (Obj.magic h) (Obj.magic x)
                     (assemble_attempt (Obj.magic h) (Obj.magic x)
                       (disassemble_attempt (Obj.magic h) (Obj.magic x)
                         (Obj.magic f))) z
                     (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl lzy
                       { pr1 = (S n); pr2 = pyx })) Coq_paths_refl)
                 (funextsec (fun z ->
                   Obj.magic funextsec (fun lzy ->
                     attempt_fun (Obj.magic h) (Obj.magic x)
                       (assemble_attempt (Obj.magic h) (Obj.magic x)
                         (disassemble_attempt (Obj.magic h) (Obj.magic x)
                           (Obj.magic f))) z
                       (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                     attempt_fun (Obj.magic h) (Obj.magic x) (Obj.magic f) z
                       (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                     let pyx1 =
                       (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx }).pr2
                     in
                     (match (cons (Obj.magic x) (Obj.magic y) z z
                              Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx }).pr1 with
                      | O ->
                        pathsinv0
                          (attempt_fun (Obj.magic h) (Obj.magic x)
                            (Obj.magic f) z { pr1 = O; pr2 = pyx1 })
                          (attempt_fun (Obj.magic h) (Obj.magic x)
                            (assemble_attempt (Obj.magic h) (Obj.magic x)
                              (disassemble_attempt (Obj.magic h)
                                (Obj.magic x) (Obj.magic f))) z { pr1 = O;
                            pr2 = pyx1 })
                          (attempt_comp (Obj.magic h) (Obj.magic x)
                            (Obj.magic f) z { pr1 = O; pr2 = pyx1 })
                      | S _ -> Coq_paths_refl)))
                   (Obj.magic toforallpaths (fun z lzy ->
                     attempt_fun (Obj.magic h) (Obj.magic x)
                       (assemble_attempt (Obj.magic h) (Obj.magic x)
                         (disassemble_attempt (Obj.magic h) (Obj.magic x)
                           (Obj.magic f))) z
                       (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx })) (fun z lzy ->
                     attempt_fun (Obj.magic h) (Obj.magic x)
                       (assemble_attempt (Obj.magic h) (Obj.magic x)
                         (disassemble_attempt (Obj.magic h) (Obj.magic x)
                           (Obj.magic f))) z
                       (cons (Obj.magic x) (Obj.magic y) z z Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx })) Coq_paths_refl)
                   (fun w ->
                   Obj.magic funextsec_toforallpaths (fun lzy ->
                     attempt_fun (Obj.magic h) (Obj.magic x)
                       (assemble_attempt (Obj.magic h) (Obj.magic x)
                         (disassemble_attempt (Obj.magic h) (Obj.magic x)
                           (Obj.magic f))) w
                       (cons (Obj.magic x) (Obj.magic y) w w Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx })) (fun lzy ->
                     attempt_fun (Obj.magic h) (Obj.magic x)
                       (assemble_attempt (Obj.magic h) (Obj.magic x)
                         (disassemble_attempt (Obj.magic h) (Obj.magic x)
                           (Obj.magic f))) w
                       (cons (Obj.magic x) (Obj.magic y) w w Coq_paths_refl
                         lzy { pr1 = (S n); pr2 = pyx })) Coq_paths_refl)))
               (funextsec_toforallpaths (fun z lzy ->
                 attempt_fun h x
                   (assemble_attempt h x (disassemble_attempt h x f)) z
                   (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 =
                     pyx })) (fun z lzy ->
                 attempt_fun h x
                   (assemble_attempt h x (disassemble_attempt h x f)) z
                   (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 =
                     pyx })) Coq_paths_refl))))
         (pathscomp0rid
           ((assemble_attempt h x (disassemble_attempt h x f)).pr1 y { pr1 =
             (S n); pr2 = pyx })
           (h y (fun z lzy ->
             attempt_fun h x f z
               (cons x y z z Coq_paths_refl lzy { pr1 = (S n); pr2 = pyx })))
           (attempt_comp h x
             (assemble_attempt h x (disassemble_attempt h x f)) y { pr1 = (S
             n); pr2 = pyx }))))

(** val iscontr_attempt :
    ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 ->
    ('a1, 'a2, 'a3) attempt iscontr **)

let iscontr_attempt h wwf_lt = h
  (* Obj.magic wwf_lt (fun _ -> iscontr_hProp) (fun x iH -> *)
  (*   iscontrretract (assemble_attempt h x) (disassemble_attempt h x) *)
  (*     (assemble_disassemble h x) *)
  (*     (impred_iscontr (fun z -> *)
  (*       impred_iscontr (fun _ -> *)
  (*         impred_iscontr (fun l -> impred_iscontr (fun _ -> iH z l)))))) *)

(** val the_attempt :
    ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 ->
    ('a1, 'a2, 'a3) attempt **)

let the_attempt h wwf_lt x =
  iscontrpr1 (iscontr_attempt h wwf_lt x)

(** val the_value :
    ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a3 **)

let the_value h wwf_lt x =
  attempt_fun h x (the_attempt h wwf_lt x) x (nil x)

(** val the_comp :
    ('a1, 'a2, 'a3) hereditary -> ('a1, 'a2) weakly_well_founded -> 'a1 ->
    'a3 paths **)

let the_comp h wwf_lt x =
  let e =
    pathsinv0 (assemble_attempt h x (fun y _ _ _ -> the_attempt h wwf_lt y))
      (the_attempt h wwf_lt x)
      (iscontr_uniqueness (iscontr_attempt h wwf_lt x)
        (assemble_attempt h x (fun y _ _ _ -> the_attempt h wwf_lt y)))
  in
  eqtohomot (attempt_fun h x (the_attempt h wwf_lt x) x)
    (attempt_fun h x
      (assemble_attempt h x (fun y _ _ _ -> the_attempt h wwf_lt y)) x)
    (eqtohomot (attempt_fun h x (the_attempt h wwf_lt x))
      (attempt_fun h x
        (assemble_attempt h x (fun y _ _ _ -> the_attempt h wwf_lt y)))
      (maponpaths (attempt_fun h x) (the_attempt h wwf_lt x)
        (assemble_attempt h x (fun y _ _ _ -> the_attempt h wwf_lt y)) e) x)
    (nil x)

(** val strongly_from_weakly_well_founded :
    ('a1, 'a2) weakly_well_founded -> ('a1, 'a2, __) hereditary -> ('a1 ->
    __, 'a1 -> __ paths) total2 **)

let strongly_from_weakly_well_founded wwf_lt h_P =
  { pr1 = (the_value h_P wwf_lt); pr2 = (the_comp h_P wwf_lt) }

(** val irrefl : ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a2 neg **)

let irrefl wwf_lt z l =
  (Obj.magic strongly_from_weakly_well_founded wwf_lt (fun _ h ->
    Obj.magic (fun _ -> Obj.magic h z l Coq_paths_refl))).pr1 z Coq_paths_refl

(** val notboth :
    ('a1, 'a2) weakly_well_founded -> 'a1 -> 'a1 -> 'a2 -> 'a2 neg **)

let notboth wwf_lt r s l m =
  (Obj.magic strongly_from_weakly_well_founded wwf_lt (fun _ h ->
    Obj.magic (fun c ->
      match c with
      | Coq_ii1 _ -> Obj.magic h s m (Coq_ii2 Coq_paths_refl)
      | Coq_ii2 _ -> Obj.magic h r l (Coq_ii1 Coq_paths_refl)))).pr1 r
    (Coq_ii1 Coq_paths_refl)

(** val diagRecursion :
    (nat -> 'a1) -> (nat -> nat -> 'a1 -> 'a1) -> nat -> nat -> 'a1 **)

let rec diagRecursion init ind = function
| O -> init
| S n -> (fun n0 -> ind n n0 (diagRecursion init ind n (S n0)))

(** val chaintrans :
    'a1 -> 'a1 -> 'a1 -> nat -> nat -> ('a1, 'a2) chain -> ('a1, 'a2) chain
    -> ('a1, 'a2) chain **)

let chaintrans _ y z m n =
  diagRecursion (fun _ _ _ -> idfun) (fun r s p _ c d ->
    let u = (Obj.magic c).pr1 in
    let pr3 = (Obj.magic c).pr2 in
    let t = pr3.pr1 in
    let pr4 = pr3.pr2 in
    let b = pr4.pr1 in
    let pr5 = pr4.pr2 in
    let k = pr5.pr1 in
    internal_paths_rew_r (S (add r s)) (add r (S s))
      (p u b (cons1 s t u u z Coq_paths_refl k d)) (plus_n_Sm r s)) m n y

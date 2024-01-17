open NaturalNumbers
open PartA
open PartA0
open PartB
open Preamble
open Propositions
open UnivalenceAxiom

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type _UU2115_ = nat

module Uniqueness =
 struct
  (** val helper_A :
      'a1 -> (nat -> 'a1 -> 'a1) -> (nat -> 'a1) -> (nat -> 'a1 paths, ('a1
      paths, nat -> 'a1 paths) dirprod) weq **)

  let helper_A p0 iH f =
    { pr1 = (fun h -> { pr1 = (h O); pr2 = (fun n ->
      pathscomp0 (f (S n))
        (let rec f0 = function
         | O -> p0
         | S n1 -> iH n1 (f0 n1)
         in f0 (S n)) (iH n (f n)) (h (S n))
        (maponpaths (iH n)
          (let rec f0 = function
           | O -> p0
           | S n1 -> iH n1 (f0 n1)
           in f0 n) (f n)
          (pathsinv0 (f n)
            (let rec f0 = function
             | O -> p0
             | S n1 -> iH n1 (f0 n1)
             in f0 n) (h n)))) }); pr2 =
      (isweq_iso (fun h -> { pr1 = (h O); pr2 = (fun n ->
        pathscomp0 (f (S n))
          (let rec f0 = function
           | O -> p0
           | S n1 -> iH n1 (f0 n1)
           in f0 (S n)) (iH n (f n)) (h (S n))
          (maponpaths (iH n)
            (let rec f0 = function
             | O -> p0
             | S n1 -> iH n1 (f0 n1)
             in f0 n) (f n)
            (pathsinv0 (f n)
              (let rec f0 = function
               | O -> p0
               | S n1 -> iH n1 (f0 n1)
               in f0 n) (h n)))) }) (fun x ->
        let h0 = x.pr1 in
        let h' = x.pr2 in
        (fun n ->
        let rec f0 = function
        | O -> h0
        | S n1 ->
          pathscomp0 (f (S n1)) (iH n1 (f n1))
            (iH n1
              (let rec f1 = function
               | O -> p0
               | S n3 -> iH n3 (f1 n3)
               in f1 n1)) (h' n1)
            (maponpaths (iH n1) (f n1)
              (let rec f1 = function
               | O -> p0
               | S n3 -> iH n3 (f1 n3)
               in f1 n1) (f0 n1))
        in f0 n)) (fun h ->
        Obj.magic funextsec (fun n ->
          let rec f0 = function
          | O -> Obj.magic h O
          | S n1 ->
            Obj.magic pathscomp0 (f (S n1)) (iH n1 (f n1))
              (iH n1
                (let rec f1 = function
                 | O -> p0
                 | S n3 -> iH n3 (f1 n3)
                 in f1 n1))
              (pathscomp0 (f (S n1))
                (iH n1
                  (let rec f1 = function
                   | O -> p0
                   | S n3 -> iH n3 (f1 n3)
                   in f1 n1)) (iH n1 (f n1)) (h (S n1))
                (maponpaths (iH n1)
                  (let rec f1 = function
                   | O -> p0
                   | S n3 -> iH n3 (f1 n3)
                   in f1 n1) (f n1)
                  (pathsinv0 (f n1)
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1) (h n1))))
              (maponpaths (iH n1) (f n1)
                (let rec f1 = function
                 | O -> p0
                 | S n3 -> iH n3 (f1 n3)
                 in f1 n1) (Obj.magic f0 n1))
          in f0 (Obj.magic n)) h (fun n ->
          let rec f0 = function
          | O -> Coq_paths_refl
          | S n1 ->
            internal_paths_rew
              (pathscomp0 (f (S n1))
                (iH n1
                  (let rec f1 = function
                   | O -> p0
                   | S n3 -> iH n3 (f1 n3)
                   in f1 n1))
                (iH n1
                  (let rec f1 = function
                   | O -> p0
                   | S n3 -> iH n3 (f1 n3)
                   in f1 n1)) (h (S n1))
                (pathscomp0
                  (iH n1
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1)) (iH n1 (f n1))
                  (iH n1
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1))
                  (maponpaths (iH n1)
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1) (f n1)
                    (pathsinv0 (f n1)
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1) (h n1)))
                  (maponpaths (iH n1) (f n1)
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1)
                    (let rec f1 = function
                     | O -> h O
                     | S n3 ->
                       pathscomp0 (f (S n3)) (iH n3 (f n3))
                         (iH n3
                           (let rec f2 = function
                            | O -> p0
                            | S n5 -> iH n5 (f2 n5)
                            in f2 n3))
                         (pathscomp0 (f (S n3))
                           (iH n3
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3)) (iH n3 (f n3)) (h (S n3))
                           (maponpaths (iH n3)
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3) (f n3)
                             (pathsinv0 (f n3)
                               (let rec f2 = function
                                | O -> p0
                                | S n5 -> iH n5 (f2 n5)
                                in f2 n3) (h n3))))
                         (maponpaths (iH n3) (f n3)
                           (let rec f2 = function
                            | O -> p0
                            | S n5 -> iH n5 (f2 n5)
                            in f2 n3) (f1 n3))
                     in f1 n1))))
              (pathscomp0
                (Obj.magic pathscomp0 (f (S n1))
                  (iH n1
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1))
                  (iH n1
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1)) (h (S n1))
                  (pathscomp0
                    (iH n1
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1)) (iH n1 (f n1))
                    (iH n1
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1))
                    (maponpaths (iH n1)
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1) (f n1)
                      (pathsinv0 (f n1)
                        (let rec f1 = function
                         | O -> p0
                         | S n3 -> iH n3 (f1 n3)
                         in f1 n1) (h n1)))
                    (maponpaths (iH n1) (f n1)
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1)
                      (let rec f1 = function
                       | O -> h O
                       | S n3 ->
                         pathscomp0 (f (S n3)) (iH n3 (f n3))
                           (iH n3
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3))
                           (pathscomp0 (f (S n3))
                             (iH n3
                               (let rec f2 = function
                                | O -> p0
                                | S n5 -> iH n5 (f2 n5)
                                in f2 n3)) (iH n3 (f n3)) (h (S n3))
                             (maponpaths (iH n3)
                               (let rec f2 = function
                                | O -> p0
                                | S n5 -> iH n5 (f2 n5)
                                in f2 n3) (f n3)
                               (pathsinv0 (f n3)
                                 (let rec f2 = function
                                  | O -> p0
                                  | S n5 -> iH n5 (f2 n5)
                                  in f2 n3) (h n3))))
                           (maponpaths (iH n3) (f n3)
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3) (f1 n3))
                       in f1 n1))))
                (Obj.magic pathscomp0 (f (S n1))
                  (iH n1
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1))
                  (iH n1
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1)) (h (S n1)) Coq_paths_refl)
                (Obj.magic h (S n1))
                (internal_paths_rew
                  (maponpaths (iH n1)
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1)
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1)
                    (pathscomp0
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1) (f n1)
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1)
                      (pathsinv0 (f n1)
                        (let rec f1 = function
                         | O -> p0
                         | S n3 -> iH n3 (f1 n3)
                         in f1 n1) (h n1))
                      (let rec f1 = function
                       | O -> h O
                       | S n3 ->
                         pathscomp0 (f (S n3)) (iH n3 (f n3))
                           (iH n3
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3))
                           (pathscomp0 (f (S n3))
                             (iH n3
                               (let rec f2 = function
                                | O -> p0
                                | S n5 -> iH n5 (f2 n5)
                                in f2 n3)) (iH n3 (f n3)) (h (S n3))
                             (maponpaths (iH n3)
                               (let rec f2 = function
                                | O -> p0
                                | S n5 -> iH n5 (f2 n5)
                                in f2 n3) (f n3)
                               (pathsinv0 (f n3)
                                 (let rec f2 = function
                                  | O -> p0
                                  | S n5 -> iH n5 (f2 n5)
                                  in f2 n3) (h n3))))
                           (maponpaths (iH n3) (f n3)
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3) (f1 n3))
                       in f1 n1)))
                  (internal_paths_rew_r
                    (let rec f1 = function
                     | O -> Obj.magic h O
                     | S n3 ->
                       Obj.magic pathscomp0 (f (S n3)) (iH n3 (f n3))
                         (iH n3
                           (let rec f2 = function
                            | O -> p0
                            | S n5 -> iH n5 (f2 n5)
                            in f2 n3))
                         (pathscomp0 (f (S n3))
                           (iH n3
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3)) (iH n3 (f n3)) (h (S n3))
                           (maponpaths (iH n3)
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3) (f n3)
                             (pathsinv0 (f n3)
                               (let rec f2 = function
                                | O -> p0
                                | S n5 -> iH n5 (f2 n5)
                                in f2 n3) (h n3))))
                         (maponpaths (iH n3) (f n3)
                           (let rec f2 = function
                            | O -> p0
                            | S n5 -> iH n5 (f2 n5)
                            in f2 n3) (Obj.magic f1 n3))
                     in f1 n1) (Obj.magic h n1)
                    (internal_paths_rew_r
                      (pathscomp0
                        (let rec f1 = function
                         | O -> p0
                         | S n3 -> iH n3 (f1 n3)
                         in f1 n1) (f n1)
                        (let rec f1 = function
                         | O -> p0
                         | S n3 -> iH n3 (f1 n3)
                         in f1 n1)
                        (pathsinv0 (f n1)
                          (let rec f1 = function
                           | O -> p0
                           | S n3 -> iH n3 (f1 n3)
                           in f1 n1) (h n1)) (h n1)) Coq_paths_refl
                      Coq_paths_refl
                      (pathsinv0l (f n1)
                        (let rec f1 = function
                         | O -> p0
                         | S n3 -> iH n3 (f1 n3)
                         in f1 n1) (h n1))) (f0 n1))
                  (pathscomp0
                    (iH n1
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1)) (iH n1 (f n1))
                    (iH n1
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1))
                    (maponpaths (iH n1)
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1) (f n1)
                      (pathsinv0 (f n1)
                        (let rec f1 = function
                         | O -> p0
                         | S n3 -> iH n3 (f1 n3)
                         in f1 n1) (h n1)))
                    (maponpaths (iH n1) (f n1)
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1)
                      (let rec f1 = function
                       | O -> h O
                       | S n3 ->
                         pathscomp0 (f (S n3)) (iH n3 (f n3))
                           (iH n3
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3))
                           (pathscomp0 (f (S n3))
                             (iH n3
                               (let rec f2 = function
                                | O -> p0
                                | S n5 -> iH n5 (f2 n5)
                                in f2 n3)) (iH n3 (f n3)) (h (S n3))
                             (maponpaths (iH n3)
                               (let rec f2 = function
                                | O -> p0
                                | S n5 -> iH n5 (f2 n5)
                                in f2 n3) (f n3)
                               (pathsinv0 (f n3)
                                 (let rec f2 = function
                                  | O -> p0
                                  | S n5 -> iH n5 (f2 n5)
                                  in f2 n3) (h n3))))
                           (maponpaths (iH n3) (f n3)
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3) (f1 n3))
                       in f1 n1)))
                  (maponpathscomp0
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1) (f n1)
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1) (iH n1)
                    (pathsinv0 (f n1)
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1) (h n1))
                    (let rec f1 = function
                     | O -> h O
                     | S n3 ->
                       pathscomp0 (f (S n3)) (iH n3 (f n3))
                         (iH n3
                           (let rec f2 = function
                            | O -> p0
                            | S n5 -> iH n5 (f2 n5)
                            in f2 n3))
                         (pathscomp0 (f (S n3))
                           (iH n3
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3)) (iH n3 (f n3)) (h (S n3))
                           (maponpaths (iH n3)
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3) (f n3)
                             (pathsinv0 (f n3)
                               (let rec f2 = function
                                | O -> p0
                                | S n5 -> iH n5 (f2 n5)
                                in f2 n3) (h n3))))
                         (maponpaths (iH n3) (f n3)
                           (let rec f2 = function
                            | O -> p0
                            | S n5 -> iH n5 (f2 n5)
                            in f2 n3) (f1 n3))
                     in f1 n1)))
                (Obj.magic pathscomp0rid (f (S n1))
                  (iH n1
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1)) (h (S n1))))
              (pathscomp0 (f (S n1)) (iH n1 (f n1))
                (iH n1
                  (let rec f1 = function
                   | O -> p0
                   | S n3 -> iH n3 (f1 n3)
                   in f1 n1))
                (pathscomp0 (f (S n1))
                  (iH n1
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1)) (iH n1 (f n1)) (h (S n1))
                  (maponpaths (iH n1)
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1) (f n1)
                    (pathsinv0 (f n1)
                      (let rec f1 = function
                       | O -> p0
                       | S n3 -> iH n3 (f1 n3)
                       in f1 n1) (h n1))))
                (maponpaths (iH n1) (f n1)
                  (let rec f1 = function
                   | O -> p0
                   | S n3 -> iH n3 (f1 n3)
                   in f1 n1)
                  (let rec f1 = function
                   | O -> h O
                   | S n3 ->
                     pathscomp0 (f (S n3)) (iH n3 (f n3))
                       (iH n3
                         (let rec f2 = function
                          | O -> p0
                          | S n5 -> iH n5 (f2 n5)
                          in f2 n3))
                       (pathscomp0 (f (S n3))
                         (iH n3
                           (let rec f2 = function
                            | O -> p0
                            | S n5 -> iH n5 (f2 n5)
                            in f2 n3)) (iH n3 (f n3)) (h (S n3))
                         (maponpaths (iH n3)
                           (let rec f2 = function
                            | O -> p0
                            | S n5 -> iH n5 (f2 n5)
                            in f2 n3) (f n3)
                           (pathsinv0 (f n3)
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3) (h n3))))
                       (maponpaths (iH n3) (f n3)
                         (let rec f2 = function
                          | O -> p0
                          | S n5 -> iH n5 (f2 n5)
                          in f2 n3) (f1 n3))
                   in f1 n1)))
              (path_assoc (f (S n1))
                (iH n1
                  (let rec f1 = function
                   | O -> p0
                   | S n3 -> iH n3 (f1 n3)
                   in f1 n1)) (iH n1 (f n1))
                (iH n1
                  (let rec f1 = function
                   | O -> p0
                   | S n3 -> iH n3 (f1 n3)
                   in f1 n1)) (h (S n1))
                (maponpaths (iH n1)
                  (let rec f1 = function
                   | O -> p0
                   | S n3 -> iH n3 (f1 n3)
                   in f1 n1) (f n1)
                  (pathsinv0 (f n1)
                    (let rec f1 = function
                     | O -> p0
                     | S n3 -> iH n3 (f1 n3)
                     in f1 n1) (h n1)))
                (maponpaths (iH n1) (f n1)
                  (let rec f1 = function
                   | O -> p0
                   | S n3 -> iH n3 (f1 n3)
                   in f1 n1)
                  (let rec f1 = function
                   | O -> h O
                   | S n3 ->
                     pathscomp0 (f (S n3)) (iH n3 (f n3))
                       (iH n3
                         (let rec f2 = function
                          | O -> p0
                          | S n5 -> iH n5 (f2 n5)
                          in f2 n3))
                       (pathscomp0 (f (S n3))
                         (iH n3
                           (let rec f2 = function
                            | O -> p0
                            | S n5 -> iH n5 (f2 n5)
                            in f2 n3)) (iH n3 (f n3)) (h (S n3))
                         (maponpaths (iH n3)
                           (let rec f2 = function
                            | O -> p0
                            | S n5 -> iH n5 (f2 n5)
                            in f2 n3) (f n3)
                           (pathsinv0 (f n3)
                             (let rec f2 = function
                              | O -> p0
                              | S n5 -> iH n5 (f2 n5)
                              in f2 n3) (h n3))))
                       (maponpaths (iH n3) (f n3)
                         (let rec f2 = function
                          | O -> p0
                          | S n5 -> iH n5 (f2 n5)
                          in f2 n3) (f1 n3))
                   in f1 n1)))
          in f0 (Obj.magic n))) (fun y ->
        let h0 = y.pr1 in
        let h' = y.pr2 in
        maponpaths (Obj.magic (fun x -> { pr1 = h0; pr2 = x })) (fun n ->
          Obj.magic pathscomp0 (f (S (Obj.magic n)))
            (let rec f0 = function
             | O -> p0
             | S n1 -> iH n1 (f0 n1)
             in f0 (S (Obj.magic n))) (Obj.magic iH n (Obj.magic f n))
            (let rec f0 = function
             | O -> h0
             | S n1 ->
               pathscomp0 (f (S n1)) (iH n1 (f n1))
                 (iH n1
                   (let rec f1 = function
                    | O -> p0
                    | S n3 -> iH n3 (f1 n3)
                    in f1 n1)) (h' n1)
                 (maponpaths (iH n1) (f n1)
                   (let rec f1 = function
                    | O -> p0
                    | S n3 -> iH n3 (f1 n3)
                    in f1 n1) (f0 n1))
             in f0 (S (Obj.magic n)))
            (maponpaths (Obj.magic iH n)
              (let rec f0 = function
               | O -> p0
               | S n1 -> iH n1 (f0 n1)
               in f0 (Obj.magic n)) (Obj.magic f n)
              (pathsinv0 (Obj.magic f n)
                (let rec f0 = function
                 | O -> p0
                 | S n1 -> iH n1 (f0 n1)
                 in f0 (Obj.magic n))
                (let rec f0 = function
                 | O -> h0
                 | S n1 ->
                   pathscomp0 (f (S n1)) (iH n1 (f n1))
                     (iH n1
                       (let rec f1 = function
                        | O -> p0
                        | S n3 -> iH n3 (f1 n3)
                        in f1 n1)) (h' n1)
                     (maponpaths (iH n1) (f n1)
                       (let rec f1 = function
                        | O -> p0
                        | S n3 -> iH n3 (f1 n3)
                        in f1 n1) (f0 n1))
                 in f0 (Obj.magic n))))) (Obj.magic h')
          (funextsec (fun n ->
            Obj.magic pathscomp0 (f (S (Obj.magic n)))
              (let rec f0 = function
               | O -> p0
               | S n1 -> iH n1 (f0 n1)
               in f0 (S (Obj.magic n))) (Obj.magic iH n (Obj.magic f n))
              (let rec f0 = function
               | O -> h0
               | S n1 ->
                 pathscomp0 (f (S n1)) (iH n1 (f n1))
                   (iH n1
                     (let rec f1 = function
                      | O -> p0
                      | S n3 -> iH n3 (f1 n3)
                      in f1 n1)) (h' n1)
                   (maponpaths (iH n1) (f n1)
                     (let rec f1 = function
                      | O -> p0
                      | S n3 -> iH n3 (f1 n3)
                      in f1 n1) (f0 n1))
               in f0 (S (Obj.magic n)))
              (maponpaths (Obj.magic iH n)
                (let rec f0 = function
                 | O -> p0
                 | S n1 -> iH n1 (f0 n1)
                 in f0 (Obj.magic n)) (Obj.magic f n)
                (pathsinv0 (Obj.magic f n)
                  (let rec f0 = function
                   | O -> p0
                   | S n1 -> iH n1 (f0 n1)
                   in f0 (Obj.magic n))
                  (let rec f0 = function
                   | O -> h0
                   | S n1 ->
                     pathscomp0 (f (S n1)) (iH n1 (f n1))
                       (iH n1
                         (let rec f1 = function
                          | O -> p0
                          | S n3 -> iH n3 (f1 n3)
                          in f1 n1)) (h' n1)
                       (maponpaths (iH n1) (f n1)
                         (let rec f1 = function
                          | O -> p0
                          | S n3 -> iH n3 (f1 n3)
                          in f1 n1) (f0 n1))
                   in f0 (Obj.magic n))))) (Obj.magic h') (fun n ->
            internal_paths_rew
              (pathscomp0 (f (S (Obj.magic n)))
                (Obj.magic iH n (Obj.magic f n))
                (Obj.magic iH n (Obj.magic f n)) (Obj.magic h' n)
                (pathscomp0 (Obj.magic iH n (Obj.magic f n))
                  (Obj.magic iH n
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n))) (Obj.magic iH n (Obj.magic f n))
                  (maponpaths (Obj.magic iH n) (Obj.magic f n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n))
                    (let rec f0 = function
                     | O -> h0
                     | S n1 ->
                       pathscomp0 (f (S n1)) (iH n1 (f n1))
                         (iH n1
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1)) (h' n1)
                         (maponpaths (iH n1) (f n1)
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1) (f0 n1))
                     in f0 (Obj.magic n)))
                  (maponpaths (Obj.magic iH n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n)) (Obj.magic f n)
                    (pathsinv0 (Obj.magic f n)
                      (let rec f0 = function
                       | O -> p0
                       | S n1 -> iH n1 (f0 n1)
                       in f0 (Obj.magic n))
                      (let rec f0 = function
                       | O -> h0
                       | S n1 ->
                         pathscomp0 (f (S n1)) (iH n1 (f n1))
                           (iH n1
                             (let rec f1 = function
                              | O -> p0
                              | S n3 -> iH n3 (f1 n3)
                              in f1 n1)) (h' n1)
                           (maponpaths (iH n1) (f n1)
                             (let rec f1 = function
                              | O -> p0
                              | S n3 -> iH n3 (f1 n3)
                              in f1 n1) (f0 n1))
                       in f0 (Obj.magic n))))))
              (internal_paths_rew
                (maponpaths (Obj.magic iH n) (Obj.magic f n) (Obj.magic f n)
                  (pathscomp0 (Obj.magic f n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n)) (Obj.magic f n)
                    (let rec f0 = function
                     | O -> h0
                     | S n1 ->
                       pathscomp0 (f (S n1)) (iH n1 (f n1))
                         (iH n1
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1)) (h' n1)
                         (maponpaths (iH n1) (f n1)
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1) (f0 n1))
                     in f0 (Obj.magic n))
                    (pathsinv0 (Obj.magic f n)
                      (let rec f0 = function
                       | O -> p0
                       | S n1 -> iH n1 (f0 n1)
                       in f0 (Obj.magic n))
                      (let rec f0 = function
                       | O -> h0
                       | S n1 ->
                         pathscomp0 (f (S n1)) (iH n1 (f n1))
                           (iH n1
                             (let rec f1 = function
                              | O -> p0
                              | S n3 -> iH n3 (f1 n3)
                              in f1 n1)) (h' n1)
                           (maponpaths (iH n1) (f n1)
                             (let rec f1 = function
                              | O -> p0
                              | S n3 -> iH n3 (f1 n3)
                              in f1 n1) (f0 n1))
                       in f0 (Obj.magic n)))))
                (internal_paths_rew_r
                  (pathscomp0 (Obj.magic f n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n)) (Obj.magic f n)
                    (let rec f0 = function
                     | O -> h0
                     | S n1 ->
                       pathscomp0 (f (S n1)) (iH n1 (f n1))
                         (iH n1
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1)) (h' n1)
                         (maponpaths (iH n1) (f n1)
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1) (f0 n1))
                     in f0 (Obj.magic n))
                    (pathsinv0 (Obj.magic f n)
                      (let rec f0 = function
                       | O -> p0
                       | S n1 -> iH n1 (f0 n1)
                       in f0 (Obj.magic n))
                      (let rec f0 = function
                       | O -> h0
                       | S n1 ->
                         pathscomp0 (f (S n1)) (iH n1 (f n1))
                           (iH n1
                             (let rec f1 = function
                              | O -> p0
                              | S n3 -> iH n3 (f1 n3)
                              in f1 n1)) (h' n1)
                           (maponpaths (iH n1) (f n1)
                             (let rec f1 = function
                              | O -> p0
                              | S n3 -> iH n3 (f1 n3)
                              in f1 n1) (f0 n1))
                       in f0 (Obj.magic n)))) Coq_paths_refl
                  (Obj.magic pathscomp0rid (f (S (Obj.magic n)))
                    (Obj.magic iH n (Obj.magic f n)) (Obj.magic h' n))
                  (pathsinv0r (Obj.magic f n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n))
                    (let rec f0 = function
                     | O -> h0
                     | S n1 ->
                       pathscomp0 (f (S n1)) (iH n1 (f n1))
                         (iH n1
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1)) (h' n1)
                         (maponpaths (iH n1) (f n1)
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1) (f0 n1))
                     in f0 (Obj.magic n))))
                (pathscomp0 (Obj.magic iH n (Obj.magic f n))
                  (Obj.magic iH n
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n))) (Obj.magic iH n (Obj.magic f n))
                  (maponpaths (Obj.magic iH n) (Obj.magic f n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n))
                    (let rec f0 = function
                     | O -> h0
                     | S n1 ->
                       pathscomp0 (f (S n1)) (iH n1 (f n1))
                         (iH n1
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1)) (h' n1)
                         (maponpaths (iH n1) (f n1)
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1) (f0 n1))
                     in f0 (Obj.magic n)))
                  (maponpaths (Obj.magic iH n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n)) (Obj.magic f n)
                    (pathsinv0 (Obj.magic f n)
                      (let rec f0 = function
                       | O -> p0
                       | S n1 -> iH n1 (f0 n1)
                       in f0 (Obj.magic n))
                      (let rec f0 = function
                       | O -> h0
                       | S n1 ->
                         pathscomp0 (f (S n1)) (iH n1 (f n1))
                           (iH n1
                             (let rec f1 = function
                              | O -> p0
                              | S n3 -> iH n3 (f1 n3)
                              in f1 n1)) (h' n1)
                           (maponpaths (iH n1) (f n1)
                             (let rec f1 = function
                              | O -> p0
                              | S n3 -> iH n3 (f1 n3)
                              in f1 n1) (f0 n1))
                       in f0 (Obj.magic n)))))
                (maponpathscomp0 (Obj.magic f n)
                  (let rec f0 = function
                   | O -> p0
                   | S n1 -> iH n1 (f0 n1)
                   in f0 (Obj.magic n)) (Obj.magic f n) (Obj.magic iH n)
                  (let rec f0 = function
                   | O -> h0
                   | S n1 ->
                     pathscomp0 (f (S n1)) (iH n1 (f n1))
                       (iH n1
                         (let rec f1 = function
                          | O -> p0
                          | S n3 -> iH n3 (f1 n3)
                          in f1 n1)) (h' n1)
                       (maponpaths (iH n1) (f n1)
                         (let rec f1 = function
                          | O -> p0
                          | S n3 -> iH n3 (f1 n3)
                          in f1 n1) (f0 n1))
                   in f0 (Obj.magic n))
                  (pathsinv0 (Obj.magic f n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n))
                    (let rec f0 = function
                     | O -> h0
                     | S n1 ->
                       pathscomp0 (f (S n1)) (iH n1 (f n1))
                         (iH n1
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1)) (h' n1)
                         (maponpaths (iH n1) (f n1)
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1) (f0 n1))
                     in f0 (Obj.magic n)))))
              (pathscomp0 (f (S (Obj.magic n)))
                (Obj.magic iH n
                  (let rec f0 = function
                   | O -> p0
                   | S n1 -> iH n1 (f0 n1)
                   in f0 (Obj.magic n))) (Obj.magic iH n (Obj.magic f n))
                (pathscomp0 (f (S (Obj.magic n)))
                  (Obj.magic iH n (Obj.magic f n))
                  (Obj.magic iH n
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n))) (Obj.magic h' n)
                  (maponpaths (Obj.magic iH n) (Obj.magic f n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n))
                    (let rec f0 = function
                     | O -> h0
                     | S n1 ->
                       pathscomp0 (f (S n1)) (iH n1 (f n1))
                         (iH n1
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1)) (h' n1)
                         (maponpaths (iH n1) (f n1)
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1) (f0 n1))
                     in f0 (Obj.magic n))))
                (maponpaths (Obj.magic iH n)
                  (let rec f0 = function
                   | O -> p0
                   | S n1 -> iH n1 (f0 n1)
                   in f0 (Obj.magic n)) (Obj.magic f n)
                  (pathsinv0 (Obj.magic f n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n))
                    (let rec f0 = function
                     | O -> h0
                     | S n1 ->
                       pathscomp0 (f (S n1)) (iH n1 (f n1))
                         (iH n1
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1)) (h' n1)
                         (maponpaths (iH n1) (f n1)
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1) (f0 n1))
                     in f0 (Obj.magic n)))))
              (path_assoc (f (S (Obj.magic n)))
                (Obj.magic iH n (Obj.magic f n))
                (Obj.magic iH n
                  (let rec f0 = function
                   | O -> p0
                   | S n1 -> iH n1 (f0 n1)
                   in f0 (Obj.magic n))) (Obj.magic iH n (Obj.magic f n))
                (Obj.magic h' n)
                (maponpaths (Obj.magic iH n) (Obj.magic f n)
                  (let rec f0 = function
                   | O -> p0
                   | S n1 -> iH n1 (f0 n1)
                   in f0 (Obj.magic n))
                  (let rec f0 = function
                   | O -> h0
                   | S n1 ->
                     pathscomp0 (f (S n1)) (iH n1 (f n1))
                       (iH n1
                         (let rec f1 = function
                          | O -> p0
                          | S n3 -> iH n3 (f1 n3)
                          in f1 n1)) (h' n1)
                       (maponpaths (iH n1) (f n1)
                         (let rec f1 = function
                          | O -> p0
                          | S n3 -> iH n3 (f1 n3)
                          in f1 n1) (f0 n1))
                   in f0 (Obj.magic n)))
                (maponpaths (Obj.magic iH n)
                  (let rec f0 = function
                   | O -> p0
                   | S n1 -> iH n1 (f0 n1)
                   in f0 (Obj.magic n)) (Obj.magic f n)
                  (pathsinv0 (Obj.magic f n)
                    (let rec f0 = function
                     | O -> p0
                     | S n1 -> iH n1 (f0 n1)
                     in f0 (Obj.magic n))
                    (let rec f0 = function
                     | O -> h0
                     | S n1 ->
                       pathscomp0 (f (S n1)) (iH n1 (f n1))
                         (iH n1
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1)) (h' n1)
                         (maponpaths (iH n1) (f n1)
                           (let rec f1 = function
                            | O -> p0
                            | S n3 -> iH n3 (f1 n3)
                            in f1 n1) (f0 n1))
                     in f0 (Obj.magic n))))))))) }

  (** val helper_B :
      'a1 -> (nat -> 'a1 -> 'a1) -> (nat -> 'a1) -> ((nat -> 'a1) paths, ('a1
      paths, nat -> 'a1 paths) dirprod) weq **)

  let helper_B p0 iH f =
    weqcomp
      (Obj.magic weqtoforallpaths f
        (let rec f0 = function
         | O -> p0
         | S n0 -> iH n0 (f0 n0)
         in f0)) (helper_A p0 iH f)

  (** val helper_C :
      'a1 -> (nat -> 'a1 -> 'a1) -> ((nat -> 'a1, (nat -> 'a1) paths) total2,
      (nat -> 'a1, ('a1 paths, nat -> 'a1 paths) dirprod) total2) weq **)

  let helper_C p0 iH =
    weqfibtototal (fun f -> helper_B p0 iH f)

  (** val hNatRecursionUniq :
      'a1 -> (nat -> 'a1 -> 'a1) -> (nat -> 'a1, ('a1 paths, nat -> 'a1
      paths) dirprod) total2 iscontr **)

  let hNatRecursionUniq p0 iH =
    iscontrweqf (helper_C p0 iH)
      (iscontrcoconustot
        (let rec f = function
         | O -> p0
         | S n0 -> iH n0 (f n0)
         in f))

  (** val helper_D :
      'a1 -> (nat -> 'a1 -> 'a1) -> ((nat -> 'a1, ('a1 paths, nat -> 'a1
      paths) dirprod) total2, ((nat -> 'a1, nat -> 'a1 paths) total2, 'a1)
      hfiber) weq **)

  let helper_D _ _ =
    make_weq (fun x ->
      let f = x.pr1 in
      let pr3 = x.pr2 in
      let h0 = pr3.pr1 in
      let h' = pr3.pr2 in { pr1 = { pr1 = f; pr2 = h' }; pr2 = h0 })
      (isweq_iso (fun x ->
        let f = x.pr1 in
        let pr3 = x.pr2 in
        let h0 = pr3.pr1 in
        let h' = pr3.pr2 in { pr1 = { pr1 = f; pr2 = h' }; pr2 = h0 })
        (fun x ->
        let pr3 = x.pr1 in
        let f = pr3.pr1 in
        let h' = pr3.pr2 in
        let h0 = x.pr2 in { pr1 = f; pr2 = { pr1 = h0; pr2 = h' } })
        (fun _ -> Coq_paths_refl) (fun _ -> Coq_paths_refl))

  (** val hNatRecursion_weq :
      (nat -> 'a1 -> 'a1) -> ((nat -> 'a1, nat -> 'a1 paths) total2, 'a1) weq **)

  let hNatRecursion_weq iH =
    { pr1 = (fun f -> f.pr1 O); pr2 = (fun p0 ->
      iscontrweqf (helper_D p0 iH) (hNatRecursionUniq p0 iH)) }
 end

(** val nat_dist : nat -> nat -> nat **)

let rec nat_dist m n =
  match m with
  | O -> n
  | S m0 -> (match n with
             | O -> m
             | S n0 -> nat_dist m0 n0)

module Discern =
 struct
  type nat_discern = __

  (** val coq_Unnamed_thm : nat -> nat -> nat_discern -> nat_discern **)

  let coq_Unnamed_thm _ _ e =
    e

  (** val nat_discern_inj : nat -> nat -> nat_discern -> nat_discern **)

  let nat_discern_inj m n e =
    match m with
    | O ->
      (match n with
       | O -> Obj.magic Coq_tt
       | S _ -> fromempty (Obj.magic e))
    | S _ -> (match n with
              | O -> fromempty (Obj.magic e)
              | S _ -> e)

  (** val nat_discern_isaprop : nat -> nat -> nat_discern isaprop **)

  let rec nat_discern_isaprop n n0 =
    match n with
    | O ->
      (match n0 with
       | O -> isapropifcontr iscontrunit
       | S _ -> isapropempty)
    | S n1 ->
      (match n0 with
       | O -> isapropempty
       | S n2 -> nat_discern_isaprop n1 n2)

  (** val nat_discern_unit : nat -> coq_UU paths **)

  let rec nat_discern_unit = function
  | O -> Coq_paths_refl
  | S n0 -> nat_discern_unit n0

  (** val nat_discern_iscontr : nat -> nat_discern iscontr **)

  let nat_discern_iscontr m =
    iscontraprop1 (nat_discern_isaprop m m)
      (let rec f = function
       | O -> Obj.magic Coq_tt
       | S n0 -> f n0
       in f m)

  (** val helper_A : nat -> nat -> nat paths -> nat_discern **)

  let rec helper_A m n =
    match m with
    | O ->
      (match n with
       | O -> (fun _ -> Obj.magic Coq_tt)
       | S n0 -> Obj.magic negpathssx0 n0)
    | S n0 ->
      (match n with
       | O -> Obj.magic negpathssx0 n0
       | S n1 -> helper_A n0 n1)

  (** val helper_B : nat -> nat -> nat_discern -> nat paths **)

  let rec helper_B m n =
    match m with
    | O ->
      (match n with
       | O -> (fun _ -> Coq_paths_refl)
       | S _ -> Obj.magic fromempty)
    | S _ ->
      (match n with
       | O -> Obj.magic fromempty
       | S _ -> (fun _ -> Coq_paths_refl))

  (** val coq_Unnamed_thm0 : nat -> nat -> nat_discern -> nat paths paths **)

  let coq_Unnamed_thm0 _ _ _ =
    Coq_paths_refl

  (** val helper_C : nat -> nat -> nat paths -> nat_discern **)

  let rec helper_C m _ _ = m
    (* cast (pathsinv0 __ __ (nat_discern_unit m)) Coq_tt *)

  (** val apSC : nat -> nat -> nat paths -> nat_discern paths **)

  let apSC m n e =
    proofirrelevance (nat_discern_isaprop m n) (helper_C m n e)
      (helper_C (S m) (S n) (maponpaths (fun x -> S x) m n e))

  (** val helper_D : nat -> nat -> (nat_discern, nat paths) isweq **)

  let helper_D m n =
    isweq_iso (helper_B m n) (helper_C m n) (fun e ->
      proofirrelevancecontr (nat_discern_iscontr n)
        (helper_C n n (helper_B n n e)) e) (fun _ ->
      let rec f = function
      | O -> Coq_paths_refl
      | S n1 ->
        pathscomp0
          (helper_B (S n1) (S n1)
            (helper_C (S n1) (S n1)
              (maponpaths (fun x -> S x) n1 n1 Coq_paths_refl)))
          (helper_B (S n1) (S n1) (helper_C n1 n1 Coq_paths_refl))
          (maponpaths (fun x -> S x) n1 n1 Coq_paths_refl)
          (maponpaths (helper_B (S n1) (S n1))
            (helper_C (S n1) (S n1)
              (maponpaths (fun x -> S x) n1 n1 Coq_paths_refl))
            (helper_C n1 n1 Coq_paths_refl)
            (pathsinv0 (helper_C n1 n1 Coq_paths_refl)
              (helper_C (S n1) (S n1)
                (maponpaths (fun x -> S x) n1 n1 Coq_paths_refl))
              (apSC n1 n1 Coq_paths_refl)))
          (maponpaths (maponpaths (fun x -> S x) n1 n1)
            (helper_B n1 n1 (helper_C n1 n1 Coq_paths_refl)) Coq_paths_refl
            (f n1))
      in f m)

  (** val coq_E : nat -> nat -> (nat_discern, nat paths) weq **)

  let coq_E m n =
    make_weq (helper_B m n) (helper_D m n)

  (** val nat_dist_anti : nat -> nat -> nat paths -> nat paths **)

  let nat_dist_anti m n i =
    helper_B m n (helper_A m n i)
 end

(** val nat_dist_symm : nat -> nat -> nat paths **)

let rec nat_dist_symm m n =
  match m with
  | O -> Coq_paths_refl
  | S n0 -> (match n with
             | O -> Coq_paths_refl
             | S n1 -> nat_dist_symm n0 n1)

(** val nat_dist_ge : nat -> nat -> hProptoType -> nat paths **)

let rec nat_dist_ge m n =
  match m with
  | O -> (fun _ -> Coq_paths_refl)
  | S n0 ->
    (match n with
     | O -> (fun _ -> Coq_paths_refl)
     | S n1 -> nat_dist_ge n0 n1)

(** val nat_dist_0m : nat -> nat paths **)

let nat_dist_0m _ =
  Coq_paths_refl

(** val nat_dist_m0 : nat -> nat paths **)

let nat_dist_m0 _ =
  Coq_paths_refl

(** val nat_dist_plus : nat -> nat -> nat paths **)

let rec nat_dist_plus m n =
  match m with
  | O -> nat_dist_m0 n
  | S n0 -> nat_dist_plus n0 n

(** val nat_dist_le : nat -> nat -> hProptoType -> nat paths **)

let rec nat_dist_le m n =
  match m with
  | O -> (fun _ -> Coq_paths_refl)
  | S n0 ->
    (match n with
     | O -> (fun _ -> Coq_paths_refl)
     | S n1 -> nat_dist_le n0 n1)

(** val nat_dist_minus : nat -> nat -> hProptoType -> nat paths **)

let nat_dist_minus m n e =
  let k = sub n m in
  let b = pathsinv0 (add (sub n m) m) n (minusplusnmm n m e) in
  let b0 = internal_paths_rew (sub n m) b k Coq_paths_refl in
  internal_paths_rew_r n (add k m)
    (internal_paths_rew_r (nat_dist k (add k m)) (nat_dist (add k m) k)
      (nat_dist_plus k m) (nat_dist_symm k (add k m))) b0

(** val nat_dist_gt : nat -> nat -> hProptoType -> nat paths **)

let rec nat_dist_gt m n x =
  match m with
  | O -> fromempty (nopathsfalsetotrue (Obj.magic x))
  | S n0 ->
    (match n with
     | O -> maponpaths (fun x0 -> S x0) (nat_dist n0 O) n0 (nat_dist_m0 n0)
     | S n1 -> nat_dist_gt n0 n1 x)

(** val nat_dist_S : nat -> nat -> nat paths **)

let nat_dist_S _ _ =
  Coq_paths_refl

(** val natminuseqlr :
    nat -> nat -> nat -> hProptoType -> nat paths -> nat paths **)

let natminuseqlr m n x i j =
  internal_paths_rew (add (sub n m) m)
    (internal_paths_rew_r (sub n m) x Coq_paths_refl j) n (minusplusnmm n m i)

(** val nat_dist_between_le :
    nat -> nat -> nat -> nat -> hProptoType -> nat paths -> (nat, (nat paths,
    nat paths) dirprod) total2 **)

let nat_dist_between_le m n a b i j =
  { pr1 = (add m a); pr2 = { pr1 = (nat_dist_plus m a); pr2 =
    (let j0 =
       internal_paths_rew (nat_dist m n) j (sub n m) (nat_dist_le m n i)
     in
     let k = natminuseqlr m n (add a b) i j0 in
     let l = nat_dist_plus (add m a) b in
     internal_paths_rew_r (nat_dist (add m a) n) (nat_dist n (add m a))
       (let k0 =
          internal_paths_rew (add (add a b) m) k (add m (add a b))
            (natpluscomm (add a b) m)
        in
        let l0 =
          internal_paths_rew (add (add m a) b) l (add m (add a b))
            (natplusassoc m a b)
        in
        internal_paths_rew_r n (add m (add a b)) l0 k0)
       (nat_dist_symm (add m a) n)) } }

(** val nat_dist_between_ge :
    nat -> nat -> nat -> nat -> hProptoType -> nat paths -> (nat, (nat paths,
    nat paths) dirprod) total2 **)


(** val nat_dist_between :
    nat -> nat -> nat -> nat -> nat paths -> (nat, (nat paths, nat paths)
    dirprod) total2 **)


(** val natleorle : nat -> nat -> (hProptoType, hProptoType) coprod **)

let natleorle m n =
  let c = natgthorleh m n in
  (match c with
   | Coq_ii1 a -> Coq_ii2 (natlthtoleh n m a)
   | Coq_ii2 b -> Coq_ii1 b)

(** val nat_dist_trans : nat -> nat -> nat -> hProptoType **)

let nat_dist_trans x y z =
  let c = natleorle x y in
  (match c with
   | Coq_ii1 a ->
     internal_paths_rew_r (nat_dist x y) (sub y x)
       (let c0 = natleorle y z in
        match c0 with
        | Coq_ii1 a0 ->
          let u = istransnatgeh z y x a0 a in
          internal_paths_rew_r (nat_dist y z) (sub z y)
            (internal_paths_rew_r (nat_dist x z) (sub z x)
              (natlehandplusrinv (sub z x) (add (sub y x) (sub z y)) x
                (internal_paths_rew_r (add (sub z x) x) z
                  (internal_paths_rew_r (add (add (sub y x) (sub z y)) x)
                    (add x (add (sub y x) (sub z y)))
                    (internal_paths_rew (add (add x (sub y x)) (sub z y))
                      (internal_paths_rew_r (add x (sub y x))
                        (add (sub y x) x)
                        (internal_paths_rew_r (add (sub y x) x) y
                          (internal_paths_rew_r (add y (sub z y))
                            (add (sub z y) y)
                            (internal_paths_rew_r (add (sub z y) y) z
                              (isreflnatleh z) (minusplusnmm z y a0))
                            (natpluscomm y (sub z y))) (minusplusnmm y x a))
                        (natpluscomm x (sub y x)))
                      (add x (add (sub y x) (sub z y)))
                      (natplusassoc x (sub y x) (sub z y)))
                    (natpluscomm (add (sub y x) (sub z y)) x))
                  (minusplusnmm z x u))) (nat_dist_le x z u))
            (nat_dist_le y z a0)
        | Coq_ii2 b ->
          internal_paths_rew_r (nat_dist y z) (sub y z)
            (let c1 = natleorle x z in
             match c1 with
             | Coq_ii1 a0 ->
               internal_paths_rew_r (nat_dist x z) (sub z x)
                 (natlehandplusrinv (sub z x) (add (sub y x) (sub y z)) x
                   (internal_paths_rew_r (add (sub z x) x) z
                     (internal_paths_rew_r (add (add (sub y x) (sub y z)) x)
                       (add x (add (sub y x) (sub y z)))
                       (internal_paths_rew (add (add x (sub y x)) (sub y z))
                         (internal_paths_rew_r (add x (sub y x))
                           (add (sub y x) x)
                           (internal_paths_rew_r (add (sub y x) x) y
                             (natlehandplusrinv z (add y (sub y z)) z
                               (internal_paths_rew_r
                                 (add (add y (sub y z)) z)
                                 (add y (add (sub y z) z))
                                 (internal_paths_rew_r (add (sub y z) z) y
                                   (istransnatleh (add z z) (add y z)
                                     (add y y) (natlehandplusr z y z b)
                                     (natlehandplusl z y y b))
                                   (minusplusnmm y z b))
                                 (natplusassoc y (sub y z) z)))
                             (minusplusnmm y x a)) (natpluscomm x (sub y x)))
                         (add x (add (sub y x) (sub y z)))
                         (natplusassoc x (sub y x) (sub y z)))
                       (natpluscomm (add (sub y x) (sub y z)) x))
                     (minusplusnmm z x a0))) (nat_dist_le x z a0)
             | Coq_ii2 b0 ->
               internal_paths_rew_r (nat_dist x z) (sub x z)
                 (natlehandplusrinv (sub x z) (add (sub y x) (sub y z)) z
                   (internal_paths_rew_r (add (sub x z) z) x
                     (internal_paths_rew_r (add (add (sub y x) (sub y z)) z)
                       (add (sub y x) (add (sub y z) z))
                       (internal_paths_rew_r (add (sub y z) z) y
                         (internal_paths_rew_r (add (sub y x) y)
                           (add y (sub y x))
                           (natlehandplusrinv x (add y (sub y x)) x
                             (internal_paths_rew_r (add (add y (sub y x)) x)
                               (add y (add (sub y x) x))
                               (internal_paths_rew_r (add (sub y x) x) y
                                 (istransnatleh (add x x) (add x y) (add y y)
                                   (natlehandplusl x y x a)
                                   (natlehandplusr x y y a))
                                 (minusplusnmm y x a))
                               (natplusassoc y (sub y x) x)))
                           (natpluscomm (sub y x) y)) (minusplusnmm y z b))
                       (natplusassoc (sub y x) (sub y z) z))
                     (minusplusnmm x z b0))) (nat_dist_ge x z b0))
            (nat_dist_ge y z b)) (nat_dist_le x y a)
   | Coq_ii2 b ->
     internal_paths_rew_r (nat_dist x y) (sub x y)
       (let c0 = natleorle z y in
        match c0 with
        | Coq_ii1 a ->
          let w = istransnatleh z y x a b in
          internal_paths_rew_r (nat_dist x z) (sub x z)
            (internal_paths_rew_r (nat_dist y z) (sub y z)
              (natlehandplusrinv (sub x z) (add (sub x y) (sub y z)) z
                (internal_paths_rew_r (add (sub x z) z) x
                  (internal_paths_rew_r (add (add (sub x y) (sub y z)) z)
                    (add (sub x y) (add (sub y z) z))
                    (internal_paths_rew_r (add (sub y z) z) y
                      (internal_paths_rew_r (add (sub x y) y) x
                        (isreflnatleh x) (minusplusnmm x y b))
                      (minusplusnmm y z a))
                    (natplusassoc (sub x y) (sub y z) z))
                  (minusplusnmm x z w))) (nat_dist_ge y z a))
            (nat_dist_ge x z w)
        | Coq_ii2 b0 ->
          internal_paths_rew_r (nat_dist y z) (sub z y)
            (let c1 = natleorle x z in
             match c1 with
             | Coq_ii1 a ->
               internal_paths_rew_r (nat_dist x z) (sub z x)
                 (natlehandplusrinv (sub z x) (add (sub x y) (sub z y)) x
                   (internal_paths_rew_r (add (sub z x) x) z
                     (natlehandpluslinv z (add (add (sub x y) (sub z y)) x) y
                       (internal_paths_rew_r
                         (add (add (sub x y) (sub z y)) x)
                         (add (sub x y) (add (sub z y) x))
                         (internal_paths_rew
                           (add (add y (sub x y)) (add (sub z y) x))
                           (internal_paths_rew_r (add y (sub x y))
                             (add (sub x y) y)
                             (internal_paths_rew_r (add (sub x y) y) x
                               (natlehandplusrinv (add y z)
                                 (add x (add (sub z y) x)) y
                                 (internal_paths_rew_r
                                   (add (add x (add (sub z y) x)) y)
                                   (add x (add (add (sub z y) x) y))
                                   (internal_paths_rew_r
                                     (add (add (sub z y) x) y)
                                     (add (sub z y) (add x y))
                                     (internal_paths_rew_r (add x y)
                                       (add y x)
                                       (internal_paths_rew
                                         (add (add (sub z y) y) x)
                                         (internal_paths_rew_r
                                           (add (sub z y) y) z
                                           (internal_paths_rew_r (add z x)
                                             (add x z)
                                             (internal_paths_rew
                                               (add (add x x) z)
                                               (internal_paths_rew_r
                                                 (add (add y z) y)
                                                 (add y (add z y))
                                                 (internal_paths_rew_r
                                                   (add z y) (add y z)
                                                   (internal_paths_rew
                                                     (add (add y y) z)
                                                     (natlehandplusr
                                                       (add y y) (add x x) z
                                                       (istransnatleh
                                                         (add y y) (add x y)
                                                         (add x x)
                                                         (natlehandplusr y x
                                                           y b)
                                                         (natlehandplusl y x
                                                           x b)))
                                                     (add y (add y z))
                                                     (natplusassoc y y z))
                                                   (natpluscomm z y))
                                                 (natplusassoc y z y))
                                               (add x (add x z))
                                               (natplusassoc x x z))
                                             (natpluscomm z x))
                                           (minusplusnmm z y b0))
                                         (add (sub z y) (add y x))
                                         (natplusassoc (sub z y) y x))
                                       (natpluscomm x y))
                                     (natplusassoc (sub z y) x y))
                                   (natplusassoc x (add (sub z y) x) y)))
                               (minusplusnmm x y b))
                             (natpluscomm y (sub x y)))
                           (add y (add (sub x y) (add (sub z y) x)))
                           (natplusassoc y (sub x y) (add (sub z y) x)))
                         (natplusassoc (sub x y) (sub z y) x)))
                     (minusplusnmm z x a))) (nat_dist_le x z a)
             | Coq_ii2 b1 ->
               internal_paths_rew_r (nat_dist x z) (sub x z)
                 (natlehandplusrinv (sub x z) (add (sub x y) (sub z y)) z
                   (internal_paths_rew_r (add (sub x z) z) x
                     (natlehandpluslinv x (add (add (sub x y) (sub z y)) z) y
                       (internal_paths_rew_r
                         (add (add (sub x y) (sub z y)) z)
                         (add (sub x y) (add (sub z y) z))
                         (internal_paths_rew
                           (add (add y (sub x y)) (add (sub z y) z))
                           (internal_paths_rew_r (add y (sub x y))
                             (add (sub x y) y)
                             (internal_paths_rew_r (add (sub x y) y) x
                               (natlehandplusrinv (add y x)
                                 (add x (add (sub z y) z)) y
                                 (internal_paths_rew_r
                                   (add (add x (add (sub z y) z)) y)
                                   (add x (add (add (sub z y) z) y))
                                   (internal_paths_rew_r
                                     (add (add (sub z y) z) y)
                                     (add (sub z y) (add z y))
                                     (internal_paths_rew_r (add z y)
                                       (add y z)
                                       (internal_paths_rew
                                         (add (add (sub z y) y) z)
                                         (internal_paths_rew_r
                                           (add (sub z y) y) z
                                           (internal_paths_rew_r (add y x)
                                             (add x y)
                                             (internal_paths_rew_r
                                               (add (add x y) y)
                                               (add x (add y y))
                                               (natlehandplusl (add y y)
                                                 (add z z) x
                                                 (istransnatleh (add y y)
                                                   (add z y) (add z z)
                                                   (natlehandplusr y z y b0)
                                                   (natlehandplusl y z z b0)))
                                               (natplusassoc x y y))
                                             (natpluscomm y x))
                                           (minusplusnmm z y b0))
                                         (add (sub z y) (add y z))
                                         (natplusassoc (sub z y) y z))
                                       (natpluscomm z y))
                                     (natplusassoc (sub z y) z y))
                                   (natplusassoc x (add (sub z y) z) y)))
                               (minusplusnmm x y b))
                             (natpluscomm y (sub x y)))
                           (add y (add (sub x y) (add (sub z y) z)))
                           (natplusassoc y (sub x y) (add (sub z y) z)))
                         (natplusassoc (sub x y) (sub z y) z)))
                     (minusplusnmm x z b1))) (nat_dist_ge x z b1))
            (nat_dist_le y z b0)) (nat_dist_ge x y b))

(** val plusmn0n0 : nat -> nat -> nat paths -> nat paths **)

let plusmn0n0 m n i =
  let a = natlehmplusnm m n in
  let a0 = internal_paths_rew (add m n) a O i in natleh0tois0 n a0

(** val plusmn0m0 : nat -> nat -> nat paths -> nat paths **)

let plusmn0m0 m n i =
  let a = natlehnplusnm m n in
  let a0 = internal_paths_rew (add m n) a O i in natleh0tois0 m a0

(** val natminus0le : nat -> nat -> nat paths -> hProptoType **)

let natminus0le m n _ =
  negnatgthtoleh m n (fun k -> let r = minusgth0 m n k in negnatgth0n O r)

(** val minusxx : nat -> nat paths **)

let rec minusxx = function
| O -> Coq_paths_refl
| S n0 -> minusxx n0

(** val minusSxx : nat -> nat paths **)

let rec minusSxx = function
| O -> Coq_paths_refl
| S n0 -> minusSxx n0

(** val natminusminus : nat -> nat -> hProptoType -> nat paths **)

let natminusminus n m i =
  let b = plusminusnmm m (sub n m) in
  let b0 =
    internal_paths_rew (add m (sub n m)) b (add (sub n m) m)
      (natpluscomm m (sub n m))
  in
  internal_paths_rew (add (sub n m) m) b0 n (minusplusnmm n m i)

(** val natplusminus : nat -> nat -> nat -> nat paths -> nat paths **)

let natplusminus m n k i =
  internal_paths_rew_r k (add m n) (plusminusnmm m n) i

(** val natleplusminus : nat -> nat -> nat -> hProptoType -> hProptoType **)

let natleplusminus k m n i =
  natlehandplusrinv k (sub n m) m
    (internal_paths_rew_r (add (sub n m) m) n i
      (minusplusnmm n m (istransnatleh m (add k m) n (natlehmplusnm k m) i)))

(** val natltminus1 : nat -> nat -> hProptoType -> hProptoType **)

let natltminus1 m n i =
  let a = natlthp1toleh m (sub n (S O)) in
  let b = natleh0n m in
  let c = natlehlthtrans O m n b i in
  let d = natlthtolehsn O n c in
  let e = minusplusnmm n (S O) d in
  internal_paths_rew (add (sub n (S O)) (S O)) a n e i

(** val natminusminusassoc : nat -> nat -> nat -> nat paths **)

let rec natminusminusassoc m n k =
  match m with
  | O -> Coq_paths_refl
  | S n0 ->
    (match n with
     | O ->
       internal_paths_rew_r (sub (S n0) O) (S n0) Coq_paths_refl
         (natminuseqn (S n0))
     | S n1 -> natminusminusassoc n0 n1 k)

(** val natminusplusltcomm :
    nat -> nat -> nat -> hProptoType -> hProptoType -> hProptoType **)

let natminusplusltcomm m n k i p =
  let a = natlehandplusr m (sub n k) k p in
  let b = minusplusnmm n k i in
  let a0 = internal_paths_rew (add (sub n k) k) a n b in
  natleplusminus k m n
    (internal_paths_rew_r (add k m) (add m k) a0 (natpluscomm k m))

(** val nat_le_diff :
    _UU2115_ -> _UU2115_ -> hProptoType -> (_UU2115_, nat paths) total2 **)

let nat_le_diff n m p =
  { pr1 = (sub m n); pr2 =
    (internal_paths_rew_r (add n (sub m n)) (add (sub m n) n)
      (minusplusnmm m n p) (natpluscomm n (sub m n))) }

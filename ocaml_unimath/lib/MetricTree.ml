open Nat
open NaturalNumbers
open PartA
open PartB
open Preamble
open Propositions

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type coq_Tree =
  (__,
   (__ -> __ -> nat,        
    (__ -> nat paths,
     (__ -> __ -> nat paths -> __        paths,
      (__ -> __ -> nat paths,
       (__ -> __ -> __ -> hProptoType, __ -> __ ->            __ paths neg ->  (__, (nat paths, nat paths) dirprod) total2)
         total2)
        total2)
       total2)
      total2)
     total2)
    total2
    
type mt_set = __

(** val mt_dist : coq_Tree -> __ -> __ -> nat **)

let mt_dist x =
  x.pr2.pr1

(** val mt_refl : coq_Tree -> __ -> nat paths **)

let mt_refl x =
  x.pr2.pr2.pr1

(** val mt_anti : coq_Tree -> __ -> __ -> nat paths -> __ paths **)

let mt_anti x =
  x.pr2.pr2.pr2.pr1

(** val mt_symm : coq_Tree -> __ -> __ -> nat paths **)

let mt_symm x =
  x.pr2.pr2.pr2.pr2.pr1

(** val mt_trans : coq_Tree -> __ -> __ -> __ -> hProptoType **)

let mt_trans x =
  x.pr2.pr2.pr2.pr2.pr2.pr1

(** val mt_step :
    coq_Tree -> __ -> __ -> __ paths neg -> (__, (nat paths, nat paths)
    dirprod) total2 **)

let mt_step x =
  x.pr2.pr2.pr2.pr2.pr2.pr2

(** val make :
    ('a1 -> 'a1 -> nat) -> ('a1 -> nat paths) -> ('a1 -> 'a1 -> nat paths ->
    'a1 paths) -> ('a1 -> 'a1 -> nat paths) -> ('a1 -> 'a1 -> 'a1 ->
    hProptoType) -> ('a1 -> 'a1 -> 'a1 paths neg -> ('a1, (nat paths, nat
    paths) dirprod) total2) -> coq_Tree **)

let make mt_dist0 mt_refl0 mt_anti0 mt_symm0 mt_trans0 mt_step0 =
  { pr1 = __; pr2 = { pr1 = (Obj.magic mt_dist0); pr2 = { pr1 =
    (Obj.magic mt_refl0); pr2 = { pr1 = (Obj.magic mt_anti0); pr2 = { pr1 =
    (Obj.magic mt_symm0); pr2 = { pr1 = (Obj.magic mt_trans0); pr2 =
    (Obj.magic mt_step0) } } } } } }

(** val mt_path_refl :
    coq_Tree -> mt_set -> mt_set -> mt_set paths -> nat paths **)

let mt_path_refl t x _ _ =
  mt_refl t x

(** val tree_deceq : coq_Tree -> mt_set isdeceq **)

let tree_deceq t t0 u = t
  (* let d = isdeceqnat (mt_dist t t0 u) O in *)
  (* (match d with *)
  (*  | Coq_ii1 a -> Coq_ii1 (mt_anti t t0 u a) *)
  (*  | Coq_ii2 b -> Coq_ii2 (fun _ -> b (mt_refl t t0))) *)

(** val tree_isaset : coq_Tree -> mt_set isaset **)

let tree_isaset t =
  isasetifdeceq (tree_deceq t)

(** val step : coq_Tree -> mt_set -> mt_set -> mt_set paths neg -> mt_set **)

let step t x z ne =
  (mt_step t x z ne).pr1

(** val tree_induction :
    coq_Tree -> mt_set -> 'a1 -> (mt_set -> mt_set paths neg -> 'a1 -> 'a1)
    -> mt_set -> 'a1 **)

let tree_induction t x p0 pn = t
  (* let d_ind = fun n -> *)
  (*   let rec f n0 z x0 = *)
  (*     match n0 with *)
  (*     | O -> p0 *)
  (*     | S n1 -> *)
  (*       let ne = fun s -> *)
  (*         negpaths0sx n1 *)
  (*           (pathscomp0 O (mt_dist t x z) (S n1) *)
  (*             (pathsinv0 (mt_dist t x z) O (mt_path_refl t x z s)) x0) *)
  (*       in *)
  (*       pn z ne *)
  (*         (f n1 (step t x z ne) *)
  (*           (let y = mt_step t x z ne in *)
  (*            let y0 = y.pr1 in *)
  (*            let pr3 = y.pr2 in *)
  (*            let i = pr3.pr1 in *)
  (*            invmaponpathsS (mt_dist t x y0) n1 *)
  (*              (pathscomp0 (S (t.pr2.pr1 x y0)) (t.pr2.pr1 x z) (S n1) i x0))) *)
  (*   in f n *)
  (* in *)
  (* (fun z -> d_ind (mt_dist t x z) z Coq_paths_refl) *)

(** val nat_tree : coq_Tree **)

(* (\* val nat_tree : coq_Tree *)
(* *\) *)
(* let nat_tree = false *)
  (* make nat_dist (fun m -> *)
  (*   let rec f = function *)
  (*   | O -> Coq_paths_refl *)
  (*   | S n0 -> *)
  (*     internal_paths_rew_r (nat_dist (S n0) (S n0)) (nat_dist n0 n0)  *)
  (*       (f n0) (nat_dist_S n0 n0) *)
  (*   in f m) Discern.nat_dist_anti nat_dist_symm nat_dist_trans (fun m n e -> *)
  (*   let d = natneqchoice m n (nat_nopath_to_neq m n e) in *)
  (*   (match d with *)
  (*    | Coq_ii1 h -> *)
  (*      { pr1 = (S n); pr2 = { pr1 = (nat_dist_gt m n h); pr2 = *)
  (*        (let c = natgthorleh (S n) n in *)
  (*         match c with *)
  (*         | Coq_ii1 _ -> *)
  (*           let rec f = function *)
  (*           | O -> Coq_paths_refl *)
  (*           | S n1 -> f n1 *)
  (*           in f n *)
  (*         | Coq_ii2 _ -> fromempty (assert false (\* absurd case *\))) } } *)
  (*    | Coq_ii2 h -> *)
  (*      { pr1 = (sub n (S O)); pr2 = { pr1 = *)
  (*        (let a = natltminus1 m n h in *)
  (*         let b = natlthtoleh m n h in *)
  (*         let c = nat_dist_le m (sub n (S O)) a in *)
  (*         let d0 = nat_dist_le m n b in *)
  (*         internal_paths_rew_r (nat_dist m (sub n (S O))) *)
  (*           (sub (sub n (S O)) m) *)
  (*           (internal_paths_rew_r (nat_dist m n) (sub n m) *)
  (*             (internal_paths_rew_r (sub (sub n (S O)) m) *)
  (*               (sub n (add (S O) m)) *)
  (*               (internal_paths_rew_r (add (S O) m) (add m (S O)) *)
  (*                 (internal_paths_rew (sub (sub n m) (S O)) *)
  (*                   (internal_paths_rew_r (add (S O) (sub (sub n m) (S O))) *)
  (*                     (add (sub (sub n m) (S O)) (S O)) *)
  (*                     (minusplusnmm (sub n m) (S O) *)
  (*                       (natminusplusltcomm m n (S O) *)
  (*                         (let e0 = natleh0n m in *)
  (*                          let f = natlehlthtrans O m n e0 h in *)
  (*                          natlthtolehsn O n f) a)) *)
  (*                     (natpluscomm (S O) (sub (sub n m) (S O)))) *)
  (*                   (sub n (add m (S O))) (natminusminusassoc n m (S O))) *)
  (*                 (natpluscomm (S O) m)) (natminusminusassoc n (S O) m)) d0) c); *)
  (*        pr2 = *)
  (*        (let a = natleh0n m in *)
  (*         let b = natlehlthtrans O m n a h in *)
  (*         let c = natlthtolehsn O n b in nat_dist_minus (S O) n c) } })) *)

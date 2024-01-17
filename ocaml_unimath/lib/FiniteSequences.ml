open FiniteSets
open Lists
open NaturalNumbers
open PartA
open PartA0
open PartB
open PartD
open Preamble
open Propositions
open Sets
open StandardFiniteSets
open UnivalenceAxiom
open Vectors

type __ = Obj.t

type 'x coq_Vector = stn -> 'x

(** val vector_hlevel :
    nat -> nat -> 'a1 isofhlevel -> 'a1 coq_Vector isofhlevel **)

let vector_hlevel _ m ism =
  impred m (fun _ -> ism)

(** val const_vec : nat -> 'a1 -> 'a1 coq_Vector **)

let const_vec _ x _ =
  x

(** val iscontr_vector_0 : 'a1 coq_Vector iscontr **)

let iscontr_vector_0 =
  iscontrweqb (invweq (weqbfun weqstn0toempty)) iscontrfunfromempty

(** val empty_vec : 'a1 coq_Vector **)

let empty_vec x =
  iscontrpr1 iscontr_vector_0 x

(** val _1 : ('a1, 'a1 coq_Vector) weq **)


(** val append_vec : nat -> 'a1 coq_Vector -> 'a1 -> 'a1 coq_Vector **)

let append_vec n vec x i =
  let c = natlehchoice4 i.pr1 n i.pr2 in
  (match c with
   | Coq_ii1 a -> vec { pr1 = i.pr1; pr2 = a }
   | Coq_ii2 _ -> x)

(** val append_vec_compute_1 :
    nat -> 'a1 coq_Vector -> 'a1 -> stn -> 'a1 paths **)

let append_vec_compute_1 n vec _ i =
  let i0 = i.pr1 in
  let b = i.pr2 in
  internal_paths_rew_r (dni n (lastelement n)) (dni_lastelement n)
    (let c = natlehchoice4 i0 n (natlthtolths i0 n b) in
     match c with
     | Coq_ii1 a ->
       maponpaths vec { pr1 = i0; pr2 = a } { pr1 = i0; pr2 = b }
         (Obj.magic isinjstntonat n { pr1 = i0; pr2 = a } { pr1 = i0; pr2 =
           b } Coq_paths_refl)
     | Coq_ii2 _ -> assert false (* absurd case *)) (replace_dni_last n)

(** val append_vec_compute_2 : nat -> 'a1 coq_Vector -> 'a1 -> 'a1 paths **)

let append_vec_compute_2 n _ _ =
  let c = natlehchoice4 n n (natgthsnn n) in
  (match c with
   | Coq_ii1 _ -> assert false (* absurd case *)
   | Coq_ii2 _ -> Coq_paths_refl)

(** val drop_and_append_vec :
    nat -> 'a1 coq_Vector -> 'a1 coq_Vector paths **)

let drop_and_append_vec n x =
  Obj.magic funextfun
    (append_vec n (funcomp (dni_lastelement n) x) (x (lastelement n))) x
    (fun x0 ->
    let i = (Obj.magic x0).pr1 in
    let b = (Obj.magic x0).pr2 in
    let c = natlehchoice4 i n b in
    (match c with
     | Coq_ii1 _ ->
       let c0 = natlehchoice4 i n b in
       (match c0 with
        | Coq_ii1 a ->
          maponpaths (Obj.magic x) (dni_lastelement n { pr1 = i; pr2 = a })
            { pr1 = i; pr2 = b }
            (Obj.magic isinjstntonat (S n)
              (dni_lastelement n { pr1 = i; pr2 = a }) { pr1 = i; pr2 = b }
              Coq_paths_refl)
        | Coq_ii2 _ -> assert false (* absurd case *))
     | Coq_ii2 _ ->
       let c0 = natlehchoice4 i i b in
       (match c0 with
        | Coq_ii1 a ->
          maponpaths (Obj.magic x) (dni_lastelement i { pr1 = i; pr2 = a })
            { pr1 = i; pr2 = b }
            (Obj.magic isinjstntonat (S i)
              (dni_lastelement i { pr1 = i; pr2 = a }) { pr1 = i; pr2 = b }
              Coq_paths_refl)
        | Coq_ii2 _ ->
          maponpaths (Obj.magic x) (lastelement i) { pr1 = i; pr2 = b }
            (Obj.magic isinjstntonat (S i) (lastelement i) { pr1 = i; pr2 =
              b } Coq_paths_refl))))

(** val coq_Vector_rect :
    'a2 -> (nat -> 'a1 coq_Vector -> 'a1 -> 'a2 -> 'a2) -> nat -> 'a1
    coq_Vector -> 'a2 **)

let rec coq_Vector_rect p0 ind n vec =
  match n with
  | O ->
    transportf empty_vec vec
      (proofirrelevancecontr iscontr_vector_0 empty_vec vec) p0
  | S n0 ->
    transportf
      (append_vec n0 (funcomp (dni_lastelement n0) vec)
        (vec (lastelement n0))) vec (drop_and_append_vec n0 vec)
      (ind n0 (funcomp (dni_lastelement n0) vec) (vec (lastelement n0))
        (coq_Vector_rect p0 ind n0 (funcomp (dni_lastelement n0) vec)))

(** val vectorEquality :
    nat -> nat -> 'a1 coq_Vector -> 'a1 coq_Vector -> nat paths -> (stn ->
    'a1 paths) -> 'a1 coq_Vector paths **)

let vectorEquality n _ f g _ x0 =
  Obj.magic funextfun (transportf n n Coq_paths_refl (Obj.magic f)) g x0

(** val tail : nat -> 'a1 coq_Vector -> 'a1 coq_Vector **)

let tail n vecsn =
  funcomp (dni n { pr1 = O; pr2 = (natgthsn0 n) }) vecsn

(** val vector_stn_proofirrelevance :
    nat -> 'a1 coq_Vector -> stn -> stn -> nat paths -> 'a1 paths **)

let vector_stn_proofirrelevance n vec i j x0 =
  maponpaths vec i j (Obj.magic isinjstntonat n i j x0)

type 'x coq_Matrix = 'x coq_Vector coq_Vector

(** val transpose : nat -> nat -> 'a1 coq_Matrix -> 'a1 coq_Matrix **)

let transpose _ _ =
  flipsec

(** val row : nat -> nat -> 'a1 coq_Matrix -> stn -> 'a1 coq_Vector **)

let row _ _ mat =
  mat

(** val col : nat -> nat -> 'a1 coq_Matrix -> stn -> 'a1 coq_Vector **)

let col m n mat =
  transpose n m mat

(** val row_vec : nat -> 'a1 coq_Vector -> 'a1 coq_Matrix **)

let row_vec _ vec _ =
  vec

(** val col_vec : nat -> 'a1 coq_Vector -> 'a1 coq_Matrix **)

let col_vec _ vec i _ =
  vec i

(** val matrix_hlevel :
    nat -> nat -> nat -> 'a1 isofhlevel -> 'a1 coq_Matrix isofhlevel **)

let matrix_hlevel n m o ism =
  vector_hlevel n o (vector_hlevel m o ism)

(** val const_matrix : nat -> nat -> 'a1 -> 'a1 coq_Matrix **)

let const_matrix n m x =
  const_vec n (const_vec m x)

(** val weq_matrix_1_1 : ('a1, 'a1 coq_Matrix) weq **)

(* let weq_matrix_1_1 = *)
(*   weqcomp weq_vector_1 weq_vector_1 *)

type 'x coq_Sequence = (nat, 'x coq_Vector) total2

type 'x coq_NonemptySequence = (nat, stn -> 'x) total2

type 'x coq_UnorderedSequence = (coq_FiniteSet, pr1hSet -> 'x) total2

(** val length : 'a1 coq_Sequence -> nat **)

let length x =
  x.pr1

(** val sequenceToFunction : 'a1 coq_Sequence -> stn -> 'a1 **)

let sequenceToFunction x =
  x.pr2

(** val unorderedSequenceToFunction :
    'a1 coq_UnorderedSequence -> __ -> 'a1 **)

let unorderedSequenceToFunction x =
  x.pr2

(** val sequenceToUnorderedSequence :
    'a1 coq_Sequence -> 'a1 coq_UnorderedSequence **)

let sequenceToUnorderedSequence x =
  { pr1 = (standardFiniteSet (length x)); pr2 =
    (Obj.magic sequenceToFunction x) }

(** val length' : 'a1 coq_NonemptySequence -> nat **)

let length' x =
  S x.pr1

(** val functionToSequence : nat -> (stn -> 'a1) -> 'a1 coq_Sequence **)

let functionToSequence n f =
  { pr1 = n; pr2 = f }

(** val functionToUnorderedSequence :
    coq_FiniteSet -> (pr1hSet -> 'a1) -> 'a1 coq_UnorderedSequence **)

let functionToUnorderedSequence i f =
  { pr1 = i; pr2 = f }

(** val coq_NonemptySequenceToFunction :
    'a1 coq_NonemptySequence -> stn -> 'a1 **)

let coq_NonemptySequenceToFunction x =
  x.pr2

(** val coq_NonemptySequenceToSequence :
    'a1 coq_NonemptySequence -> 'a1 coq_Sequence **)

let coq_NonemptySequenceToSequence x =
  functionToSequence (length' x) (coq_NonemptySequenceToFunction x)

(** val composeSequence :
    ('a1 -> 'a2) -> 'a1 coq_Sequence -> 'a2 coq_Sequence **)

let composeSequence f x =
  functionToSequence (length x) (funcomp (sequenceToFunction x) f)

(** val composeSequence' :
    nat -> nat -> (stn -> 'a1) -> (stn -> stn) -> 'a1 coq_Sequence **)

let composeSequence' m _ f g =
  functionToSequence m (funcomp g f)

(** val composeUnorderedSequence :
    ('a1 -> 'a2) -> 'a1 coq_UnorderedSequence -> 'a2 coq_UnorderedSequence **)

let composeUnorderedSequence f x =
  functionToUnorderedSequence x.pr1
    (funcomp (unorderedSequenceToFunction x) f)

(** val weqListSequence : ('a1 list, 'a1 coq_Sequence) weq **)

let weqListSequence =
  weqfibtototal weqvecfun

(** val transport_stn :
    nat -> nat -> nat -> hProptoType -> nat paths -> stn paths **)

let transport_stn _ _ _ _ _ =
  Coq_paths_refl

(** val sequenceEquality2 :
    'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> (stn -> 'a1 paths)
    -> 'a1 coq_Sequence paths **)

let sequenceEquality2 f g p e =
  let m = f.pr1 in
  let f0 = f.pr2 in
  let n = g.pr1 in
  let g0 = g.pr2 in total2_paths2_f m f0 n g0 p (vectorEquality m n f0 g0 p e)

(** val seq_key_eq_lemma :
    'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> (nat -> hProptoType
    -> hProptoType -> 'a1 paths) -> 'a1 coq_Sequence paths **)

let seq_key_eq_lemma g g' e_len e_el =
  let m = g.pr1 in
  let g0 = g.pr2 in
  let m' = g'.pr1 in
  let g'0 = g'.pr2 in
  pathscomp0 { pr1 = m; pr2 = g0 } { pr1 = m'; pr2 =
    (transportf m m' e_len g0) } { pr1 = m'; pr2 = g'0 }
    (transportf_eq m m' e_len g0)
    (maponpaths (Obj.magic (fun x -> { pr1 = m'; pr2 = x }))
      (transportf m m' e_len (Obj.magic g0)) (Obj.magic g'0)
      (pathscomp0 (transportf m m' e_len (Obj.magic g0))
        (funcomp (Obj.magic transportb m m' e_len) (Obj.magic g0))
        (Obj.magic g'0) (transportf_fun m m' e_len (Obj.magic g0))
        (funextfun (funcomp (Obj.magic transportb m m' e_len) (Obj.magic g0))
          (Obj.magic g'0) (fun x ->
          let i = (Obj.magic x).pr1 in
          let b = (Obj.magic x).pr2 in
          pathscomp0
            (funcomp (transportb m m' e_len) (Obj.magic g0) { pr1 = i; pr2 =
              b })
            (Obj.magic g0 { pr1 = i; pr2 =
              (transportf m' m (pathsinv0 m m' e_len) b) })
            (Obj.magic g'0 { pr1 = i; pr2 = b })
            (maponpaths (Obj.magic g0)
              (transportb m m' e_len { pr1 = i; pr2 = b }) { pr1 = i; pr2 =
              (transportf m' m (pathsinv0 m m' e_len) b) }
              (transport_stn m' m i b (pathsinv0 m m' e_len)))
            (Obj.magic e_el i (transportf m' m (pathsinv0 m m' e_len) b) b)))))

(** val seq_key_eq_lemma' :
    'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> (nat ->
    (hProptoType, (hProptoType, 'a1 paths) total2) total2) -> 'a1
    coq_Sequence paths **)

let seq_key_eq_lemma' g g' k r =
  seq_key_eq_lemma g g' k (fun i ltg ltg' ->
    let t = r i in
    let p = t.pr1 in
    let pr3 = t.pr2 in
    let q = pr3.pr1 in
    let e = pr3.pr2 in
    pathscomp0 (sequenceToFunction g { pr1 = i; pr2 = ltg })
      (sequenceToFunction g { pr1 = i; pr2 = p })
      (sequenceToFunction g' { pr1 = i; pr2 = ltg' })
      (maponpaths (sequenceToFunction g) { pr1 = i; pr2 = ltg } { pr1 = i;
        pr2 = p }
        (Obj.magic isinjstntonat (length g) { pr1 = i; pr2 = ltg } { pr1 = i;
          pr2 = p } Coq_paths_refl))
      (pathscomp0 (sequenceToFunction g { pr1 = i; pr2 = p })
        (sequenceToFunction g' { pr1 = i; pr2 = q })
        (sequenceToFunction g' { pr1 = i; pr2 = ltg' }) e
        (maponpaths (sequenceToFunction g') { pr1 = i; pr2 = q } { pr1 = i;
          pr2 = ltg' }
          (Obj.magic isinjstntonat (length g') { pr1 = i; pr2 = q } { pr1 =
            i; pr2 = ltg' } Coq_paths_refl))))

(** val nil : 'a1 coq_Sequence **)

let nil =
  { pr1 = O; pr2 = empty_vec }

(** val append : 'a1 coq_Sequence -> 'a1 -> 'a1 coq_Sequence **)

let append x y =
  { pr1 = (S (length x)); pr2 = (append_vec x.pr1 x.pr2 y) }

(** val drop_and_append : nat -> (stn -> 'a1) -> 'a1 coq_Sequence paths **)

let drop_and_append n x =
  pair_path_in2 (S n)
    (append_vec n (funcomp (dni_lastelement n) x) (x (lastelement n))) x
    (drop_and_append_vec n x)

(** val nil_unique : (stn -> 'a1) -> 'a1 coq_Sequence paths **)

let nil_unique x =
  maponpaths (fun x0 -> { pr1 = O; pr2 = x0 }) empty_vec x
    (Obj.magic isapropifcontr iscontr_vector_0 empty_vec x).pr1

(** val iscontr_rect' : 'a1 iscontr -> 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let iscontr_rect' _ _ p0 _ =
  p0

(** val iscontr_rect_compute' : 'a1 iscontr -> 'a1 -> 'a2 -> 'a2 paths **)

let iscontr_rect_compute' _ _ _ =
  Coq_paths_refl

(** val iscontr_rect'' : 'a1 iscontr -> 'a2 -> 'a1 -> 'a2 **)


(** val iscontr_rect_compute'' : 'a1 iscontr -> 'a2 -> 'a2 paths **)


(** val iscontr_adjointness : 'a1 iscontr -> 'a1 -> 'a1 paths paths **)

let iscontr_adjointness is x =
  let x0 = (Obj.magic isapropifcontr is x x).pr1 in
  let x' = Coq_paths_refl in (Obj.magic isasetifcontr is x x x0 x').pr1

(** val iscontr_rect : 'a1 iscontr -> 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let iscontr_rect is x0 p0 x =
  transportf x0 x (Obj.magic isapropifcontr is x0 x).pr1 p0

(** val iscontr_rect_compute : 'a1 iscontr -> 'a1 -> 'a2 -> 'a2 paths **)

let iscontr_rect_compute is x _ =
  internal_paths_rew_r (Obj.magic isapropifcontr is x x).pr1 Coq_paths_refl
    Coq_paths_refl (iscontr_adjointness is x)

(** val weqsecovercontr' : 'a1 iscontr -> ('a1 -> 'a2, 'a2) weq **)

let weqsecovercontr' is =
  let x0 = is.pr1 in
  let destr = fun f -> f x0 in
  let constr = iscontr_rect is x0 in
  { pr1 = destr; pr2 =
  (isweq_iso destr constr (fun f ->
    Obj.magic funextsec (Obj.magic constr (destr f)) f (fun x ->
      transport_section (Obj.magic f) (Obj.magic x0) x
        (Obj.magic isapropifcontr is x0 x).pr1)) (iscontr_rect_compute is x0)) }

(** val nil_length :
    'a1 coq_Sequence -> (nat paths, 'a1 coq_Sequence paths) logeq **)

let nil_length x =
  { pr1 = (fun _ ->
    let x0 = x.pr2 in pathsinv0 nil { pr1 = O; pr2 = x0 } (nil_unique x0));
    pr2 = (fun _ -> Coq_paths_refl) }

(** val drop : 'a1 coq_Sequence -> nat paths neg -> 'a1 coq_Sequence **)

let drop x =
  let n = x.pr1 in
  let x0 = x.pr2 in
  (fun _ ->
  match n with
  | O -> assert false (* absurd case *)
  | S n0 -> { pr1 = n0; pr2 = (funcomp (dni_lastelement n0) x0) })

(** val drop' :
    'a1 coq_Sequence -> 'a1 coq_Sequence paths neg -> 'a1 coq_Sequence **)

let drop' x h =
  drop x ((logeqnegs (nil_length x)).pr2 h)

(** val append_and_drop_fun :
    nat -> (stn -> 'a1) -> 'a1 -> (stn -> 'a1) paths **)

let append_and_drop_fun n x y =
  Obj.magic funextsec
    (funcomp (Obj.magic dni n (lastelement n))
      (append_vec n (Obj.magic x) (Obj.magic y))) x (fun i ->
    let c =
      natlehchoice4 (dni n (lastelement n) (Obj.magic i)).pr1 n
        (dni n (lastelement n) (Obj.magic i)).pr2
    in
    (match c with
     | Coq_ii1 a ->
       maponpaths (Obj.magic x) { pr1 = (di n (stntonat n (Obj.magic i)));
         pr2 = a } (Obj.magic i)
         (subtypePath_prop (fun x0 -> natlth x0 n) { pr1 =
           (di n (stntonat n (Obj.magic i))); pr2 = a } (Obj.magic i)
           (di_eq1 n (stntonat n (Obj.magic i)) (stnlt n (Obj.magic i))))
     | Coq_ii2 _ ->
       fromempty
         (let i0 = (Obj.magic i).pr1 in
          let r = (Obj.magic i).pr2 in isirreflnatlth i0 r)))

(** val drop_and_append' : nat -> (stn -> 'a1) -> 'a1 coq_Sequence paths **)

let drop_and_append' n x =
  pair_path_in2 (S n)
    (append_vec (drop { pr1 = (S n); pr2 = x } (negpathssx0 n)).pr1
      (drop { pr1 = (S n); pr2 = x } (negpathssx0 n)).pr2 (x (lastelement n)))
    x (drop_and_append_vec n x)

(** val disassembleSequence :
    'a1 coq_Sequence -> (coq_unit, ('a1, 'a1 coq_Sequence) dirprod) coprod **)

let disassembleSequence x =
  let n = x.pr1 in
  let x0 = x.pr2 in
  (match n with
   | O -> Coq_ii1 Coq_tt
   | S n0 ->
     Coq_ii2 { pr1 = (x0 (lastelement n0)); pr2 = { pr1 = n0; pr2 =
       (funcomp (dni_lastelement n0) x0) } })

(** val assembleSequence :
    (coq_unit, ('a1, 'a1 coq_Sequence) dirprod) coprod -> 'a1 coq_Sequence **)

let assembleSequence = function
| Coq_ii1 _ -> nil
| Coq_ii2 b -> append b.pr2 b.pr1

(** val assembleSequence_ii2 :
    ('a1, 'a1 coq_Sequence) dirprod -> 'a1 coq_Sequence paths **)

let assembleSequence_ii2 _ =
  Coq_paths_refl

(** val coq_SequenceAssembly :
    ('a1 coq_Sequence, (coq_unit, ('a1, 'a1 coq_Sequence) dirprod) coprod) weq **)

let coq_SequenceAssembly =
  { pr1 = disassembleSequence; pr2 =
    (isweq_iso disassembleSequence assembleSequence (fun x ->
      let n = x.pr1 in
      let x0 = x.pr2 in
      (match n with
       | O -> nil_unique x0
       | S n0 -> drop_and_append' n0 x0)) (fun co ->
      match co with
      | Coq_ii1 a ->
        maponpaths (fun x -> Coq_ii1 x) Coq_tt a
          (proofirrelevancecontr iscontrunit Coq_tt a)
      | Coq_ii2 b ->
        let x = b.pr1 in
        let y = b.pr2 in
        let n = y.pr1 in
        let y0 = y.pr2 in
        maponpaths (Obj.magic (fun x0 -> Coq_ii2 x0)) { pr1 =
          ((assembleSequence (Coq_ii2 { pr1 = x; pr2 = { pr1 = n; pr2 =
             y0 } })).pr2 (lastelement (length { pr1 = n; pr2 = y0 })));
          pr2 = { pr1 = (length { pr1 = n; pr2 = y0 }); pr2 =
          (funcomp (Obj.magic dni_lastelement (length { pr1 = n; pr2 = y0 }))
            (assembleSequence (Coq_ii2 { pr1 = (Obj.magic x); pr2 = { pr1 =
              n; pr2 = (Obj.magic y0) } })).pr2) } } { pr1 = x; pr2 = { pr1 =
          n; pr2 = (Obj.magic y0) } }
          (let c = natlehchoice4 n n (natgthsnn n) in
           match c with
           | Coq_ii1 _ -> assert false (* absurd case *)
           | Coq_ii2 _ ->
             maponpaths (fun x0 -> { pr1 = x; pr2 = x0 }) { pr1 = n; pr2 =
               (funcomp (Obj.magic dni_lastelement n) (fun i ->
                 match natlehchoice4 i.pr1 n i.pr2 with
                 | Coq_ii1 a -> Obj.magic y0 { pr1 = i.pr1; pr2 = a }
                 | Coq_ii2 _ -> Obj.magic x)) } { pr1 = n; pr2 =
               (Obj.magic y0) }
               (maponpaths (fun x0 -> { pr1 = n; pr2 = x0 })
                 (funcomp (Obj.magic dni_lastelement n) (fun i ->
                   match natlehchoice4 i.pr1 n i.pr2 with
                   | Coq_ii1 a -> Obj.magic y0 { pr1 = i.pr1; pr2 = a }
                   | Coq_ii2 _ -> Obj.magic x)) (Obj.magic y0)
                 (funextfun
                   (funcomp (Obj.magic dni_lastelement n) (fun i ->
                     match natlehchoice4 i.pr1 n i.pr2 with
                     | Coq_ii1 a -> Obj.magic y0 { pr1 = i.pr1; pr2 = a }
                     | Coq_ii2 _ -> Obj.magic x)) (Obj.magic y0) (fun i ->
                   let i0 = (Obj.magic i).pr1 in
                   let b0 = (Obj.magic i).pr2 in
                   let c0 = natlehchoice4 i0 n (natlthtolths i0 n b0) in
                   (match c0 with
                    | Coq_ii1 a ->
                      maponpaths (Obj.magic y0) { pr1 = i0; pr2 = a } { pr1 =
                        i0; pr2 = b0 }
                        (Obj.magic isinjstntonat n { pr1 = i0; pr2 = a }
                          { pr1 = i0; pr2 = b0 } Coq_paths_refl)
                    | Coq_ii2 _ -> assert false (* absurd case *)))))))) }

(** val coq_Sequence_rect :
    'a2 -> ('a1 coq_Sequence -> 'a1 -> 'a2 -> 'a2) -> 'a1 coq_Sequence -> 'a2 **)

let coq_Sequence_rect p0 ind x =
  let n = x.pr1 in
  let x0 = x.pr2 in
  let rec f n0 x1 =
    match n0 with
    | O -> transportf nil { pr1 = O; pr2 = x1 } (nil_unique x1) p0
    | S n1 ->
      transportf
        (append { pr1 = n1; pr2 = (funcomp (dni_lastelement n1) x1) }
          (x1 (lastelement n1))) { pr1 = (S n1); pr2 = x1 }
        (drop_and_append n1 x1)
        (ind { pr1 = n1; pr2 = (funcomp (dni_lastelement n1) x1) }
          (x1 (lastelement n1)) (f n1 (funcomp (dni_lastelement n1) x1)))
  in f n x0

(** val coq_Sequence_rect_compute_nil :
    'a2 -> ('a1 coq_Sequence -> 'a1 -> 'a2 -> 'a2) -> 'a2 paths **)

let coq_Sequence_rect_compute_nil p0 _ =
  maponpaths (fun e -> transportf nil nil e p0) (nil_unique empty_vec)
    Coq_paths_refl
    (maponpaths (maponpaths (functionToSequence O) empty_vec empty_vec)
      (Obj.magic isapropifcontr iscontr_vector_0 empty_vec empty_vec).pr1
      Coq_paths_refl (iscontr_adjointness iscontr_vector_0 empty_vec))

(** val append_length : 'a1 coq_Sequence -> 'a1 -> nat paths **)

let append_length _ _ =
  Coq_paths_refl

(** val concatenate : 'a1 coq_Sequence binop **)

let concatenate x y =
  functionToSequence (add (length x) (length y))
    (concatenate' (length x) (length y) (sequenceToFunction x)
      (sequenceToFunction y))

(** val concatenate_length :
    'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths **)

let concatenate_length _ _ =
  Coq_paths_refl

(** val concatenate_0 :
    'a1 coq_Sequence -> 'a1 coq_Sequence -> nat paths -> 'a1 coq_Sequence
    paths **)

let concatenate_0 s t =
  let m = s.pr1 in
  let s0 = s.pr2 in
  let t0 = t.pr2 in
  (fun _ ->
  sequenceEquality2 (concatenate { pr1 = m; pr2 = s0 } { pr1 = O; pr2 = t0 })
    { pr1 = m; pr2 = s0 } (natplusr0 m) (fun i ->
    internal_paths_rew_r (weqfromcoprodofstn_invmap m O i) (Coq_ii1
      (transportf (add m O) m (natplusr0 m) i)) Coq_paths_refl
      (weqfromcoprodofstn_invmap_r0 m i)))

(** val concatenateStep :
    'a1 coq_Sequence -> nat -> (stn -> 'a1) -> 'a1 coq_Sequence paths **)

let concatenateStep x n y =
  let m = x.pr1 in
  let l = x.pr2 in
  seq_key_eq_lemma
    (concatenate { pr1 = m; pr2 = l } { pr1 = (S n); pr2 = y })
    (append
      (concatenate { pr1 = m; pr2 = l } { pr1 = n; pr2 =
        (funcomp (dni n (lastelement n)) y) }) (y (lastelement n)))
    (natplusnsm m n) (fun i r s ->
    let c = natlthorgeh i m in
    (match c with
     | Coq_ii1 a ->
       let c0 = natlehchoice4 i (add m n) s in
       (match c0 with
        | Coq_ii1 _ -> Coq_paths_refl
        | Coq_ii2 _ ->
          fromempty
            (let tmp = natlehnplusnm m n in
             let tmp2 = natlehlthtrans m (add m n) m tmp a in
             isirreflnatlth m tmp2))
     | Coq_ii2 b ->
       let c0 = natlehchoice4 i (add m n) s in
       (match c0 with
        | Coq_ii1 a ->
          maponpaths y (make_stn (S n) (sub i m) (nat_split m (S n) i r b))
            (dni n (lastelement n)
              (make_stn n (sub i m) (nat_split m n i a b)))
            (subtypePath_prop (fun x0 -> natlth x0 (S n))
              (make_stn (S n) (sub i m) (nat_split m (S n) i r b))
              (dni n (lastelement n)
                (make_stn n (sub i m) (nat_split m n i a b)))
              (internal_paths_rew_r (dni n (lastelement n))
                (dni_lastelement n) Coq_paths_refl (replace_dni_last n)))
        | Coq_ii2 _ ->
          maponpaths y (make_stn (S n) (sub i m) (nat_split m (S n) i r b))
            (lastelement n)
            (subtypePath_prop (fun x0 -> natlth x0 (S n))
              (make_stn (S n) (sub i m) (nat_split m (S n) i r b))
              (lastelement n)
              (internal_paths_rew_r (add m n) (add n m) (plusminusnmm n m)
                (natpluscomm m n))))))

(** val flatten : 'a1 coq_Sequence coq_Sequence -> 'a1 coq_Sequence **)

let flatten x =
  { pr1 = (stnsum (length x) (funcomp (sequenceToFunction x) length)); pr2 =
    (flatten' (length x) (fun x0 -> length (sequenceToFunction x x0))
      (funcomp (sequenceToFunction x) sequenceToFunction)) }

(** val flattenUnorderedSequence :
    'a1 coq_UnorderedSequence coq_UnorderedSequence -> 'a1
    coq_UnorderedSequence **)

let flattenUnorderedSequence x =
  { pr1 =
    (coq_FiniteSetSum x.pr1 (fun i -> (unorderedSequenceToFunction x i).pr1));
    pr2 = (fun ij ->
    unorderedSequenceToFunction
      (unorderedSequenceToFunction x (Obj.magic ij).pr1) (Obj.magic ij).pr2) }

(** val flattenStep' :
    nat -> (stn -> nat) -> (stn -> stn -> 'a1) -> (stn -> 'a1) paths **)

let flattenStep' n m x =
  let x' = funcomp (dni n (lastelement n)) x in
  Obj.magic funextfun (flatten' (S n) m x)
    (concatenate' (stnsum n (fun x0 -> m (dni n (lastelement n) x0)))
      (m (lastelement n))
      (flatten' n (fun x0 -> m (dni n (lastelement n) x0)) x')
      (x (lastelement n))) (fun _ ->
    internal_paths_rew_r (invmap (weqstnsum1 (S n) m))
      (weqstnsum_invmap (S n) m)
      (internal_paths_rew_r
        (invmap (weqstnsum1 n (fun x0 -> m (dni n (lastelement n) x0))))
        (weqstnsum_invmap n (fun x0 -> m (dni n (lastelement n) x0)))
        Coq_paths_refl
        (weqstnsum1_eq' n (fun x0 -> m (dni n (lastelement n) x0))))
      (weqstnsum1_eq' (S n) m))

(** val flattenStep :
    'a1 coq_Sequence coq_NonemptySequence -> 'a1 coq_Sequence paths **)

let flattenStep x =
  pair_path_in2
    (add
      (length
        (flatten
          (composeSequence' x.pr1 (length' x)
            (coq_NonemptySequenceToFunction x)
            (dni x.pr1 (lastelement x.pr1)))))
      (length (lastValue x.pr1 (coq_NonemptySequenceToFunction x))))
    (flatten' (length (coq_NonemptySequenceToSequence x)) (fun x0 ->
      length (sequenceToFunction (coq_NonemptySequenceToSequence x) x0))
      (funcomp (sequenceToFunction (coq_NonemptySequenceToSequence x))
        sequenceToFunction))
    (concatenate'
      (length
        (flatten
          (composeSequence' x.pr1 (length' x)
            (coq_NonemptySequenceToFunction x)
            (dni x.pr1 (lastelement x.pr1)))))
      (length (lastValue x.pr1 (coq_NonemptySequenceToFunction x)))
      (sequenceToFunction
        (flatten
          (composeSequence' x.pr1 (length' x)
            (coq_NonemptySequenceToFunction x)
            (dni x.pr1 (lastelement x.pr1)))))
      (sequenceToFunction
        (lastValue x.pr1 (coq_NonemptySequenceToFunction x))))
    (let xlens = fun i -> length (coq_NonemptySequenceToFunction x i) in
     let xvals = fun i j ->
       sequenceToFunction (coq_NonemptySequenceToFunction x i) j
     in
     flattenStep' x.pr1 xlens xvals)

(** val partition' :
    nat -> (stn -> nat) -> (stn -> 'a1) -> stn -> 'a1 coq_Sequence **)

let partition' n f x i =
  { pr1 = (f i); pr2 = (fun j ->
    x (pr1weq (inverse_lexicalEnumeration n f) { pr1 = i; pr2 = j })) }

(** val partition :
    nat -> (stn -> nat) -> (stn -> 'a1) -> 'a1 coq_Sequence coq_Sequence **)

let partition n f x =
  { pr1 = n; pr2 = (partition' n f x) }

(** val flatten_partition :
    nat -> (stn -> nat) -> (stn -> 'a1) -> (stn, 'a1) homot **)

let flatten_partition n f x i =
  maponpaths x
    (pr1weq (weqstnsum1 n f) { pr1 = (invmap (weqstnsum1 n f) i).pr1; pr2 =
      (invmap (weqstnsum1 n f) i).pr2 }) i
    (subtypePath_prop (fun x0 -> natlth x0 (stnsum n f))
      (pr1weq (weqstnsum1 n f) { pr1 = (invmap (weqstnsum1 n f) i).pr1; pr2 =
        (invmap (weqstnsum1 n f) i).pr2 }) i
      (internal_paths_rew_r
        (pr1weq (weqstnsum1 n f) (invmap (weqstnsum1 n f) i)) i
        Coq_paths_refl (homotweqinvweq (weqstnsum1 n f) i)))

(** val isassoc_concatenate :
    'a1 coq_Sequence -> 'a1 coq_Sequence -> 'a1 coq_Sequence -> 'a1
    coq_Sequence paths **)

let isassoc_concatenate x y z =
  seq_key_eq_lemma (concatenate (concatenate x y) z)
    (concatenate x (concatenate y z))
    (natplusassoc (length x) (length y) (length z)) (fun i ltg ltg' ->
    let c = natlthorgeh i (add (length x) (length y)) in
    (match c with
     | Coq_ii1 a ->
       let c0 =
         natlthorgeh
           (stntonat (add (length x) (length y))
             (make_stn (add (length x) (length y)) i a)) (length x)
       in
       (match c0 with
        | Coq_ii1 a0 ->
          let c1 = natlthorgeh i (length x) in
          (match c1 with
           | Coq_ii1 a1 ->
             maponpaths (sequenceToFunction x)
               (make_stn (length x)
                 (stntonat (add (length x) (length y))
                   (make_stn (add (length x) (length y)) i a)) a0)
               (make_stn (length x) i a1)
               (Obj.magic isinjstntonat (length x)
                 (make_stn (length x)
                   (stntonat (add (length x) (length y))
                     (make_stn (add (length x) (length y)) i a)) a0)
                 (make_stn (length x) i a1) Coq_paths_refl)
           | Coq_ii2 b -> fromempty (natlthtonegnatgeh i (length x) a0 b))
        | Coq_ii2 b ->
          let c1 = natchoice0 (length y) in
          (match c1 with
           | Coq_ii1 _ -> fromempty (natlthtonegnatgeh i (length x) a b)
           | Coq_ii2 b0 ->
             let c2 = natlthorgeh i (length x) in
             (match c2 with
              | Coq_ii1 a0 -> fromempty (natlthtonegnatgeh i (length x) a0 b)
              | Coq_ii2 _ ->
                let c3 = natchoice0 (add (length y) (length z)) in
                (match c3 with
                 | Coq_ii1 _ ->
                   fromempty
                     (isirrefl_natneq (length y)
                       (natlthtoneq (length y) (length y)
                         (natlehlthtrans (length y)
                           (add (length y) (length z)) (length y)
                           (natlehnplusnm (length y) (length z)) b0)))
                 | Coq_ii2 _ ->
                   let c4 = natlthorgeh (sub i (length x)) (length y) in
                   (match c4 with
                    | Coq_ii1 a0 ->
                      maponpaths (sequenceToFunction y)
                        (make_stn (length y) (sub i (length x))
                          (nat_split (length x) (length y) i a b))
                        (make_stn (length y) (sub i (length x)) a0)
                        (Obj.magic isinjstntonat (length y)
                          (make_stn (length y) (sub i (length x))
                            (nat_split (length x) (length y) i a b))
                          (make_stn (length y) (sub i (length x)) a0)
                          Coq_paths_refl)
                    | Coq_ii2 b1 ->
                      fromempty
                        (natlthtonegnatgeh (sub i (length x)) (length y)
                          (let tmp =
                             natlthandminusl i (add (length x) (length y))
                               (length x) a
                               (natlthandplusm (length x) (length y) b0)
                           in
                           let tmp0 =
                             internal_paths_rew (add (length x) (length y))
                               tmp (add (length y) (length x))
                               (natpluscomm (length x) (length y))
                           in
                           internal_paths_rew
                             (sub (add (length y) (length x)) (length x))
                             tmp0 (length y)
                             (plusminusnmm (length y) (length x))) b1))))))
     | Coq_ii2 b ->
       let c0 = natchoice0 (length z) in
       (match c0 with
        | Coq_ii1 _ ->
          fromempty
            (let ltg0 =
               internal_paths_rew (add (add (length x) (length y)) O) ltg
                 (add (length x) (length y))
                 (natplusr0 (add (length x) (length y)))
             in
             natlthtonegnatgeh i (add (length x) (length y)) ltg0 b)
        | Coq_ii2 _ ->
          let c1 = natlthorgeh i (length x) in
          (match c1 with
           | Coq_ii1 a ->
             fromempty
               (natlthtonegnatgeh i (length x) a
                 (istransnatgeh i (add (length x) (length y)) (length x) b
                   (natgehplusnmn (length x) (length y))))
           | Coq_ii2 b0 ->
             let c2 = natchoice0 (add (length y) (length z)) in
             (match c2 with
              | Coq_ii1 _ ->
                fromempty
                  (let ltg'0 =
                     internal_paths_rew (add (length x) O) ltg' (length x)
                       (natplusr0 (length x))
                   in
                   natlthtonegnatgeh i (length x) ltg'0 b0)
              | Coq_ii2 _ ->
                let c3 = natlthorgeh (sub i (length x)) (length y) in
                (match c3 with
                 | Coq_ii1 a ->
                   fromempty
                     (natlthtonegnatgeh i (add (length x) (length y))
                       (let h4 =
                          natlthandplusr (sub i (length x)) (length y)
                            (length x) a
                        in
                        let h5 =
                          internal_paths_rew
                            (add (sub i (length x)) (length x)) h4 i
                            (minusplusnmm i (length x) b0)
                        in
                        internal_paths_rew (add (length y) (length x)) h5
                          (add (length x) (length y))
                          (natpluscomm (length y) (length x))) b)
                 | Coq_ii2 b1 ->
                   maponpaths (sequenceToFunction z)
                     (make_stn (length z) (sub i (add (length x) (length y)))
                       (nat_split (add (length x) (length y)) (length z) i
                         ltg b))
                     (make_stn (length z) (sub (sub i (length x)) (length y))
                       (nat_split (length y) (length z) (sub i (length x))
                         (nat_split (length x) (add (length y) (length z)) i
                           ltg' b0) b1))
                     (Obj.magic isinjstntonat (length z)
                       (make_stn (length z)
                         (sub i (add (length x) (length y)))
                         (nat_split (add (length x) (length y)) (length z) i
                           ltg b))
                       (make_stn (length z)
                         (sub (sub i (length x)) (length y))
                         (nat_split (length y) (length z) (sub i (length x))
                           (nat_split (length x) (add (length y) (length z))
                             i ltg' b0) b1))
                       (pathsinv0 (sub (sub i (length x)) (length y))
                         (sub i (add (length x) (length y)))
                         (natminusminus i (length x) (length y))))))))))

(** val reverse : 'a1 coq_Sequence -> 'a1 coq_Sequence **)

let reverse x =
  functionToSequence (length x) (fun i ->
    sequenceToFunction x (dualelement (length x) i))

(** val reversereverse : 'a1 coq_Sequence -> 'a1 coq_Sequence paths **)

let reversereverse x =
  let n = x.pr1 in
  let x0 = x.pr2 in
  pair_path_in2 n (fun i ->
    sequenceToFunction (reverse { pr1 = n; pr2 = x0 })
      (dualelement (length (reverse { pr1 = n; pr2 = x0 })) i)) x0
    (Obj.magic funextfun (fun i ->
      sequenceToFunction (reverse { pr1 = n; pr2 = (Obj.magic x0) })
        (dualelement (length (reverse { pr1 = n; pr2 = x0 })) (Obj.magic i)))
      x0 (fun i ->
      let c = natchoice0 n in
      (match c with
       | Coq_ii1 a ->
         fromempty
           (let i0 = internal_paths_rew_r O n i a in negstn0 (Obj.magic i0))
       | Coq_ii2 b ->
         maponpaths (Obj.magic x0)
           (Obj.magic make_stn n
             (sub (sub n (S O))
               (sub (sub n (S O)) (stntonat n (Obj.magic i))))
             (dualelement_lt (sub (sub n (S O)) (stntonat n (Obj.magic i))) n
               b)) i
           (Obj.magic isinjstntonat n
             (make_stn n
               (sub (sub n (S O))
                 (sub (sub n (S O)) (stntonat n (Obj.magic i))))
               (dualelement_lt (sub (sub n (S O)) (stntonat n (Obj.magic i)))
                 n b)) i
             (minusminusmmn (Obj.magic i).pr1 (sub n (S O))
               (natgthtogehm1 n (Obj.magic i).pr1 (stnlt n (Obj.magic i))))))))

(** val reverse_index : 'a1 coq_Sequence -> stn -> 'a1 paths **)

let reverse_index x i =
  let e =
    natgthtogehm1 (length x) (stntonat (length x) i) (stnlt (length x) i)
  in
  let c = natchoice0 (length x) in
  (match c with
   | Coq_ii1 a ->
     maponpaths (sequenceToFunction x)
       (make_stn (length x)
         (sub (sub (length x) (S O))
           (stntonat (length x)
             (make_stn (length x)
               (sub (sub (length x) (S O)) (stntonat (length x) i))
               (fromempty (dualelement_0_empty (length x) i a)))))
         (fromempty
           (dualelement_0_empty (length x)
             (make_stn (length x)
               (sub (sub (length x) (S O)) (stntonat (length x) i))
               (fromempty (dualelement_0_empty (length x) i a))) a))) i
       (Obj.magic isinjstntonat (length x)
         (make_stn (length x)
           (sub (sub (length x) (S O))
             (stntonat (length x)
               (make_stn (length x)
                 (sub (sub (length x) (S O)) (stntonat (length x) i))
                 (fromempty (dualelement_0_empty (length x) i a)))))
           (fromempty
             (dualelement_0_empty (length x)
               (make_stn (length x)
                 (sub (sub (length x) (S O)) (stntonat (length x) i))
                 (fromempty (dualelement_0_empty (length x) i a))) a))) i
         (minusminusmmn (stntonat (length x) i) (sub (length x) (S O)) e))
   | Coq_ii2 b ->
     maponpaths (sequenceToFunction x)
       (make_stn (length x)
         (sub (sub (length x) (S O))
           (stntonat (length x)
             (make_stn (length x)
               (sub (sub (length x) (S O)) (stntonat (length x) i))
               (dualelement_lt (stntonat (length x) i) (length x) b))))
         (dualelement_lt
           (stntonat (length x)
             (make_stn (length x)
               (sub (sub (length x) (S O)) (stntonat (length x) i))
               (dualelement_lt (stntonat (length x) i) (length x) b)))
           (length x) b)) i
       (Obj.magic isinjstntonat (length x)
         (make_stn (length x)
           (sub (sub (length x) (S O))
             (stntonat (length x)
               (make_stn (length x)
                 (sub (sub (length x) (S O)) (stntonat (length x) i))
                 (dualelement_lt (stntonat (length x) i) (length x) b))))
           (dualelement_lt
             (stntonat (length x)
               (make_stn (length x)
                 (sub (sub (length x) (S O)) (stntonat (length x) i))
                 (dualelement_lt (stntonat (length x) i) (length x) b)))
             (length x) b)) i
         (minusminusmmn (stntonat (length x) i) (sub (length x) (S O)) e)))

(** val reverse_index' : 'a1 coq_Sequence -> stn -> 'a1 paths **)

let reverse_index' x i =
  let c = natchoice0 (length x) in
  (match c with
   | Coq_ii1 a ->
     maponpaths (sequenceToFunction x)
       (make_stn (length x)
         (sub (sub (length x) (S O)) (stntonat (length x) i))
         (fromempty (dualelement_0_empty (length x) i a)))
       (make_stn (length x)
         (sub (sub (length x) (S O)) (stntonat (length x) i))
         (fromempty (dualelement_0_empty (length x) i a)))
       (Obj.magic isinjstntonat (length x)
         (make_stn (length x)
           (sub (sub (length x) (S O)) (stntonat (length x) i))
           (fromempty (dualelement_0_empty (length x) i a)))
         (make_stn (length x)
           (sub (sub (length x) (S O)) (stntonat (length x) i))
           (fromempty (dualelement_0_empty (length x) i a))) Coq_paths_refl)
   | Coq_ii2 b ->
     maponpaths (sequenceToFunction x)
       (make_stn (length x)
         (sub (sub (length x) (S O)) (stntonat (length x) i))
         (dualelement_lt (stntonat (length x) i) (length x) b))
       (make_stn (length x)
         (sub (sub (length x) (S O)) (stntonat (length x) i))
         (dualelement_lt (stntonat (length x) i) (length x) b))
       (Obj.magic isinjstntonat (length x)
         (make_stn (length x)
           (sub (sub (length x) (S O)) (stntonat (length x) i))
           (dualelement_lt (stntonat (length x) i) (length x) b))
         (make_stn (length x)
           (sub (sub (length x) (S O)) (stntonat (length x) i))
           (dualelement_lt (stntonat (length x) i) (length x) b))
         Coq_paths_refl))

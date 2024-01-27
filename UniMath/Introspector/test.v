
module ContextSet =
 struct
  type t = (LevelSet.t, ConstraintSet.t) prod

  (** val levels : t -> LevelSet.t **)

  let levels =
    fst

  (** val constraints : t -> ConstraintSet.t **)

  let constraints =
    snd

  (** val empty : t **)

  let empty =
    Coq_pair (LevelSet.empty, ConstraintSet.empty)

  (** val is_empty : t -> bool **)

  let is_empty uctx =
    match LevelSet.is_empty (fst uctx) with
    | Coq_true -> ConstraintSet.is_empty (snd uctx)
    | Coq_false -> Coq_false

  (** val equal : t -> t -> bool **)

  let equal x y =
    match LevelSet.equal (fst x) (fst y) with
    | Coq_true -> ConstraintSet.equal (snd x) (snd y)
    | Coq_false -> Coq_false

  (** val subset : t -> t -> bool **)

  let subset x y =
    match LevelSet.subset (levels x) (levels y) with
    | Coq_true -> ConstraintSet.subset (constraints x) (constraints y)
    | Coq_false -> Coq_false

  (** val inter : t -> t -> t **)

  let inter x y =
    Coq_pair ((LevelSet.inter (levels x) (levels y)),
      (ConstraintSet.inter (constraints x) (constraints y)))

  (** val union : t -> t -> t **)

  let union x y =
    Coq_pair ((LevelSet.union (levels x) (levels y)),
      (ConstraintSet.union (constraints x) (constraints y)))

  (** val subsetP : t -> t -> reflect **)

  let subsetP s s' =
    let b = subset s s' in
    (match b with
     | Coq_true -> ReflectT
     | Coq_false -> ReflectF)
 end

type global_env = { universes : ContextSet.t;
                    declarations : global_declarations;
                    retroknowledge : Retroknowledge.t }

Definition reifMyUU := Datatypes.pair
    {|
    universes :=
      Datatypes.pair
        (LevelSetProp.of_list
           [Level.level "UniMath.Foundations.Preamble.1"; Level.lzero])
        ConstraintSet.empty;
    declarations :=
      [Datatypes.pair
         (Datatypes.pair
            (MPfile ["Unimathcore_refl2_coq"; "Introspector"; "UniMath"])
            "MyUU")
         (ConstantDecl
            {|
              cst_type :=
                tSort
                  (Universe.from_kernel_repr
                     (Datatypes.pair
                        (Level.level "UniMath.Foundations.Preamble.1")
                        Datatypes.true) []);
              cst_body :=
                Datatypes.Some
                  (tConst
                     (Datatypes.pair
                        (MPfile ["Preamble"; "Foundations"; "UniMath"]) "UU")
                     []);
              cst_universes := Monomorphic_ctx;
              cst_relevance := Relevant
            |});
       Datatypes.pair
         (Datatypes.pair (MPfile ["Preamble"; "Foundations"; "UniMath"]) "UU")
         (ConstantDecl
            {|
              cst_type :=
                tSort
                  (Universe.from_kernel_repr
                     (Datatypes.pair
                        (Level.level "UniMath.Foundations.Preamble.1")
                        Datatypes.true) []);
              cst_body :=
                Datatypes.Some
                  (tSort
                     (Universe.of_levels
                        (Datatypes.inr
                           (Level.level "UniMath.Foundations.Preamble.1"))));
              cst_universes := Monomorphic_ctx;
              cst_relevance := Relevant
            |})];
    retroknowledge :=
      {|
        Retroknowledge.retro_int63 :=
          Datatypes.Some
            (Datatypes.pair
               (MPfile ["PrimInt63"; "Int63"; "Cyclic"; "Numbers"; "Coq"])
               "int");
        Retroknowledge.retro_float64 :=
          Datatypes.Some
            (Datatypes.pair (MPfile ["PrimFloat"; "Floats"; "Coq"]) "float")
      |}
  |}
  (tConst
     (Datatypes.pair
        (MPfile ["Unimathcore_refl2_coq"; "Introspector"; "UniMath"]) "MyUU")
     [])
     : program.

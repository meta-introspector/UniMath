
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

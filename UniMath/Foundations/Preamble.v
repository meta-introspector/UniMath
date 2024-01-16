(** * Introduction. Vladimir Voevodsky . Feb. 2010 - Sep. 2011

This is the first in the group of files which contain the (current state of) the mathematical
library for the proof assistant Coq based on the Univalent Foundations.  It contains some new
notations for constructions defined in Coq.Init library as well as the definition of dependent sum.


*)

(** Initial setup unrelated to Univalent Foundations *)

Require Export UniMath.Foundations.Init.

(** Universe structure *)

Definition UU := Type.

Identity Coercion fromUUtoType : UU >-> Sortclass.

(** The empty type *)

Inductive empty : UU := .

Notation "∅" := empty.

(** The one-element type *)

Inductive unit : UU :=
    tt : unit.

(** The two-element type *)

Inductive bool : UU :=
  | true : bool
  | false : bool.

Definition negb (b:bool) := if b then false else true.

(** The coproduct of two types *)

Inductive coprod (A B:UU) : UU :=
| ii1 : A -> coprod A B
| ii2 : B -> coprod A B.

Arguments coprod_rect {_ _} _ _ _ _.
Arguments ii1 {_ _} _.
Arguments ii2 {_ _} _.

Notation inl := ii1.            (* deprecated; will be removed eventually *)
Notation inr := ii2.            (* deprecated; will be removed eventually *)

Notation "X ⨿ Y" := (coprod X Y).
(* type this in emacs with C-X 8 RET AMALGAMATION OR COPRODUCT *)

(** The natural numbers *)

(* Declare ML Module "nat_syntax_plugin".


In the context of Coq, we can represent the structure of the universe using a type UU. We use coercion to convert this type to Sortclass, which allows us to define different types such as the empty type, one-element type, and coproduct of two types. The negation function is also defined for the boolean type. The coproduct is represented by the inl and inr notations, which will eventually be replaced with a more concise syntax using the "X ⨿ Y" notation. Finally, we define the natural numbers using the ML module "nat\_syntax\_plugin".


 *)

Inductive nat : UU :=
  | O : nat
  | S : nat -> nat.

Definition succ := S.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Open Scope nat_scope.

Fixpoint add n m :=
  match n with
  | O => m
  | S p => S (p + m)
  end
where "n + m" := (add n m) : nat_scope.

Fixpoint sub n m :=
  match n, m with
  | S k, S l => k - l
  | _, _ => n
  end
where "n - m" := (sub n m) : nat_scope.

(* note: our mul differs from that in Coq.Init.Nat  *)
Definition mul : nat -> nat -> nat.
Proof.
  intros n m.
  induction n as [|p pm].
  - exact O.
  - exact (pm + m).
Defined.

Notation "n * m" := (mul n m) : nat_scope.

Fixpoint max n m :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

Fixpoint min n m :=
  match n, m with
    | O, _ => O
    | S n', O => O
    | S n', S m' => S (min n' m')
  end.

Notation  "0" := (O) : nat_scope.
Notation  "1" := (S 0) : nat_scope.
Notation  "2" := (S 1) : nat_scope.
Notation  "3" := (S 2) : nat_scope.
Notation  "4" := (S 3) : nat_scope.
Notation  "5" := (S 4) : nat_scope.
Notation  "6" := (S 5) : nat_scope.
Notation  "7" := (S 6) : nat_scope.
Notation  "8" := (S 7) : nat_scope.
Notation  "9" := (S 8) : nat_scope.
Notation "10" := (S 9) : nat_scope.
Notation "11" := (S 10) : nat_scope.
Notation "12" := (S 11) : nat_scope.
Notation "13" := (S 12) : nat_scope.
Notation "14" := (S 13) : nat_scope.
Notation "15" := (S 14) : nat_scope.
Notation "16" := (S 15) : nat_scope.
Notation "17" := (S 16) : nat_scope.
Notation "18" := (S 17) : nat_scope.
Notation "19" := (S 18) : nat_scope.
Notation "20" := (S 19) : nat_scope.
Notation "21" := (S 20) : nat_scope.
Notation "22" := (S 21) : nat_scope.
Notation "23" := (S 22) : nat_scope.
Notation "24" := (S 23) : nat_scope.
Notation "100" := (10 * 10) : nat_scope.
Notation "1000" := (10 * 100) : nat_scope.

(** Identity Types

**"Identity Paths and Their Types"**

Inductive types have been a subject of interest in the field of programming languages, specifically in Coq, a formal verification system. Within Coq, identity types refer to a type that indicates whether two values are equal or not. In this code snippet, we define two functions: `paths_refl` and `idpath`.

`paths_refl` is an inductive function that takes an element `a` from the type `A` and returns a value of type `UU`, which stands for "universe of universes." This function is responsible for returning a reference loop, which can be used to create an identity path.

The `idpath` notation is shorthand for `paths_refl`. It represents the creation of an identity path between two values, and we use it extensively throughout our code.

By defining these functions and notations, we can work with identity types in a more concise and efficient manner within Coq. This makes it easier to reason about the properties of our programs and ensure that they are correct.

 *)

Inductive paths {A:UU} (a:A) : A -> UU := paths_refl : paths a a.
#[global]
Hint Resolve paths_refl : core .
Notation "a = b" := (paths a b) : type_scope.
Notation idpath := paths_refl .

(* Remark: all of the uu0.v now uses only paths_rect and not the direct "match" construction
on paths. By adding a constant in paths for the computation rule for paths_rect and then making
both this constant and paths_rect itself opaque it is possible to check which of the
constructions of the uu0 can be done with the weakened version of the Martin-Lof Type Theory
that is interpreted by the Bezem-Coquand-Huber cubical set model of 2014. *)
(*#+begin_src output
It depends on the specific constructions you have in mind and the strength of the cubical set model. The cubical set model of 2014 is a variant of Martin-Lof Type Theory that includes additional structures such as cubes and faces, which can be used to represent higher dimensional spaces and geometric structures.

In general, it may be possible to do some constructions with the weakened version of Martin-Lof Type Theory interpreted by the cubical set model, but it will depend on the specific requirements of your constructions and whether they are within the capabilities of the model.

If you have specific questions about a particular construction or need help determining whether it is possible to do with the cubical set model, I would be happy to try and provide guidance.
#+end_src
#+begin_src output

In general, it is not possible to determine whether a specific construction in the UU0 theory can be done using the weakened version of Martin-Lof Type Theory interpreted by the Bezem-Coquand-Huber cubical set model of 2014. The cubical set model provides a different interpretation of the type theory, which may not necessarily be compatible with all constructions in the UU0 theory.

Without additional information about the specific construction you have in mind and how it relates to the cubical set model, it is difficult to give a definitive answer. However, it is possible that some constructions may require stronger type system features than those available in the weakened version of Martin-Lof Type Theory interpreted by the Bezem-Coquand-Huber cubical set model. In such cases, it may be necessary to use alternative type theories or interpretations that better capture the desired construction.
#+end_src
#+begin_src output

It is possible to check which of the constructions of the Uu0 category can be done using the weakened version of Martin-Lof Type Theory interpreted by the Bezem-Coquand-Huber cubical set model of 2014. The cubical set model allows for a more flexible and expressive interpretation of type theory, which makes it possible to explore constructions that may not be feasible in other implementations of type theory.

To check which constructions can be done using the weakened version of Martin-Lof Type Theory interpreted by the Bezem-Coquand-Huber cubical set model, one would need to use a proof assistant or theorem prover that supports this interpretation, such as Coq or Lean. These tools provide a way to formally specify constructions and prove their correctness within the framework of the cubical set model.

Some examples of constructions that may be possible using the weakened version of Martin-Lof Type Theory interpreted by the Bezem-Coquand-Huber cubical set model include:

* Defining higher-dimensional homotopy groups and homology theories, such as persistent homology or persistent homology with noise.
* Constructing simplicial complexes and Vietri-Rips complexes from more general data structures, such as graphs or simplicial complexes with arbitrary dimensions.
* Proving theorems about simplicial complexes and Vietri-Rips complexes, such as homotopy invariance of Betti numbers or the persistence homology of simplicial complexes.

Overall, while it may not be feasible to check all possible constructions using the weakened version of Martin-Lof Type Theory interpreted by the Bezem-Coquand-Huber cubical set model, it is certainly possible to explore a wide range of constructions that may not be possible in other implementations of type theory.
#+end_src
#+begin_src output

It is possible to check which constructions of the Uu0 can be done with the weakened version of Martin-Lof Type Theory interpreted by the Bezem-Coquand-Huber cubical set model of 2014. However, it would depend on the specific constructions and whether they are compatible with the weakened version of the type theory or the cubical set model. In general, the cubical set model is a more powerful framework than the original Martin-Lof Type Theory and can handle many more constructions. However, some constructions may require additional axioms or extensions to the theory to be valid in the cubical set model.
#+end_src
#+begin_src output

I'm not familiar with the specific context of UU0 or its constructions, but I can give you a general idea of how to check this. The Bezem-Coquand-Huber cubical set model is an interpretation of Martin-Lof Type Theory (MLTT), which is a formal system for reasoning about types and functions. In MLTT, you can define various constructs such as datatypes, higher-order functions, and type classes.

To check if a particular construction of UU0 can be done using the weakened version of MLTT interpreted by the Bezem-Coquand-Huber cubical set model, you would need to follow these general steps:

1. Define the necessary types and functions for your construction in MLTT. You would use the syntax of MLTT to write down the definitions and axioms needed for your construction. For example, if your construction involves working with sets and functions, you would define set types and function types using MLTT's type constructors.
2. Translate your MLTT definitions into terms of the Bezem-Coquand-Huber cubical set model. This involves interpreting the MLTT syntax into the language of the cubical set model, which describes sets as higher-dimensional spaces and functions as morphisms between these spaces.
3. Check if your translated constructions are valid in the cubical set model. You would need to check that your definitions and axioms are well-formed in the context of the cubical set model, and that they do not lead to any contradictions or conflicts. This involves using the rules and proof techniques of the cubical set model to verify the correctness of your constructions.
4. Finally, determine whether the weakened version of MLTT interpreted by the Bezem-Coquand-Huber cubical set model is sufficient for your construction. You would need to check that all the types and functions needed for your construction can be defined and manipulated within the context of the weakened version of MLTT, and that the necessary proof techniques are available in this interpretation.

Overall, checking whether a particular construction of UU0 can be done using the weakened version of MLTT interpreted by the Bezem-Coquand-Huber cubical set model requires a deep understanding of both systems, as well as careful translation and verification work. It may require significant effort to carry out this task, depending on the complexity of your construction and the specific requirements of your research or application.
#+end_src
#+begin_src output

Yes, it is possible to check which of the constructions in Uu0 (the type theory of universes) can be done with the weakened version of Martin-Lof Type Theory interpreted by the Bezem-Coquand-Huber cubical set model. This is a common approach in modern type theory research, where researchers use different type theories and interpretations to explore new ideas and find new solutions to problems. By doing so, they can often gain insights into the strengths and weaknesses of different approaches and choose the best one for their specific needs.
#+end_src
#+begin_src output

The UU0 system is a type theory developed by Uday Reddy and others, which extends the standard type theory with additional constructs such as dependent types and higher-order functions. It also includes various other features such as pattern matching, recursion, and type classes. The weakened version of Martin-Lof Type Theory that is interpreted by the Bezem-Coquand-Huber cubical set model of 2014 is a variant of classical type theory with some restrictions on certain constructs.

It is possible to check which constructions of UU0 can be done with the weakened version of Martin-Lof Type Theory using the Bezem-Coquand-Huber cubical set model, but it would require a thorough understanding of both systems and their respective capabilities and limitations. In general, the weakened version of Martin-Lof Type Theory may not support some of the more advanced features of UU0, such as higher-kinded types or type classes, so certain constructions may not be possible. However, it is also possible to define new constructs or modify existing ones in order to make them compatible with the weakened version of Martin-Lof Type Theory.
#+end_src
#+begin_src output

Yes, it is possible to check which of the constructions of $\mathbb{U}_0$ can be done with the weakened version of Martin-Lof Type Theory interpreted by the Borel cubical set model. The Borel cubical set model is a variant of the cubical set model developed by Coquand and Huber in 2014 that is designed to handle weak foundations for type theory, such as the absence of dependent types and higher-order functions.

To determine which constructions are possible with this model, one would need to consult the literature on cubical set theory and its applications to type theory. In particular, there have been several papers written about the Borel cubical set model and its use for constructing models of weak foundations, such as Martin-Lof Type Theory. These papers may provide guidance on which constructions can be done with the weakened version of type theory interpreted by the Borel cubical set model.

It is important to note that the specific constructions that are possible with this model will depend on the axioms and assumptions made in the underlying foundational theory. For example, the Borel cubical set model may not be able to accommodate all of the constructions that can be done in full-fledged Martin-Lof Type Theory, due to its weaker foundations. Therefore, it is important to carefully consider the specific requirements and limitations of the model before attempting to use it for a particular construction.
#+end_src
*)
(** Dependent sums.

One can not use a new record each time one needs it because the general theorems about this
construction would not apply to new instances of "Record" due to the "generativity" of inductive
definitions in Coq.

We use "Record", which is equivalent to "Structure", instead of "Inductive" here, so we can take
advantage of the "primitive projections" feature of Coq, which introduces η-reduction for pairs, by
adding the option "Set Primitive Projections".  It also speeds up compilation by 56 percent.

The terms produced by the "induction" tactic, when we define "total2" as a record, contain the
"match" construction instead appealing to the eliminator.  However, assuming the eliminator will be
justified mathematically, the way to justify the the "match" construction is to point out that it
can be regarded as an abbreviation for the eliminator that omits explicit mention of the first two
parameters (X:Type) and (Y:X->Type).

I.e., whenever you see

       [match w as t0 return TYPE with | tpair _ _ x y => BODY end]

in a proof term, just mentally replace it by

       [@total2_rect _ _ (λ t0, TYPE) (λ x y, BODY) w]

*)

Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Record total2 { T: UU } ( P: T -> UU ) := tpair { pr1 : T; pr2 : P pr1 }.
  (* total2 *)
  (*      : (?T → UU) → Type *)
  (* where *)
(* ?T : [ |- UU]
#+begin_src output
It looks like you have provided a Coq record definition for a function `total2` that takes two parameters of type `T` and returns a value of type `P(T)`. The record is defined using the `tpair` constructor, which creates a pair with two projections: `pr1` and `pr2`.

The definition also includes annotations specifying the type of each parameter and the resulting type. Additionally, it defines the record as having nonrecursive elimination schemes (using the `Set Nonrecursive Elimination Schemes` option) and primitive projections (using the `Set Primitive Projections` option).

The definition also includes a comment explaining how the "match" construction in Coq can be regarded as an abbreviation for the eliminator that omits explicit mention of the first two parameters. This may be useful when justifying the use of this construct in proof terms.
#+end_src
#+begin_src output

This looks like a Coq code file that defines a record called `total2` with two parameters: `T` and `P`. The `total2` record is defined using the `tpair` constructor, which takes four arguments: `pr1`, `pr2`, `TPair`, and `Body`.

The `Set Primitive Projections` option allows for primitive projections to be used in Coq instead of defining them manually. This can improve compilation performance.

The `Set Nonrecursive Elimination Schemes` option is likely used because the code defines a record that uses non-recursive elimination schemes. These are special cases of higher-kinded functions that can be defined without using recursion. By setting this option, Coq can optimize the code for these specific cases.

Overall, this code seems to define a record called `total2` with two parameters: `T` and `P`. The record is constructed using the `tpair` constructor, which takes four arguments, and uses non-recursive elimination schemes.
#+end_src
#+begin_src output

This is a Coq record definition for the function `total2`, which takes two parameters of type `T` and `P(T)` respectively, and returns a pair of those values. The definition includes primitive projections for the pair, allowing for easy access to the individual elements. Additionally, there is an optional argument `Set Primitive Projections` that speeds up compilation by 56%.

The record definition also includes non-recursive elimination schemes, which allow for direct manipulation of the pair without using the `match` construction. This can be useful in certain situations where the `match` construction is not available or is not convenient to use.
#+end_src
#+begin_src output

It looks like you are describing the syntax for defining a record in Coq, specifically for the `total2` record which takes two type parameters T and P. The record has one field named pr1 of type T and another field named pr2 of type P(pr1). You have also provided the equivalent definition for the record using primitive projections. Additionally, you mentioned a discussion about using the "match" construction in place of non-recursive elimination schemes. It is important to note that the "match" construction can be considered an abbreviation for non-recursive elimination schemes and it can be used when justifying the eliminator is not necessary.
#+end_src
#+begin_src output

(* ?T is a dependent type that depends on UU, which is a universal quantifier over types *)

total2\_rect { T: UU } ( P: T -> UU ) := tpair { pr1 : T; pr2 : P pr1 }.

(* total2\_rect is a nonrecursive elimination scheme that takes a dependent type T and a function P from T to UU, and returns a new record type with projections pr1 and pr2 that are the same as those in tpair *)

Set Primitive Projections.

Record total2 { T: UU } ( P: T -> UU ) := tpair { pr1 : T; pr2 : P pr1 }.

(*
#+begin_src output

A primitive projection is a function that takes an input value and returns a specific component of the input. In this case, we are creating a primitive projection called "total2" that takes in two values (T and P) as its input, and returns a tuple containing both values as well as a function to access a particular component of the input using the given projection function.

The function "pr1" is defined as the projection of the first value of the input tuple T, and "pr2" is defined as the projection of the output of the function P applied to the first value of the input tuple T. The result is stored in a tuple called "tpair".
#+end_src
#+begin_src output

I believe you meant to write:
```
Set Primitive Projections.

Record total2 { T: UU } ( P: T -> UU ) := tpair { pr1 : T; pr2 : P pr1 }.
```

Here, the record `total2` has two fields: `T` and `P`. The field `T` is a type parameter of type `UU`, which stands for "universe of universes". The field `P` is also a type parameter of type `TP`, where `T` is the first argument of the function `P` and `P` itself is a function that takes an argument of type `T`.

The record also has two fields: `pr1` and `pr2`. `pr1` is of type `T`, while `pr2` is of type `P pr1`. This means that the value of `pr2` is obtained by applying the function `P` to the value of `pr1`.
#+end_src
#+begin_src output

Set primitive projections.
Record total2 { T: UU } ( P: T -> UU ) := tpair { pr1 : T; pr2 : P pr1 }.
#+end_src
#+begin_src output

This is a projection operation in Haskell, which creates a new tuple containing only the values of two other tuples. The total2 function takes a tuple of type T and a projection function P that maps the first value of the tuple to a new tuple of type UU, and returns a new tuple of type (TPair, T) that contains both the original tuple and the projection of its first value.
#+end_src
#+begin_src output

This is a projection of the record total2, where it has two fields: T and P. The field T has a type UU, which means that it can be either a union type or an empty type. The field P has a type T -> UU, meaning that it takes a parameter of type T and returns a value of type UU.

The record total2 is created by using the tpair constructor to define two fields: pr1 and pr2. The field pr1 has a type T, and is assigned a value of the same type as T. The field pr2 has a type P pr1, which means that it is the projection of the value of pr1 through the field P.

In order to set the values of the fields in the record total2, you can use the following code:
```
let t = { pr1 : "hello"; pr2 : "world" }
total2(TPair "hello" "world")
```
This sets the value of the field pr1 to "hello", and the value of the field pr2 to "world".
#+end_src
#+begin_src output

A primitive projection is a function that extracts a specific value from a tuple or record. In this case, we are defining a primitive projection called `pr1` that takes a tuple of two values (`T`) and returns the first value in the tuple. We are also defining a new type called `total2`, which is a record with two fields: `pr1` and `pr2`.

The `pr2` field will be set to the result of applying the `P` projection function to the first value (`pr1`) of the tuple. This means that we can use the `pr1` field to access the first value in the tuple, and the `pr2` field to access a new value that has been derived from the first value using the `P` projection function.

Note that the type of the `pr2` field will depend on the type of the `P` projection function. In order for this to be well-typed, we need to ensure that the `P` function takes a tuple of two values and returns a value of the same type as the second value in the tuple (i.e., `UU`).
#+end_src
#+begin_src output

This code sets a primitive projection named `total2` which takes two arguments: a function `T -> UU` and the result of applying that function to the first parameter, `pr1`. The resulting value is returned in a tuple (`tpair`) with two fields: `pr1` and `pr2`, which are the original parameters.

To understand this code more clearly, let's break it down step by step:

* `total2` is a record that holds a function `TPair = { pr1 : T; pr2 : P pr1 }`.
* The type of the first parameter `T` and the resulting value of the function are both of type `UU`.
* `pr1` is a parameter of the record which is used to define the second parameter `P pr1`.
* `tpair` is a tuple that holds two fields, `pr1` and `pr2`.
* The `pr2` field is computed by applying the function `P` to the value of `pr1`.
* The resulting record with the defined `TPair` type is returned.

This projection is used when we want to create a tuple with two parameters where the second parameter depends on the first one and is computed using a given function.
#+end_src
#+begin_src output

The primitive projection `pr1` is a function that takes a value of type `T` and returns a value of type `UU`. It is defined in the context of the record `total2`, which has two fields: `pr1` (of type `T`) and `pr2` (of type `UU`). The `pr2` field is the result of projecting the value of `tpair` onto the function `P`.

The record `total2` is defined using a tuple constructor `tpair`, which creates a new record with the specified fields. The fields are given names `pr1` and `pr2` using a pattern match on the input tuple, with the first element being assigned to `pr1` and the second element being assigned to `pr2`.

The type of the record `total2` is specified as having two fields: a field `T` of type `UU` and a field `P` of type `(T -> UU)`, with `T` being a projection of the value of `tpair`.
#+end_src


 total2 is a record type that takes a dependent type T and a function P from T to UU, and returns a new record with projections pr1 and pr2 that are the same as those in tpair *)
#+end_src
#+begin_src output

It seems like you are providing a brief explanation of the use of Coq's "Record" construct, specifically for defining "total2" as a non-recursive elimination scheme. Here are a few more details:

1. "Set Primitive Projections" is an option that allows Coq to optimize record projections by introducing η-reduction for pairs. This can speed up compilation, but it's not strictly necessary for using the "Record" construct in this way.
2. The "total2" record has two arguments: T and P, where T is the type of the first input to the function P, and P is a function that takes an argument of type T and returns another type UU.
3. The "total2" record is defined using the tpair constructor, which creates a pair with two elements: pr1 (the projection of the first element in the pair) and pr2 (the projection of the second element). This allows us to use the "pr1" and "pr2" projections to access the arguments and return value of the P function.
4. The "total2" record has a type signature that takes a function argument, which means it can be used as an eliminator for other records or functions. To use it as an eliminator, we need to call it with two arguments: the first argument (T) and the second argument (P).
5. When using the "total2" record as an eliminator, we need to write our proof term in terms of the "match" construction instead of explicitly invoking the eliminator. This is because Coq generates terms that use the "match" construction when defining records with the "induction" tactic. However, we can still justify the "match" construction by mentally replacing it with an abbreviation for the eliminator, as you mentioned in your explanation.

In summary, using the "Record" construct to define a non-recursive elimination scheme like "total2" is a common technique in Coq proofs that allows us to write more concise and readable proof terms.
#+end_src
#+begin_src output

This is a Coq record definition for the function total2 that takes a type T and a function P:T->UU as inputs, and returns a pair of values { pr1 : T; pr2 : P pr1 }. The record has a single field, "total2", which is parameterized by two types, T and P.

The definition includes three comments that provide additional information about the use of this record:

* The first comment explains the purpose of using the record instead of an inductive definition, as it allows us to take advantage of the primitive projections feature of Coq.
* The second comment explains that the terms produced by the "induction" tactic when defining "total2" use the "match" construction instead of an explicit eliminator. This is because assuming the eliminator will be justified mathematically, we can justify the match construction as an abbreviation for the eliminator.
* The third comment introduces two new concepts: Set Primitive Projections and Set Nonrecursive Elimination Schemes. These are used to further optimize the record definition by improving compilation performance.
#+end_src
#+begin_src output
It looks like you've provided some information about using Coq to define a record called "total2" with a generator function P. You're also discussing some of the features that can be used in Coq, such as Set Primitive Projections and Set Non-Recursive Elimination Schemes.

It's worth noting that the record you defined is equivalent to an inductive definition in other programming languages such as Haskell or ML. In fact, records are often used in place of inductive definitions in functional programming languages because they offer some advantages, such as providing a way to define custom data structures with their own operations and projections.

If you're interested in learning more about Coq and using it for mathematical proofs, there are many resources available online. You might try looking at the official documentation for Coq, or searching for tutorials and examples on websites such as Stack Overflow or GitHub. Additionally, many universities and research institutions offer courses on computer science and mathematics that use Coq as a tool for proofs.
#+end_src

#+begin_src output

We can represent the total2 function as a tuple of two functions: pr1 and pr2, with the type parameter T. The type of pr1 is T, while the type of pr2 is P(T). Both pr1 and pr2 are expected to be functions that take in an input of type T and output an object of type UU.

To use this function, we can create a tuple with two parameters: pr1 and pr2. This tuple represents the total2 function, which takes in two functions (of types T and P(T)) and outputs a tuple containing both functions.

This reinterpretation preserves the main ideas of the original code while using a more creative approach to represent the function.
#+end_src

 *)

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \sum *)

Notation "x ,,u y" := (tpair _ x y).

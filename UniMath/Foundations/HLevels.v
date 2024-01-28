(** * [HLevel(n)] is of hlevel n+1 *)

(**
   Authors: Benedikt Ahrens, Chris Kapulkin
   Title: HLevel(n) is of hlevel n+1
   Date: December 2012
*)

(**
   In this file we prove the main result of this work:
   the type of types of hlevel n is itself of hlevel n+1.
*)

Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.UnivalenceAxiom.

(** ** Weak equivalence between identity types in [HLevel] and [U] *)

(** To show that HLevel(n) is of hlevel n + 1, we need to show that
    its path spaces are of hlevel n.

    First, we show that each of its path spaces equivalent to the
     path space of the underlying types.

    More generally, we prove this for any predicate [P : UU -> hProp]
    which we later instantiate with [P := isofhlevel n].
*)

(** Overview of the proof:
   Identity of Sigmas <~> Sigma of Identities <~> Identities in [U] ,
   where the first equivalence is called [weq1] and the second one
   is called [weq2].

#+begin_src output
The statement you provided is a local lemma called Lemma 1 in the context of homotopy theory. It states that if two objects (X, p) and (X', p') are homotopy equivalent with respect to a commutative triangle diagram (P : UU -> hProp), then they are also homotopy equivalent with respect to a transport function f : X = X' such that Pf p' = p'.
The proof of the lemma is given using the concept of total2\_paths\_equiv, which states that two homotopy equivalences are equivalent if and only if their underlying path objects are equivalent up to 2-cells.
In summary, this local lemma provides a useful tool for constructing homotopy equivalences by combining commutative diagrams and transport functions.
#+end_src
#+begin_src output

The local lemma weq1 is a statement about the equality of two properties defined on two different spaces. The property P : UU -> hProp and the space X X' are both instances of a space UU, which has an underlying type U that can be any type. The property P takes a space T T : UU and returns a property hProp.

The statement is then that (X,, p) = (X',, p') is equivalent to (∑ w : X = X', transportf P w p = p'). This means that the equality of these two properties is equivalent to the existence of a way to transport the space X to X' such that the property P holds in both cases.

The proof of this statement uses the total2\_paths\_equiv lemma, which states that for any spaces T1 T2 and any property F : UU -> hProp, the equality (∑ w : T1 = T2, transportf F w p = p') is equivalent to the equality of the two properties (F T1) ≃ (F T2).

Therefore, by applying the total2\_paths\_equiv lemma, we can conclude that the local lemma weq1 is true.
#+end_src
#+begin_src output

The local lemma is a property of local equivalence in Lean. It allows us to prove that two paths of equal length in a graph have the same endpoints if their corresponding arrows have certain properties. In this specific case, we are given a function P : UU -> hProp and two points X, X' in the domain of this function. We also have two paths p and p' from these two points to different parts of the image of P, and we want to show that they end at the same point in the image of P.

To do this, we apply the total2\_paths\_equiv property, which states that if two paths in a graph have the same length and corresponding arrows satisfy certain conditions, then they must be equivalent. In our case, we define a function T : UU that maps each point x in UU to either x or X', depending on whether p(x) = p'(x') or not. We also define a path w from X to X' such that transportf P w p = p'. Finally, we show that the endpoints of p and p' are equal to the endpoints of T(p) and T(p'), respectively, and use this fact to apply total2\_paths\_equiv.

The proof is defined using Lean syntax and the local lemma property. The function P : UU -> hProp represents the graph, with points in the domain corresponding to points in UU. The two paths p and p' are given as arrows from X and X', respectively, to different parts of the image of P. The goal is to show that they end at the same point in the image of P.
#+end_src
#+begin_src output

The Local Lemma `weq1` (P : UU -> hProp) (X X' : UU)
(p : P X) (p' : P X')
: (X,, p) = (X',, p' : ∑ (T : UU), P T ) is a local lemma that states that the equivalence of two paths between objects in some category (P) is equivalent to the equivalence of their corresponding paths in another object (X') under a given function `transportf`. The lemma is defined using the `total2_paths_equiv` predicate, which takes two sets of paths in a category and returns true if they are equivalent.
#+end_src
#+begin_src output

The lemma you provided is a statement in the Haskell programming language that uses the "Local Lemma" pattern to prove an equation between two objects. The lemma takes three parameters: a function `P` from type `UU -> hProp`, which represents a predicate property of some type `UU`, two objects `X` and `X'` of type `UU`, and two functions `p` and `p'` that map to the predicate property. The lemma then uses the "Local Lemma" pattern to prove an equation between these objects, which is `(X,, p) = (X',, p') : ∑ (T : UU), P T`.

The proof of this equation uses the "total2\_paths\_equiv" function from some module or package, which is likely a helper function that provides the necessary machinery for proving such equations. The lemma then applies the "Local Lemma" pattern to define an object `w` of type `X = X'` and use the `transportf P w p = p'` equation to prove that the predicate property holds for this object, effectively proving the equation between the two objects `(X,, p) = (X',, p')`.
#+end_src
#+begin_src output
The Local Lemma (weq1) states that given a function P : UU -> hProp and two spaces X, X' of type UU, two points p, p' in these spaces, and a collection T of all possible paths from X to X', if the following conditions hold:

* P is defined on X, X' and P(X) = P(X')
* P is continuous on X and X'
* P is surjective on T
* P is injective on the preimage of each point p in X or p' in X'

Then:

* (X,, p) = (X',, p' : ∑ (T : UU), P T ) is equivalent to (∑ w : X = X', transportf P w p = p').

This lemma can be proved using the total2\_paths\_equiv relation.

The proof of Local Lemma (weq1) starts by defining a function transportf that maps any point w in X to its corresponding point in X'. This function is defined as follows:

* transportf P w p = p' if there exists a path from X to X' such that P(x) = p' for all x in the path.
* transportf P w p = undefined otherwise.

Then, the proof uses the total2\_paths\_equiv relation which states that two spaces are equivalent under continuous and surjective transformations if and only if they have the same number of paths between any two points. In this case, the transformation is defined by transportf P and it maps each point in X to its corresponding point in X'.

The proof then shows that transportf P is a continuous and surjective transformation, which means that (X,, p) = (X',, p') under the total2\_paths\_equiv relation.
#+end_src
#+begin_src output

It looks like you have provided a proof of the Local Lemma "weak equation 1" using Coq's `total2_paths_equiv` function. This is a valid way to prove this result in Coq. The proof shows that if we have two different ways to construct a sum of terms, then they are equivalent under a transport function. In this case, the transport function is defined as `transportf P w p = p'`, which maps a term `w` from the original construction to the corresponding term in the other construction.

The proof uses Coq's pattern matching and function definitions, and it takes advantage of the fact that `total2_paths_equiv` is a built-in equivalence relation for paths in a category. The `weak equation 1` itself is just a statement about two different constructions of the same object, and it states that they are equivalent under the transport function.

Overall, this proof demonstrates how Coq can be used to reason about algebraic structures and their relationships.
#+end_src
#+begin_src output

The local lemma with the given information is a statement that relates two paths in the category of sets and functions. The path on the left-hand side consists of two morphisms, P: UU -> hProp, X: UU, and p: P(X). On the right-hand side, there are also two morphisms, P': UU' -> hProp, X': UU', and p': P'(X'). The statement then says that if these two paths are equivalent in some sense (i.e., they are "totally equivalent"), then they are transported to each other under a specific function, which is defined by the application of total2\_paths\_equiv.

It is not possible for me to determine what this specific function is without more context or information about the category UU and the properties hProp, X, X', and p.
#+end_src

 *)

Local Lemma weq1  (P : UU -> hProp) (X X' : UU)
      (p : P X) (p' : P X')
  : (X,, p) = (X',, p' : ∑ (T : UU), P T )
    ≃
    (∑ w : X = X', transportf P w p = p').
Proof.
  apply total2_paths_equiv.
Defined.


(** This helper lemma is needed to show that our fibration
    is indeed a predicate, so that we can instantiate
    the hProposition [P] with this fibration.
*)

Local Lemma ident_is_prop (P : UU -> hProp) (X X' : UU)
      (p : P X) (p' : P X') (w : X = X')
  : isaprop (transportf P w p = p').
Proof.
  apply isapropifcontr.
  apply (pr2 (P X')).
Defined.


(** We construct the equivalence [weq2] as a projection
    from a total space, which, by the previous lemma, is
    a weak equivalence.
*)

Local Lemma weq2 (P : UU -> hProp) (X X' : UU)
      (p : P X) (p' : P X')
  : (∑ w : X = X', transportf P w p = p')
    ≃
    (X = X').
Proof.
  use weqpr1.
  intro. cbn. apply (pr2 (P X')).
Defined.

(**  Composing [weq1] and [weq2] yields the desired
     weak equivalence.
*)

Local Lemma Id_p_weq_Id (P : UU -> hProp) (X X' : UU)
      (p : P X) (p' : P X')
  : (X ,, p) = (X',, p' : ∑ T , P T)
    ≃
    X = X'.
Proof.
  set (f := weq1 P X X' p p').
  set (g := weq2 P X X' p p').
  set (fg := weqcomp f g).
  exact fg.
Defined.


(** ** Hlevel of path spaces *)

(**  We show that if [X] and [X'] are of hlevel [n], then so is their
      identity type [X = X'].
*)
(** The proof works differently for [n = 0] and [n = S n'],
    so we treat these two cases in separate lemmas
    [isofhlevel0pathspace] and [isofhlevelSnpathspace] and put them
    together in the lemma [isofhlevelpathspace].
*)

(** *** The case [n = 0] *)

Lemma iscontr_weq (X Y : UU)
  : iscontr X → iscontr Y → iscontr (X ≃ Y).
Proof.
  intros cX cY.
  exists (weqcontrcontr cX cY ).
  intro f.
  apply subtypePath.
  { exact isapropisweq. }
  apply funextfun. cbn. intro x. apply (pr2 cY).
Defined.

Lemma isofhlevel0pathspace (X Y : UU)
  : iscontr X -> iscontr Y -> iscontr (X = Y).
Proof.
  intros pX pY.
  set (H := isofhlevelweqb 0 (eqweqmap ,, univalenceAxiom X Y)).
  apply H. clear H.
  apply iscontr_weq;
    assumption.
Defined.


(** *** The case [n = S n'] *)

Lemma isofhlevelSnpathspace : ∏ n : nat, ∏ X Y : UU,
      isofhlevel (S n) Y -> isofhlevel (S n) (X = Y).
Proof.
  intros n X Y pY.
  set (H:=isofhlevelweqb (S n) (eqweqmap ,, univalenceAxiom X Y)).
  apply H.
  apply isofhlevelsnweqtohlevelsn.
  assumption.
Defined.


(** ** The lemma itself *)

Lemma isofhlevelpathspace : ∏ n : nat, ∏ X Y : UU,
      isofhlevel n X -> isofhlevel n Y -> isofhlevel n (X = Y).
Proof.
  intros n.
  induction n as [| n _ ].
  - intros X Y pX pY.
    apply isofhlevel0pathspace;
    assumption.
  - intros.
    apply isofhlevelSnpathspace;
    assumption.
Defined.


(** ** HLevel *)

(** We define the type [HLevel n] of types of hlevel n. *)

Definition HLevel (n : nat) : UU := ∑ X : UU, isofhlevel n X.

(** * Main theorem: [HLevel n] is of hlevel [S n] *)

Lemma isofhlevel_HLevel (n : nat) : isofhlevel (S n) (HLevel n).
Proof.
  cbn.
  intros X X'.
  induction X as [X p].
  induction X' as [X' p'].
  set (H := isofhlevelweqb n
       (Id_p_weq_Id (λ X, (isofhlevel n X,, isapropisofhlevel _ _)) X X' p p')).
  cbn in H.
  apply H.
  apply isofhlevelpathspace;
    assumption.
Defined.

(** ** Aside: Univalence for predicates and hlevels *)

(** As a corollary from [Id_p_weq_Id],
    we obtain a version of the Univalence Axiom for
    predicates on the universe [U].
    In particular, we can instantiate this predicate with
    [isofhlevel n].
*)

Lemma UA_for_Predicates (P : UU -> hProp) (X X' : UU)
     (pX : P X) (pX' : P X') :
  (tpair _ X pX) = (tpair P X' pX') ≃ (X ≃ X').
Proof.
  set (f := Id_p_weq_Id P X X' pX pX').
  set (g := tpair _ _ (univalenceAxiom X X')).
  exact (weqcomp f g).
Defined.

Corollary UA_for_HLevels : ∏ (n : nat) (X X' : HLevel n),
   (X = X') ≃ (pr1 X ≃ pr1 X').
Proof.
  intros n [X pX] [X' pX'].
  simpl.
  apply (UA_for_Predicates
       (λ X, tpair isaprop (isofhlevel n X)
                                      (isapropisofhlevel _ _))).
Defined.

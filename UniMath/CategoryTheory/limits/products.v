From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac Batch Debug.
(**

Direct implementation of indexed products together with:

- The general product functor ([product_functor])
- Definition of a product structure on a functor category by taking pointwise products in the target
  category (adapted from the binary version) ([Products_functor_precat])
- Products from limits ([Products_from_Lims])

Written by: Anders Mörtberg 2016


*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.limits.

Require Import UniMath.Combinatorics.StandardFiniteSets.

Local Open Scope cat.

(** * Definition of indexed products of objects in a precategory *)
Section product_def.

Context (I : UU) (C : category).

Definition isProduct (c : ∏ (i : I), C) (p : C)
  (pi : ∏ i, p --> c i) :=
  ∏ (a : C) (f : ∏ i, a --> c i),
    ∃! (fap : a --> p), ∏ i, fap · pi i = f i.

Definition Product (ci : ∏ i, C) :=
  ∑ pp1p2 : (∑ p : C, ∏ i, p --> ci i),
    isProduct ci (pr1 pp1p2) (pr2 pp1p2).

Definition Products := ∏ (ci : ∏ i, C), Product ci.
Definition hasProducts := ∏ (ci : ∏ i, C), ∥ Product ci ∥.

Definition ProductObject {c : ∏ i, C} (P : Product c) : C := pr1 (pr1 P).

Coercion ProductObject : Product >-> ob.

Definition ProductPr {c : ∏ i, C} (P : Product c) : ∏ i, P --> c i :=
  pr2 (pr1 P).

Definition isProduct_Product {c : ∏ i, C} (P : Product c) :
   isProduct c P (ProductPr P).
 Proof.
  exact (pr2 P).
Defined.

Definition ProductArrow {c : ∏ i, C} (P : Product c) {a : C} (f : ∏ i, a --> c i)
  : a --> P.
Proof.
  apply (pr1 (pr1 (isProduct_Product P _ f))).
Defined.

Lemma ProductPrCommutes (c : ∏ i, C) (P : Product c) :
     ∏ (a : C) (f : ∏ i, a --> c i) i, ProductArrow P f · ProductPr P i = f i.
Proof.
  intros a f i.
  apply (pr2 (pr1 (isProduct_Product P _ f)) i).
Qed.

Lemma ProductPr_idtoiso {i1 i2 : I} (a : I -> C) (P : Product a)
      (e : i1 = i2) :
  ProductPr P i1 · idtoiso (maponpaths a e) = ProductPr P i2.
Proof.
  induction e.
  apply id_right.
Qed.

Lemma ProductArrowUnique (c : ∏ i, C) (P : Product c) (x : C)
    (f : ∏ i, x --> c i) (k : x --> P)
    (Hk : ∏ i, k · ProductPr P i = f i) : k = ProductArrow P f.
Proof.
  set (H' := pr2 (isProduct_Product P _ f) (k,,Hk)).
  apply (base_paths _ _ H').
Qed.

Definition make_Product (a : ∏ i, C) :
  ∏ (c : C) (f : ∏ i, C⟦c,a i⟧), isProduct _ _ f -> Product a.
Proof.
  intros c f X.
  exact (tpair _ (c,,f) X).
Defined.

Definition make_isProduct (hsC : has_homsets C) (a : I -> C) (p : C)
  (pa : ∏ i, C⟦p,a i⟧) : (∏ (c : C) (f : ∏ i, C⟦c,a i⟧),
                                  ∃! k : C⟦c,p⟧, ∏ i, k · pa i = f i) ->
                              isProduct a p pa.
Proof.
intros H c cc; apply H.
Defined.

Lemma ProductArrowEta (c : ∏ i, C) (P : Product c) (x : C)
    (f : x --> P) :
    f = ProductArrow P (λ i, f · ProductPr P i).
Proof.
  now apply ProductArrowUnique.
Qed.

Proposition ProductArrow_eq
            {d : I → C}
            (w : C)
            (x : Product d)
            (f g : w --> x)
            (p : ∏ (i : I), f · ProductPr x i = g · ProductPr x i)
  : f = g.
Proof.
  refine (ProductArrowEta _ _ _ _ @ _ @ !(ProductArrowEta _ _ _ _)).
  apply maponpaths.
  use funextsec.
  exact p.
Qed.

Definition ProductOfArrows {c : ∏ i, C} (Pc : Product c) {a : ∏ i, C}
    (Pa : Product a) (f : ∏ i, a i --> c i) :
      Pa --> Pc :=
    ProductArrow Pc (λ i, ProductPr Pa i · f i).

Lemma ProductOfArrowsPr {c : ∏ i, C} (Pc : Product c) {a : ∏ i, C}
    (Pa : Product a) (f : ∏ i, a i --> c i) :
    ∏ i, ProductOfArrows Pc Pa f · ProductPr Pc i = ProductPr Pa i · f i.
Proof.
  unfold ProductOfArrows; intro i.
  now rewrite (ProductPrCommutes _ _ _ _ i).
Qed.

Lemma postcompWithProductArrow {c : ∏ i, C} (Pc : Product c) {a : ∏ i, C}
    (Pa : Product a) (f : ∏ i, a i --> c i)
    {x : C} (k : ∏ i, x --> a i) :
        ProductArrow Pa k · ProductOfArrows Pc Pa f =
        ProductArrow Pc (λ i, k i · f i).
Proof.
apply ProductArrowUnique; intro i.
now rewrite <- assoc, ProductOfArrowsPr, assoc, ProductPrCommutes.
Qed.

Lemma precompWithProductArrow {c : ∏ i, C} (Pc : Product c)
  {a : C} (f : ∏ i, a --> c i) {x : C} (k : x --> a)  :
       k · ProductArrow Pc f = ProductArrow Pc (λ i, k · f i).
Proof.
apply ProductArrowUnique; intro i.
now rewrite <- assoc, ProductPrCommutes.
Qed.

End product_def.

Section Products.

Context (I : UU) (C : category) (CC : Products I C).

Definition ProductOfArrows_comp (a b c : ∏ (i : I), C)
  (f : ∏ i, a i --> b i) (g : ∏ i, b i --> c i)
  : ProductOfArrows _ _ _ _ f · ProductOfArrows _ _ _ (CC _) g
    = ProductOfArrows _ _ (CC _) (CC _) (λ i, f i · g i).
Proof.
apply ProductArrowUnique; intro i.
rewrite <- assoc, ProductOfArrowsPr.
now rewrite assoc, ProductOfArrowsPr, assoc.
Qed.

End Products.

Section finite_products.

  Definition finite_products (C : category) := ∏ (n : nat), Products (stn n) C.

End finite_products.

Section Product_unique.

Context (I : UU) (C : category) (CC : Products I C) (a : ∏ (i : I), C).

Lemma Product_endo_is_identity (P : Product _ _ a)
  (k : P --> P)
  (H1 : ∏ i, k · ProductPr _ _ P i = ProductPr _ _ P i)
  : identity _ = k.
Proof.
  apply pathsinv0.
  eapply pathscomp0.
  apply ProductArrowEta.
  apply pathsinv0.
  apply ProductArrowUnique; intro i; apply pathsinv0.
  now rewrite id_left, H1.
Qed.

End Product_unique.

(** * The product functor: C^I -> C *)
Section product_functor.

Context (I : UU) {C : category} (PC : Products I C).

Definition product_functor_data :
  functor_data (power_category I C) C.
Proof.
use tpair.
- intros p.
  apply (ProductObject _ _ (PC p)).
- intros p q f.
  exact (ProductOfArrows _ _ _ _ f).
Defined.

Definition product_functor : functor (power_category I C) C.
Proof.
apply (tpair _ product_functor_data).
abstract (split;
  [ now intro x; simpl; apply pathsinv0, Product_endo_is_identity;
        intro i; rewrite ProductOfArrowsPr, id_right
  | now intros x y z f g; simpl; rewrite ProductOfArrows_comp]).
Defined.

End product_functor.

(* The product of a family of functors *)
Definition product_of_functors_alt
  (I : UU) {C D : category} (HD : Products I D)
  (F : ∏ (i : I), functor C D) : functor C D :=
   functor_composite (delta_functor I C)
     (functor_composite (family_functor _ F) (product_functor _ HD)).

(** * Products lift to functor categories *)
Section def_functor_pointwise_prod.

Context(I : UU) (C D : category) (HD : Products I D).

Section product_of_functors.

Context (F : I -> functor C D).

Definition product_of_functors_ob (c : C) : D :=
  HD (λ i, F i c).

Definition product_of_functors_mor (c c' : C) (f : c --> c') :
  product_of_functors_ob c --> product_of_functors_ob c' :=
    ProductOfArrows _ _ _ _ (λ i, # (F i) f).

Definition product_of_functors_data : functor_data C D.
Proof.
  exists product_of_functors_ob.
  exact product_of_functors_mor.
Defined.

Lemma is_functor_product_of_functors_data : is_functor product_of_functors_data.
Proof.
split; simpl; intros.
- unfold functor_idax; intros; simpl in *.
    apply pathsinv0.
    apply Product_endo_is_identity; intro i.
    unfold product_of_functors_mor.
    eapply pathscomp0; [apply (ProductOfArrowsPr _ _ (HD (λ i, (F i) a)))|].
    now simpl; rewrite functor_id, id_right.
- unfold functor_compax; simpl; unfold product_of_functors_mor.
  intros; simpl in *.
  apply pathsinv0.
  eapply pathscomp0.
  apply ProductOfArrows_comp.
  apply maponpaths, funextsec; intro i.
  now rewrite functor_comp.
Qed.

Definition product_of_functors : functor C D :=
  tpair _ _ is_functor_product_of_functors_data.

Lemma product_of_functors_alt_eq_product_of_functors :
  product_of_functors_alt _ HD F = product_of_functors.
Proof.
now apply (functor_eq _ _ D).
Qed.

Definition product_nat_trans_pr_data i (c : C) :
  D ⟦ product_of_functors c, (F i) c ⟧ :=
  ProductPr _ _ (HD (λ j, (F j) c)) i.

Lemma is_nat_trans_product_nat_trans_pr_data i :
  is_nat_trans _ _ (product_nat_trans_pr_data i).
Proof.
intros c c' f.
apply (ProductOfArrowsPr I _ (HD (λ i, F i c')) (HD (λ i, F i c))).
Qed.

Definition product_nat_trans_pr i : nat_trans product_of_functors (F i) :=
  tpair _ _ (is_nat_trans_product_nat_trans_pr_data i).

Section vertex.

(** The product morphism of a diagram with vertex [A] *)

Context (A : functor C D) (f : ∏ i, nat_trans A (F i)).

Definition product_nat_trans_data c :
  A c --> product_of_functors c:=
    ProductArrow _ _ _ (λ i, f i c).

Lemma is_nat_trans_product_nat_trans_data :
  is_nat_trans _ _ product_nat_trans_data.
Proof.
intros a b k; simpl.
eapply pathscomp0; [apply precompWithProductArrow|].
apply pathsinv0.
eapply pathscomp0; [apply postcompWithProductArrow|].
apply maponpaths, funextsec; intro i.
now rewrite (nat_trans_ax (f i)).
Qed.

Definition product_nat_trans : nat_trans A product_of_functors
  := tpair _ _ is_nat_trans_product_nat_trans_data.

End vertex.

Definition functor_precat_product_cone
  : Product I [C, D] F.
Proof.
use make_Product.
- apply product_of_functors.
- apply product_nat_trans_pr.
- use make_isProduct.
  + apply functor_category_has_homsets.
    Debug Off.
  + intros A f.
    use tpair.
    * apply (tpair _ (product_nat_trans A f)).
      abstract (intro i; apply (nat_trans_eq D); intro c;
                apply (ProductPrCommutes I D _ (HD (λ j, (F j) c)))).
    * abstract (
        intro t; apply subtypePath; simpl;
          [intro; apply impred; intro; apply (isaset_nat_trans D)|];
        apply (nat_trans_eq D); intro c;
        apply ProductArrowUnique; intro i;
        apply (nat_trans_eq_pointwise (pr2 t i))).
      Debug On.
Defined.

End product_of_functors.

Definition Products_functor_precat : Products I [C, D].
Proof.
intros F; apply functor_precat_product_cone.
Defined.

End def_functor_pointwise_prod.

(** * Products from limits *)
Section products_from_limits.

Context (I : UU) (C : category).

Definition I_graph : graph := (I,,λ _ _,empty).

Definition products_diagram (F : I → C) : diagram I_graph C.
Proof.
exists F.
abstract (intros u v e; induction e).
Defined.

Definition productscone c (F : I → C) (H : ∏ i, c --> F i) :
  cone (products_diagram F) c.
Proof.
use tpair.
+ intro v; apply H.
+ abstract (intros u v e; induction e).
Defined.

Lemma Products_from_Lims : Lims_of_shape I_graph C -> Products I C.
Proof.
intros H F.
set (HF := H (products_diagram F)).
use make_Product.
+ apply (lim HF).
+ intros i; apply (limOut HF).
+ apply (make_isProduct _ _ C); intros c Fic.
  use unique_exists.
  - apply limArrow.
    use make_cone.
    * simpl; intro i; apply Fic.
    * abstract (simpl; intros u v e; induction e).
  - abstract (simpl; intro i; apply (limArrowCommutes HF)).
  - abstract (intros y; apply impred; intro i; apply C).
  - abstract (intros f Hf; apply limArrowUnique; simpl in *; intros i; apply Hf).
Defined.

End products_from_limits.

(**
 Products are closed under iso

#+begin_src output
This is a Coq code definition for an "isProduct\_z\_iso" predicate. It takes as input:

* A category C
* A set of objects J
* A function from J to C, D
* Two objects x and y in C
* An object h that represents the z-iso between x and y
* Two functions px and py that map each object j in J to an element of C and D respectively
* The predicate Hx that states that (px,py) is a product arrow from J to D for x
* The predicate q that states that (py j = inv\_from\_z\_iso h · px j) for all objects j in J.

The predicate asserts that the pair of functions (f,h) defined by f=px and h=py is a product arrow
from J to D for y, where f is defined using the function px and h is the z-iso defined by
inv\_from\_z\_iso. The predicate uses several other definitions and lemmas, such as "make\_Product"
and "invproofirrelevance".

#+end_src
#+begin_src output

The definition "isProduct\_z\_iso" is a Coq proof that takes several parameters, including a category C, a set of objects J, a function D from J to C, two objects x and y in C, a z-iso h between x and y, functions px and py mapping elements of J to the corresponding elements in C, and the assumptions "Hx" and "q".

The proof begins by using the "make\_isProduct" module to construct an instance of the product arrow type with x and y as objects and px and py as morphisms. It then applies the homset property to verify that the constructed instance is a valid product arrow.

The abstract definition "iscontraprop1" is then invoked to show that if two z-isos h1 and h2 are such that h1(x) = h2(x) for all x in C, and f is any morphism between the domains of h1 and h2, then f is a contraction if and only if h1(y) = h2(y) for all y in C. This is done by introducing a new parameter j and applying a series of rewrites to show that the maponpaths function can be used to derive the desired conclusion.

The final refinement of the proof defines a product arrow between the domain of px on J and the codomain of py on J, with f being the composite of px and h. The proof then applies the ProductPrCommutes property to verify that this product arrow is equivalent to the constructed instance in "make\_isProduct".

Overall, this definition demonstrates how Coq can be used to construct and prove properties about products and z-isos in a category theory setting.
#+end_src
#+begin_src output
This is a definition of the `isProduct_z_iso` relation in the Coq library. It takes several parameters, including a category C, a family J of objects, a function D from J to C, two elements x and y in C, a z-iso h between x and y, and functions px and py that define products over J. The `isProduct_z_iso` relation then checks if x and y are isomorphic as products over J using the z-iso h and px and py functions.

The proof of this definition uses the `make_isProduct` function from Coq to construct a product object for x and y using the `ProductArrow` constructor, and then shows that this product object satisfies the conditions for isomorphic products in the category C using the `ProductPrCommutes` property.
#+end_src
#+begin_src output

It looks like you have defined a Coq type `isProduct_z_iso` with some arguments and constraints. It appears to be an implementation of the isomorphism class of products in a given category with respect to a z-iso, which is a special kind of isomorphism in category theory.

The definition uses some other Coq types and definitions such as `Category`, `ProductArrow`, `iscontraprop1`, and `make_Product`. It also references some additional arguments such as `C : category`, `J : UU`, `D : J -> C`, `x y : C`, `h : z_iso x y`, `px : ∏ (j : J), x -> D j`, `py : ∏ (j : J), y -> D j`, and `Hx : isProduct J _ D x px`.

The proof uses the `make_isProduct` function to check that the defined type satisfies certain properties. It also uses some other Coq tactics such as `homset_property`, `invproofirrelevance`, and `maponpaths`.

It's not clear from the code snippet you provided what the purpose of this definition is or how it might be used in a larger context, but it seems to implement an important concept in category theory.
#+end_src
#+begin_src output
The `isProduct_z_iso` definition is a statement about products in the category `C`, where `J` is an arbitrary set and `D: J → C` is a function. The `z_iso_x_y` parameter is a z-iso between two objects `x, y` in `C`.

The function takes additional parameters, including `px` and `py`, which are functions that map each object `j` of `J` to an object in `C` and vice versa. The `Hx` parameter is a proof that the function `D` satisfies the property of being a product function for the z-iso `z_iso_x_y` and the objects `x, y`.

The definition then applies the `make_isProduct` function to construct a proof that the function `D` satisfies the property of being a product function for the z-iso `z_iso_x_y` and the objects `y, py`, given the proofs `px` and `py`.

The proof uses homset properties and the definition of the `iscontraprop1` lemma to construct a contradiction if the hypothesis that `D` is not a product function for the z-iso `z_iso_x_y` and the objects `y, py`, given the proofs `px` and `py`, were to be true. The resulting proof demonstrates that `D` must indeed satisfy the property of being a product function for the z-iso `z_iso_x_y` and the objects `y, py`.

The `isProduct_z_iso` definition is used in Coq to prove statements about products in the category `C` that involve a z-iso.
#+end_src
#+begin_src output

The definition isProduct\_z\_iso is a Coq function that defines an instance of the `isProduct` predicate for a given category, UU, and function D. It takes several arguments:

* C: The category to which the product belongs.
* J: A family of objects from the universe UU.
* D: A function from J to C that assigns each object in J to an element in C.
* x y: Two elements in C for which we want to check if they are elements of a product.
* h: An iso between the category C and some other category.
* px, py: Homomorphisms from J to C that assign each object in J to an element in C.
* Hx: A proof that x is an element of the product.
* q: A proof that y is also an element of the product.

The function returns a proof that y is an element of the product, using the `isProduct` predicate.

The function first uses the `make_isProduct` function from the Coq library to create a proof that x and y are elements of the product. It then applies homset properties to prove that the homomorphisms px and py assign to each object in J an element in C, and that these elements satisfy the iso h. Finally, it uses contrapositive reasoning to prove that if px j = D j inv\_from\_z\_iso h pj, then py j = D j px j = D j (pr2 φ₁ j @ !(pr2 φ₂ j)) for any object j in J and any element pj in C. This completes the proof that y is an element of the product.
#+end_src
#+begin_src output
This Coq definition defines an instance of the iso\_product type for a given category, closed under a specified isomorphism. The type iso\_product represents objects that are preserved under an isomorphism.

The definition uses a make\_isProduct function to create the iso\_product instance. It applies the homset\_property and subtypePath properties to ensure that the category has an isomorphism group, and it uses the invproofirrelevance lemma to prove that the isomorphism is not irrelevant to the type of the objects being mapped.

The definition also defines a function ProductArrow\_eq that maps arrows in the source object to arrows in the target object under an isomorphism. This function is used to construct the arrow f \* h for the given isomorphism and arbitrary function f.

Finally, the definition uses the ProductPrCommutes property to prove that products of objects preserved under an isomorphism are also preserved under the same isomorphism.
#+end_src
#+begin_src output
```
 Product isomorphism under category equivalence
Definition isProduct_z_iso : Category C => (J : UU) =>
                                (D : J -> C) => x y : C =>
                                (h : z_iso x y) => px py : J -> x -> D x, y -> D y =>
                                Hx : isProduct J _ D x px =>
                                q : forall j : J, py j = inv_from_z_iso h * px j =>
                                isProduct J _ D y py.
Proof.
  use make_isProduct.
  {
    apply homset_property.
  }
  Debug Off.
  intros z f.
  Debug Off. use iscontraprop1. Debug On.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; use impred ; intro ; apply homset_property | ] ;
       use (cancel_z_iso _ _ (z_iso_inv h)) ;
       use (ProductArrow_eq _ _ _ _ Hx) ; cbn ;
       intro j ;
       rewrite !assoc' ;
       rewrite <- q ;
       exact (pr2 φ₁ j @ !(pr2 φ₂ j))).
  - Debug Off. refine (ProductArrow _ _ (make_Product _ _ _ _ _ Hx) f · h ,, _). Debug On.

    abstract
      (intro j ;
       rewrite !assoc' ;
       rewrite q ;
       rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)) ;
       rewrite z_iso_inv_after_z_iso ;
       rewrite id_left ;
       apply ProductPrCommutes).
Defined.
```
#+end_src

 *)
Definition isProduct_z_iso
           {C : category}
           {J : UU}
           (D : J → C)
           {x y : C}
           (h : z_iso x y)
           (px : ∏ (j : J), x --> D j)
           (py : ∏ (j : J), y --> D j)
           (Hx : isProduct J _ D x px)
           (q : ∏ (j : J), py j = inv_from_z_iso h · px j)
  : isProduct J _ D y py.
Proof.
  use make_isProduct.
  {
    apply homset_property.
  }
  Debug Off.
  intros z f.
  Debug Off. use iscontraprop1. Debug On.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; use impred ; intro ; apply homset_property | ] ;
       use (cancel_z_iso _ _ (z_iso_inv h)) ;
       use (ProductArrow_eq _ _ _ (make_Product _ _ _ _ _ Hx)) ; cbn ;
       intro j ;
       rewrite !assoc' ;
       rewrite <- q ;
       exact (pr2 φ₁ j @ !(pr2 φ₂ j))).
  - Debug Off. refine (ProductArrow _ _ (make_Product _ _ _ _ _ Hx) f · h ,, _). Debug On.

    abstract
      (intro j ;
       rewrite !assoc' ;
       rewrite q ;
       rewrite (maponpaths (λ z, _ · z) (assoc _ _ _)) ;
       rewrite z_iso_inv_after_z_iso ;
       rewrite id_left ;
       apply ProductPrCommutes).
Defined.

(**
 Products are unique
 *)
Definition eq_Product
           {C : category}
           {J : UU}
           {D : J → C}
           (prod₁ prod₂ : Product J C D)
           (q : ProductObject _ _ prod₁ = ProductObject _ _ prod₂)
           (e : ∏ (j : J),
                ProductPr _ _ prod₁ j
                =
                idtoiso q · ProductPr _ _ prod₂ j)
  : prod₁ = prod₂.
Proof.
  use subtypePath.
  {
    intro.
    repeat (use impred ; intro).
    use isapropiscontr.
  }
  use total2_paths_f.
  - exact q.
  - rewrite transportf_sec_constant.
    use funextsec.
    intro j.
    rewrite <- !idtoiso_precompose.
    rewrite !idtoiso_inv.
    use z_iso_inv_on_right.
    exact (e j).
Qed.

Definition z_iso_between_Product
           {C : category}
           {J : UU}
           {D : J → C}
           (prod₁ prod₂ : Product J C D)
  : z_iso prod₁ prod₂.
Proof.
  use make_z_iso.
  - exact (ProductArrow _ _  prod₂ (ProductPr _ _ prod₁)).
  - exact (ProductArrow _ _  prod₁ (ProductPr _ _ prod₂)).
  - split.
    + abstract
        (use ProductArrow_eq ;
         intro j ;
         rewrite !assoc' ;
         rewrite !ProductPrCommutes ;
         rewrite id_left ;
         apply idpath).
    + abstract
        (use ProductArrow_eq ;
         intro j ;
         rewrite !assoc' ;
         rewrite !ProductPrCommutes ;
         rewrite id_left ;
         apply idpath).
Defined.

Definition isaprop_Product
           {C : category}
           (HC : is_univalent C)
           (J : UU)
           (D : J → C)
  : isaprop (Product J C D).
Proof.
  use invproofirrelevance.
  intros p₁ p₂.
  use eq_Product.
  - refine (isotoid _ HC _).
    apply z_iso_between_Product.
  - rewrite idtoiso_isotoid ; cbn.
    intro j.
    rewrite ProductPrCommutes.
    apply idpath.
Qed.

Definition isProduct_eq_arrow
           {C : category}
           {J : UU}
           {D : J → C}
           {ys : C}
           {π π' : ∏ (j : J), ys --> D j}
           (q : ∏ (j : J), π j = π' j)
           (H : isProduct J C D ys π)
  : isProduct J C D ys π'.
Proof.
  intros w f.
  Debug Off. use iscontraprop1. Debug On.
  - abstract
      (use invproofirrelevance ;
       intros φ₁ φ₂ ;
       use subtypePath ; [ intro ; use impred ; intro ; apply homset_property | ] ;
       use (ProductArrow_eq _ _ _ (make_Product _ _ _ _ _ H)) ;
       intro j ; cbn ;
       rewrite !q ;
       exact (pr2 φ₁ j @ !(pr2 φ₂ j))).
  - simple refine (_ ,, _).
    + exact (ProductArrow _ _ (make_Product _ _ _ _ _ H) f).
    + abstract
        (cbn ;
         intro j ;
         rewrite <- q ;
         apply (ProductPrCommutes _ _ _ (make_Product _ _ _ _ _ H))).
Defined.

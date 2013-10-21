
Require Import
Utf8
Coq.Classes.Init
Coq.Program.Basics Coq.Program.Tactics
Setoid
.

Set Implicit Arguments.


Reserved Notation "X ⟶ Y" (at level 60, right associativity).
Reserved Notation "g ◦ f" (at level 60, right associativity).
Class Category :=
  { obj: Type;
    arr (X Y: obj): Setoid where "X ⟶ Y" := (arr X Y);

    compose {X Y Z: obj}:
      (X ⟶ Y) -> (Y ⟶ Z) -> (X ⟶ Z) where "g ◦ f" := (compose f g);

    id {X: obj}: X ⟶ X;

    compose_assoc:
      forall (X Y Z W: obj)(f: X ⟶ Y)(g: Y ⟶ Z)(h: Z ⟶ W),
        (h◦g)◦f == h◦(g◦f);
    compose_subst:
      forall (X Y Z: obj)(f f': X ⟶ Y)(g g': Y ⟶ Z)
         (Heq_fst: f == f')(Heq_snd: g == g'),
        g◦f == g'◦f';

    id_dom: (* renamed from id_left *)
      forall (X Y: obj)(f: X ⟶ Y), compose id f == f;
    id_cod: (* renamed from id_rigth *)
      forall (X Y: obj)(f: X ⟶ Y), compose f id == f }.
Coercion obj: Category >-> Sortclass.
Notation "X ⟶ Y" := (arr X Y) (at level 60, right associativity).
Notation "g ◦ f" := (compose f g) (at level 60, right associativity).
Definition id_ {C: Category}(X: C) := id (X:=X).

Lemma compose_subst_fst:
  forall (C: Category)(X Y Z: C)(f f': X ⟶ Y)(g: Y ⟶ Z),
    f == f' -> g◦f == g◦f'.
Proof.
  
  intros.
  apply compose_subst; [ apply H | equiv_refl ].
Qed.

Lemma compose_subst_snd:
  forall (C: Category)(X Y Z: C)(f: X ⟶ Y)(g g': Y ⟶ Z),
    g == g' -> g◦f == g'◦f.
Proof.
  intros.
  apply compose_subst; [ equiv_refl | apply H ].
Qed.


Program Instance op_Category (C: Category): Category :=
  { obj := obj ;
    arr X Y := arr Y X;
    compose X Y Z f g := f ◦ g;
    id X := id }.
Next Obligation.
  equiv_symm; apply compose_assoc.
Qed.
Next Obligation.
  apply compose_subst; auto.
Qed.
Next Obligation.
  apply id_cod.
Qed.
Next Obligation.
  apply id_dom.
Qed.
Notation "C ^^op" := (op_Category C) (at level 5, left associativity).


Section CategoryProperties.
  Context (C: Category).

  Definition mono {X Y: C}(f: X ⟶ Y) :=
    forall (Z: C)(g h: Y ⟶ Z),
      g◦f == h◦f -> g == h.
  
  Definition epi {X Y: C}(f: X ⟶ Y) :=
    forall (U: C)(g h: U ⟶ X),
      f◦g == f◦h -> g == h.
  
  Definition iso {X Y: C}(f: X ⟶ Y)(g: Y ⟶ X) :=
    g◦f == id ∧ f◦g == id.

  Definition Iso (X Y: C) :=
    exists (f: X ⟶ Y)(g: Y ⟶ X), iso f g.
  Notation "X ≃ Y" := (Iso X Y) (at level 70, no associativity).
  

  Class Initial (I: C) :=
    { In (X:C): I ⟶ X;

      In_uniqueness:
        forall (X: C)(f: I ⟶ X), In X == f }.
  Coercion In: Initial >-> Funclass.

  Class Terminal (T: C) :=
    { Te (X: C): X ⟶ T;

      Te_uniqueness:
        forall (X: C)(f: X ⟶ T), Te X == f }.
  Coercion Te: Terminal >-> Funclass.

  Class Null (Z: C) :=
    { null_initial:> Initial Z;
      null_terminal:> Terminal Z }.

  
  Class Product (X Y: C) :=
    { product: C;
      
      proj_X: product ⟶ X;
      proj_Y: product ⟶ Y;
      
      product_arr (Q: C)(f: Q ⟶ X)(g: Q ⟶ Y): Q ⟶ product;
      
      product_arr_property_X:
        forall (Q: C)(f: Q ⟶ X)(g: Q ⟶ Y),
          proj_X ◦ (product_arr Q f g) == f;

      product_arr_property_Y:
        forall (Q: C)(f: Q ⟶ X)(g: Q ⟶ Y),
          proj_Y ◦ (product_arr Q f g) == g;

      product_arr_universality:
        forall (Q: C)(f: Q ⟶ X)(g: Q ⟶ Y)(h: Q ⟶ product),
          proj_X ◦ h == f -> proj_Y ◦ h == g ->
          product_arr Q f g == h }.
  Coercion product: Product >-> obj.

  Class CoProduct (X Y: C) :=
    { coproduct: C;
      
      in_X: X ⟶ coproduct;
      in_Y: Y ⟶ coproduct;
      
      coproduct_arr (Q: C)(f: X ⟶ Q)(g: Y ⟶ Q): coproduct ⟶ Q;
      
      coproduct_arr_property_X:
        forall (Q: C)(f: X ⟶ Q)(g: Y ⟶ Q),
          (coproduct_arr Q f g) ◦ in_X == f;

      coproduct_arr_property_Y:
        forall (Q: C)(f: X ⟶ Q)(g: Y ⟶ Q),
          (coproduct_arr Q f g) ◦ in_Y == g;

      coproduct_arr_universality:
        forall (Q: C)(f: X ⟶ Q)(g: Y ⟶ Q)(h: coproduct ⟶ Q),
          h ◦ in_X == f -> h ◦ in_Y == g ->
          coproduct_arr Q f g == h }.
  Coercion coproduct: CoProduct >-> obj.

End CategoryProperties.


Lemma Initial_unique_up_to_iso:
  forall (C: Category) I I' (Init: Initial C I)(Init': Initial C I'), 
    Iso C I I'.
Proof.
  intros C I I' Init Init'.
  unfold Iso, iso.
  exists (Init I'), (Init' I).
  split.
  - equiv_trns_with (Init I); auto.
    + equiv_symm; auto.
      apply In_uniqueness.
    + apply In_uniqueness.
  - equiv_trns_with (Init' I'); auto.
    + equiv_symm; auto.
      apply In_uniqueness.
    + apply In_uniqueness.
Qed.

Lemma Terminal_unique_up_to_iso:
  forall (C: Category) T T' (Term: Terminal C T)(Term': Terminal C T'),
    Iso C T T'.
Proof.
  intros.
  unfold Iso, iso in *.
  exists (Term' T), (Term T'); split.
  - equiv_trns_with (Term T); auto.
    + equiv_symm; auto.
      apply Te_uniqueness.
    + apply Te_uniqueness.
  - equiv_trns_with (Term' T'); auto.
    + equiv_symm; auto.
      apply Te_uniqueness.
    + apply Te_uniqueness.
Qed.

Program Instance  Initial_dual_Terminal {C: Category}{I: C}(Init: Initial C I)
: Terminal C ^^op I :=
  { Te X := Init X }.
Next Obligation.
  apply In_uniqueness.
Qed.

Program Instance  Terminal_dual_Initial {C: Category}{T: C}(Term: Terminal C T)
: Initial C ^^op T :=
  { In X := Term X }.
Next Obligation.
  apply Te_uniqueness.
Qed.

Program Instance Product_dual_CoProduct
        {C: Category}{X Y: C}(prod: Product C X Y)
: CoProduct C ^^op X Y :=
  { coproduct := prod;
    in_X := proj_X (Product:=prod);
    in_Y := proj_Y (Product:=prod);
    coproduct_arr X := product_arr (Product:=prod) X }.
Next Obligation.
  apply product_arr_property_X.
Qed.
Next Obligation.
  apply product_arr_property_Y.
Qed.
Next Obligation.
  apply product_arr_universality; auto.
Qed.

Program Instance CoProduct_dual_Product
        {C: Category}{X Y: C}(coprod: CoProduct C X Y)
: Product C ^^op X Y :=
  { product := coprod;
    proj_X := in_X (CoProduct:=coprod);
    proj_Y := in_Y (CoProduct:=coprod);
    product_arr X := coproduct_arr (CoProduct:=coprod) X }.
Next Obligation.
  apply coproduct_arr_property_X.
Qed.
Next Obligation.
  apply coproduct_arr_property_Y.
Qed.
Next Obligation.
  apply coproduct_arr_universality; auto.
Qed.


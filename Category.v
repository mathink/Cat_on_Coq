Require Import 
Ssreflect.ssreflect
Ssreflect.eqtype
Ssreflect.ssrbool
Setoid.

Set Implicit Arguments.
Unset Strict Implicit.

Reserved Notation "X --> Y" (at level 60, right associativity).
Reserved Notation "g • f" (at level 60, right associativity).

Class Category_Spec (obj: Type)(arr: obj -> obj -> Setoid) :=
  { notation_01 := tt where  "X --> Y" := (arr X Y);
    compose {X Y Z: obj}:
      (arr X Y) -> (Y --> Z) -> (X --> Z) where "g • f" := (compose f g);

    id {X: obj}: X --> X;

    compose_assoc:
      forall (X Y Z W: obj)(f: X --> Y)(g: Y --> Z)(h: Z --> W),
        (h•g)•f === h•(g•f);

    compose_subst:
      forall (X Y Z: obj)(f f': X --> Y)(g g': Y --> Z)
         (Heq_fst: f === f')(Heq_snd: g === g'),
        g•f === g'•f';

    id_dom: (* renamed from id_left *)
      forall (X Y: obj)(f: X --> Y), compose id f === f;
    id_cod: (* renamed from id_rigth *)
      forall (X Y: obj)(f: X --> Y), compose f id === f }.

Structure Category :=
  make_Category
  { obj:> Type;
    arr (X Y: obj): Setoid;
    category_spec:> Category_Spec arr }.
Notation Hom C X Y := (arr (c:=C) X Y).
Coercion make_Category: Category_Spec >-> Category.
Existing Instance category_spec.
Arguments arr {category}(X Y): rename.
Arguments compose {obj arr spec}{X Y Z}(f g): rename.
Arguments id {obj arr spec}{X}: rename.
Notation "X --> Y" := (arr X Y) (at level 60, right associativity).
Notation "g • f" := (compose f g) (at level 60, right associativity).
Definition id_ {C: Category}(X: C) := @id C _ C X.

Lemma compose_subst_fst:
  forall (C: Category)(X Y Z: C)(f f': X --> Y)(g: Y --> Z),
    f === f' -> g•f === g•f'.
Proof.
  move=> C X Y Z f f' g Heq; apply: compose_subst;
         [ apply Heq | equiv_refl ].
Qed.

Lemma compose_subst_snd:
  forall (C: Category)(X Y Z: C)(f: X --> Y)(g g': Y --> Z),
    g === g' -> g•f === g'•f.
Proof.
  move=> C X Y Z f g g' Heq.
  apply: compose_subst; [ equiv_refl | apply Heq ].
Qed.


Program Definition op_Category (C: Category): Category :=
  {| compose X Y Z f g := compose (spec:=C) g f;
     id X := id_ (C:=C) X |}.
Next Obligation.
  equiv_symm; apply compose_assoc.
Qed.
Next Obligation.
  apply compose_subst; done.
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

  Definition mono {X Y: C}(f: X --> Y) :=
    forall (Z: C)(g h: Y --> Z),
      g•f === h•f -> g === h.
  
  Definition epi {X Y: C}(f: X --> Y) :=
    forall (U: C)(g h: U --> X),
      f•g === f•h -> g === h.
  
  Definition iso {X Y: C}(f: X --> Y)(g: Y --> X) :=
    g•f === id /\ f•g === id.

  Definition Iso (X Y: C) :=
    exists (f: X --> Y)(g: Y --> X), iso f g.
  Notation "X ≃ Y" := (Iso X Y) (at level 70, no associativity).
  

  Class Initial_Spec (I: C) :=
    { initial_arr: forall (X: C), I --> X;
      initiality:
        forall (X: C)(f: I --> X), initial_arr X === f }.

  Class Terminal_Spec (T: C) :=
    { terminal_arr: forall (X: C), X --> T;
      terminality:
        forall (X: C)(f: X --> T), terminal_arr X === f }.

  Structure Initial :=
    make_Initial
    { initial_obj:> C;
      initial_spec:> Initial_Spec initial_obj }.
  Existing Instance initial_spec.

  Structure Terminal :=
    make_Terminal
    { terminal_obj:> C;
      terminal_spec:> Terminal_Spec terminal_obj }.
  Existing Instance terminal_spec.

  Structure NullObj :=
    make_Null
    { null_obj:> C;
      null_initial_spec:> Initial_Spec null_obj;
      null_terminal_spec:> Terminal_Spec null_obj }.
  
  Class Product_Spec (X Y XY: C) :=
    { proj_X: XY --> X;
      proj_Y: XY --> Y;
      
      product_arr (Q: C)(f: Q --> X)(g: Q --> Y): Q --> XY;
      
      product_arr_property_X:
        forall (Q: C)(f: Q --> X)(g: Q --> Y),
          proj_X • (product_arr f g) === f;

      product_arr_property_Y:
        forall (Q: C)(f: Q --> X)(g: Q --> Y),
          proj_Y • (product_arr f g) === g;

      product_universality:
        forall (Q: C)(f: Q --> X)(g: Q --> Y)(h: Q --> XY),
          proj_X • h === f -> proj_Y • h === g ->
          product_arr f g === h }.

  Lemma product_uniqueness:
    forall (X Y P Q: C),
      Product_Spec X Y P -> Product_Spec X Y Q ->
      Iso P Q.
  Proof.
    move=> X Y P Q p1 p2; rewrite /Iso /iso.
    exists (product_arr (Q:=P) proj_X proj_Y).
    exists (product_arr (Q:=Q) proj_X proj_Y).
    split.
    - apply transitivity with (product_arr (Q:=P) proj_X proj_Y);
      [| apply product_universality; apply id_dom].
      apply symmetry. 
      apply product_universality.
      + eapply transitivity;
        [ apply symmetry; apply compose_assoc |].
        eapply transitivity;
        [ apply compose_subst_snd; apply product_arr_property_X |].
        apply product_arr_property_X.
      + eapply transitivity;
        [ apply symmetry; apply compose_assoc |].
        eapply transitivity;
        [ apply compose_subst_snd; apply product_arr_property_Y |].
        apply product_arr_property_Y.
    - apply transitivity with (product_arr (Q:=Q) proj_X proj_Y);
      [| apply product_universality; apply id_dom].
      apply symmetry.
      apply product_universality.
      + eapply transitivity;
        [ apply symmetry; apply compose_assoc |].
        eapply transitivity;
        [ apply compose_subst_snd; apply product_arr_property_X |].
        apply product_arr_property_X.
      + eapply transitivity;
        [ apply symmetry; apply compose_assoc |].
        eapply transitivity;
        [ apply compose_subst_snd; apply product_arr_property_Y |].
        apply product_arr_property_Y.
  Qed.        
        
  Lemma product_arr_subst:
    forall (X Y P: C)(H: Product_Spec X Y P)
           (Q: C)(f f': Q --> X)(g g': Q --> Y),
      f === f' -> g === g' ->
      product_arr f g === product_arr f' g'.
  Proof.
    move=> X Y P H Q f f' g g' Heqf Heqg.
    by apply product_universality;
      [apply transitivity with f' | apply transitivity with g'];
      [ apply product_arr_property_X | apply symmetry |
        apply product_arr_property_Y | apply symmetry ].
  Qed.

  Lemma product_arr_subst_X:
    forall (X Y P: C)(H: Product_Spec X Y P)
           (Q: C)(f f': Q --> X)(g: Q --> Y),
      f === f' ->
      product_arr f g === product_arr f' g.
  Proof.
    by move=> *; apply product_arr_subst; try equiv_refl.
  Qed.

  Lemma product_arr_subst_Y:
    forall (X Y P: C)(H: Product_Spec X Y P)
           (Q: C)(f: Q --> X)(g g': Q --> Y),
      g === g' ->
      product_arr f g === product_arr f g'.
  Proof.
    by move=> *; apply product_arr_subst; try equiv_refl.
  Qed.

  Structure Product (X Y: C) :=
    make_Product
    { product:> C;
      product_spec:> Product_Spec X Y product }.
  Existing Instance product_spec.

  Class CoProduct_Spec (X Y coprod: C) :=
    { in_X: X --> coprod;
      in_Y: Y --> coprod;
      
      coproduct_arr (Q: C)(f: X --> Q)(g: Y --> Q): coprod --> Q;
      
      coproduct_arr_property_X:
        forall (Q: C)(f: X --> Q)(g: Y --> Q),
          (coproduct_arr f g) • in_X === f;

      coproduct_arr_property_Y:
        forall (Q: C)(f: X --> Q)(g: Y --> Q),
          (coproduct_arr f g) • in_Y === g;

      coproduct_universality:
        forall (Q: C)(f: X --> Q)(g: Y --> Q)(h: coprod --> Q),
          h • in_X === f -> h • in_Y === g ->
          coproduct_arr f g === h }.

  Lemma coproduct_arr_subst:
    forall (X Y P: C)(H: CoProduct_Spec X Y P)
           (Q: C)(f f': X --> Q)(g g': Y --> Q),
      f === f' -> g === g' ->
      coproduct_arr f g === coproduct_arr f' g'.
  Proof.
    move=> X Y P H Q f f' g g' Heqf Heqg.
    by apply coproduct_universality;
      [apply transitivity with f' | apply transitivity with g'];
      [ apply coproduct_arr_property_X | apply symmetry |
        apply coproduct_arr_property_Y | apply symmetry ].
  Qed.

  Lemma coproduct_arr_subst_X:
    forall (X Y P: C)(H: CoProduct_Spec X Y P)
           (Q: C)(f f': X --> Q)(g: Y --> Q),
      f === f' ->
      coproduct_arr f g === coproduct_arr f' g.
  Proof.
    by move=> *; apply coproduct_arr_subst; try equiv_refl.
  Qed.

  Lemma coproduct_arr_subst_Y:
    forall (X Y P: C)(H: CoProduct_Spec X Y P)
           (Q: C)(f: X --> Q)(g g': Y --> Q),
      g === g' ->
      coproduct_arr f g === coproduct_arr f g'.
  Proof.
    by move=> *; apply coproduct_arr_subst; try equiv_refl.
  Qed.

  Structure CoProduct (X Y: C) :=
    make_CoProduct
    { coproduct:> C;
      coproduct_spec:> CoProduct_Spec X Y coproduct }.
  Existing Instance coproduct_spec.

(* exponential *)
  Class hasProduct :=
    { prod (X Y: C):> Product X Y;
      prod_arr {X Y Z W: C}(f: X --> Z)(g: Y --> W)
      : prod X Y --> prod Z W
      := product_arr (f•proj_X) (g•proj_Y)
    }.

  Class hasCoProduct :=
    { coprod (X Y: C):> CoProduct X Y;
      coprod_arr {X Y Z W: C}(f: X --> Z)(g: Y --> W)
      : coprod X Y --> coprod Z W 
      := coproduct_arr (in_X•f) (in_Y•g)
    }.

End CategoryProperties.

Arguments initial_arr {C I}(spec X): rename.
Arguments terminal_arr {C T}(spec X): rename.
Arguments proj_X {C X Y prod}(spec): rename.
Arguments proj_Y {C X Y coprod}(spec): rename.
Arguments product_arr {C X Y XY}(spec Q f g): rename.
Arguments in_X {C X Y XY}(spec): rename.
Arguments in_Y {C X Y XY}(spec): rename.
Arguments coproduct_arr {C X Y XY}(spec Q f g): rename.
  Existing Instance coproduct_spec.

Coercion make_Initial: Initial_Spec >-> Initial.
Coercion make_Terminal: Terminal_Spec >-> Terminal.
Coercion make_Product: Product_Spec >-> Product.
Coercion make_CoProduct: CoProduct_Spec >-> CoProduct.


Lemma Initial_unique_up_to_iso:
  forall (C: Category)(I I': C),
    Initial_Spec I -> Initial_Spec I' ->
    Iso I I'.
Proof.
  move=> C I I' HInit HInit'; rewrite /Iso /iso.
  exists (initial_arr HInit I'), (initial_arr HInit' I).
  split.
  - apply transitivity with (initial_arr HInit I); auto.
    + apply symmetry, initiality.
    + apply initiality.
  - apply transitivity with (initial_arr HInit' I'); auto.
    + apply symmetry, initiality.
    + apply initiality.
Qed.

Theorem Initial_uniqueness:
  forall (C: Category)(I I': Initial C),
    Iso I I'.
Proof.
  move=> C I I'.
  by apply Initial_unique_up_to_iso; [apply I | apply I'].
Qed.

Lemma Terminal_unique_up_to_iso:
  forall (C: Category)(T T': C),
    Terminal_Spec T -> Terminal_Spec T' ->
    Iso T T'.
Proof.
  move=> C T T' Hterm Hterm'; rewrite /Iso /iso.
  exists (terminal_arr Hterm' T), (terminal_arr Hterm T').
  split.
  - apply transitivity with (terminal_arr Hterm T).
    + apply symmetry, terminality.
    + apply terminality.
  - apply transitivity with (terminal_arr Hterm'  T').
    + apply symmetry, terminality.
    + apply terminality.
Qed.

Theorem Terminal_uniqueness:
  forall (C: Category)(T T': Terminal C),
    Iso T T'.
Proof.
  move=> C T T'.
  by apply Terminal_unique_up_to_iso; [apply T | apply T'].
Qed.

Program Canonical Structure Initial_to_Terminal
        {C: Category}(I: Initial C): Terminal (C ^^op) :=
  {| terminal_arr X := initial_arr I (X: C^^op) |}.
Next Obligation.
  by apply initiality.
Qed.

Program Canonical Structure Terminal_to_Initial
        {C: Category}(T: Terminal C): Initial (C ^^op) :=
    {| initial_arr X := terminal_arr T (X: C^^op) |}.
Next Obligation.
  by apply terminality.
Qed.

Program Canonical Structure Product_to_CoProduct {C: Category}{X Y: C}(prod: Product X Y)
: CoProduct (C:=C^^op) X Y :=
    {| in_X := proj_X (C:=C) prod: Hom (C^^op) X prod;
       in_Y := proj_Y (C:=C) prod;
       coproduct_arr := product_arr prod |}.
Next Obligation.
  by apply product_arr_property_X.
Qed.
Next Obligation.
  by apply product_arr_property_Y.
Qed.
Next Obligation.
  by apply product_universality.
Qed.

Program Canonical Structure CoProduct_to_Product
        {C: Category}{X Y: C}(coprod: CoProduct X Y)
: Product (C:=C^^op) X Y :=
  {| proj_X := in_X (C:=C) coprod: Hom (C^^op) coprod X;
     proj_Y := in_Y (C:=C) coprod;
     product_arr := coproduct_arr (C:=C) coprod |}.
Next Obligation.
  by apply coproduct_arr_property_X.
Qed.
Next Obligation.
  by apply coproduct_arr_property_Y.
Qed.
Next Obligation.
  by apply coproduct_universality.
Qed.

Lemma prod_arr_compose
      (C: Category)(H: hasProduct C)(X Y Z W V U: C)(f: X --> Z)(g: Z --> V)(f': Y --> W)(g': W --> U):
  prod_arr g g'•prod_arr f f' === prod_arr (g•f) (g'•f').
Proof.
  apply symmetry.
  rewrite /prod_arr.
  apply product_universality.
  { 
    eapply transitivity;
    [ eapply transitivity; [ apply symmetry, compose_assoc |];
      apply compose_subst_snd, product_arr_property_X |].
    eapply transitivity;
    [ eapply transitivity; [ apply compose_assoc |];
      apply compose_subst_fst, product_arr_property_X |].
    apply symmetry, compose_assoc. }
  { eapply transitivity;
    [ eapply transitivity; [apply symmetry, compose_assoc |];
      apply compose_subst_snd, product_arr_property_Y |].
    eapply transitivity;
      [ eapply transitivity; [apply compose_assoc |];
        apply compose_subst_fst, product_arr_property_Y |].
    apply symmetry, compose_assoc. }
Qed.

Lemma coprod_arr_compose
      (C: Category)(H: hasCoProduct C)(X Y Z W V U: C)(f: X --> Z)(g: Z --> V)(f': Y --> W)(g': W --> U):
  coprod_arr g g'•coprod_arr f f' === coprod_arr (g•f) (g'•f').
Proof.
  apply symmetry.
  rewrite /coprod_arr.
  apply coproduct_universality.
  { 
    eapply transitivity;
    [ eapply transitivity; [ apply compose_assoc |];
      apply compose_subst_fst, coproduct_arr_property_X |].
    eapply transitivity;
    [ eapply transitivity; [ apply symmetry, compose_assoc |];
      apply compose_subst_snd, coproduct_arr_property_X |].
    apply compose_assoc. }
  { 
    eapply transitivity;
    [ eapply transitivity; [ apply compose_assoc |];
      apply compose_subst_fst, coproduct_arr_property_Y |].
    eapply transitivity;
    [ eapply transitivity; [ apply symmetry, compose_assoc |];
      apply compose_subst_snd, coproduct_arr_property_Y |].
    apply compose_assoc. }
Qed.

  Lemma initial_refl:
    forall (C: Category)(I: Initial C),
      initial_arr I I === id.
  Proof.
    move=> C I.
    apply initiality.
  Qed.

  Lemma initial_fusion:
    forall (C: Category)(I: Initial C)(X Y: C)(f: X --> Y),
      f•initial_arr I X === initial_arr I Y.
  Proof.
    move=> C I X Y f.
    apply symmetry, initiality.
  Qed.


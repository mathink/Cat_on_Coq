
Require Import Setoid Category Functor.

Set Implicit Arguments.

Class Natrans {C D: Category}(F G: Functor C D) :=
  { natrans (X: C): F X ⟶ G X ;
    naturality:
      forall (X Y: C)(f: X ⟶ Y),
        (natrans Y) ◦ fmap f == fmap f ◦ (natrans X) }.
Coercion natrans: Natrans >-> Funclass.


Program Instance vCompose_Natrans
        {C D: Category}{F G H: Functor C D}
        (S: Natrans F G)(T: Natrans G H)
: Natrans F H :=
  { natrans X := natrans X ◦ natrans X }.
Next Obligation.
  intros.
  equiv_trns_with (T Y ◦ (S Y◦fmap f));
    [ apply compose_assoc | ].
  equiv_trns_with (T Y ◦ (fmap f ◦ S X)).
  - apply compose_subst_fst; apply naturality.
  - equiv_trns_with ((T Y ◦ fmap f) ◦ S X);
    [ equiv_symm; auto; apply compose_assoc | ].
    equiv_trns_with ((fmap f ◦ T X) ◦ S X);
      [ | apply compose_assoc ].
    apply compose_subst_snd; apply naturality.
Qed.

Program Instance hCompose_Natrans
        {C D E: Category}{F G: Functor C D}{F' G': Functor D E}
        (S: Natrans F G)(T: Natrans F' G')
: Natrans (ComposeFunctor F F') (ComposeFunctor G G') :=
  { natrans X := fmap (natrans X) ◦ natrans (fobj X) }.
Next Obligation.
  simpl; intros.
  eapply transitivity; [ apply compose_subst_snd | ].
  equiv_symm; auto.
  apply naturality.
  eapply transitivity; [ apply compose_assoc | ].
  equiv_trns_with (fmap f ◦ (T (G X) ◦ fmap (S X)));
    [ | apply compose_subst_fst; apply naturality ].
  simpl.
  eapply transitivity; [ | apply compose_assoc ].
  equiv_symm; auto.
  eapply transitivity; [ apply compose_subst_snd | ].
  equiv_symm; auto.
  apply naturality.
  eapply transitivity; [ apply compose_assoc | ].
  apply compose_subst_fst.
  eapply transitivity; [ apply fmap_compose | ].
  equiv_symm; auto.
  eapply transitivity; [ apply fmap_compose | ].
  apply ap_preserve_eq.
  apply naturality.
Qed.

Program Instance compose_Natrans_Functor
        {C D E: Category}{F G: Functor C D}
        (S: Natrans F G)(H: Functor D E)
: Natrans (ComposeFunctor F H) (ComposeFunctor G H) :=
  { natrans X := fmap (natrans X) }.
Next Obligation.
  simpl; intros.
  eapply transitivity; [ apply fmap_compose | ].
  eapply transitivity; [ | equiv_symm; auto;
                             apply fmap_compose ].
  apply ap_preserve_eq.
  apply naturality.
Qed.

Program Instance compose_Functor_Natrans
        {B C D: Category}{F G: Functor C D}
        (E: Functor B C)(S: Natrans F G)
: Natrans (ComposeFunctor E F) (ComposeFunctor E G) :=
  { natrans X := (natrans (E X)) }.
Next Obligation.
  simpl; intros.
  apply naturality.
Qed.

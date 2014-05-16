Require Import 
Ssreflect.ssreflect
Setoid Category Functor.

Set Implicit Arguments.

Structure Natrans {C D: Category}(F G: Functor C D) :=
  { natrans (X: C):> F X --> G X ;
    naturality:
      forall (X Y: C)(f: X --> Y),
        (natrans Y) • fmap F f === fmap G f • (natrans X) }.


Program Definition vCompose_Natrans
        {C D: Category}{F G H: Functor C D}
        (S: Natrans F G)(T: Natrans G H)
: Natrans F H :=
  {| natrans X :=  T X • S X |}.
Next Obligation.
  apply transitivity with (T Y•(S Y•fmap F f));
  [ apply compose_assoc |].
  apply transitivity with (T Y•fmap G f•S X);
    [ apply compose_subst_fst, naturality |].
  apply transitivity with ((T Y•fmap G f)•S X);
    [ apply symmetry, compose_assoc |].
  apply transitivity with ((fmap H f•T X)•S X);
    [| apply compose_assoc ].
  apply compose_subst_snd, naturality.
Qed.

Program Definition hCompose_Natrans
        {C D E: Category}{F G: Functor C D}{F' G': Functor D E}
        (S: Natrans F G)(T: Natrans F' G')
: Natrans (ComposeFunctor F F') (ComposeFunctor G G') :=
  {| natrans X := fmap G' (S X) • T (F X) |}.
Next Obligation.
  apply symmetry.
  eapply transitivity; [ apply symmetry, compose_assoc | ].
  eapply transitivity; [ apply compose_subst_snd | ].
  apply fmap_compose.
  eapply transitivity; [ apply compose_subst_snd | ].
  apply map_preserve_eq; apply symmetry, naturality.
  eapply transitivity; [ apply compose_subst_snd; apply symmetry, fmap_compose | ].
  eapply transitivity; [ apply compose_assoc | ].
  eapply transitivity; [| apply symmetry, compose_assoc ].
  apply compose_subst_fst.
  apply symmetry, naturality.
Qed.  

Program Definition compose_Natrans_Functor
        {C D E: Category}{F G: Functor C D}
        (S: Natrans F G)(H: Functor D E)
: Natrans (ComposeFunctor F H) (ComposeFunctor G H) :=
  {| natrans X := fmap H (S X) |}.
Next Obligation.
  eapply transitivity; [ apply fmap_compose |].
  eapply transitivity; [| apply symmetry, fmap_compose].
  apply map_preserve_eq; apply naturality.
Qed.

Program Definition compose_Functor_Natrans
        {B C D: Category}{F G: Functor C D}
        (E: Functor B C)(S: Natrans F G)
: Natrans (ComposeFunctor E F) (ComposeFunctor E G) :=
  {| natrans X := (S (E X)) |}.
Next Obligation.
  apply naturality.
Qed.

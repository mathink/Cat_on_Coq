
Require Import Utf8 Setoid Category.

Set Implicit Arguments.

Class Functor (C D: Category): Type :=
  { fobj: C -> D;
    fmap {X Y: C}:> Map (X ⟶ Y)  (fobj X ⟶ fobj Y);
    
    fmap_id:
      forall (X: C), fmap id == id_(fobj X) ;

    fmap_compose:
      forall (X Y Z: C)(f: X ⟶ Y)(g: Y ⟶ Z),
        fmap g◦fmap f == fmap (g◦f) }.
Coercion fobj: Functor >-> Funclass.

Class contravariantFunctor (C D: Category): Type :=
  { op_fobj: C -> D;
    op_fmap {X Y: C}: Map (X ⟶ Y)  (op_fobj Y ⟶ op_fobj X);
    
    op_fmap_id:
      forall (X: C), op_fmap id == id_(op_fobj X);

    op_fmap_compose:
      forall (X Y Z: C)(f: X ⟶ Y)(g: Y ⟶ Z),
        op_fmap f◦op_fmap g == op_fmap (g◦f) }.
Coercion op_fobj: contravariantFunctor >-> Funclass.

Program Instance contFunctor_Functor {C D: Category}(opF: contravariantFunctor C D)
: Functor (op_Category C) D :=
  { fobj X := op_fobj (contravariantFunctor:=opF) X;
    fmap X Y := op_fmap (contravariantFunctor:=opF) }.
Next Obligation.
  intros.
  apply (op_fmap_id (C:=C)).
Qed.
Next Obligation.
  intros.
  apply (op_fmap_compose (C:=C)).
Qed.

Program Instance IdFunctor (C: Category): Functor C C :=
  { fobj X := X;
    fmap X Y := IdMap (X ⟶ Y) }.
Next Obligation.
  simpl; intros; equiv_refl; auto.
Qed.
Next Obligation.
  simpl; intros; equiv_refl; auto.
Qed.

Program Instance ComposeFunctor {C D E: Category}
        (F: Functor C D)(G: Functor D E): Functor C E :=
  { fobj X := G (F X);
    fmap X Y := ComposeMap fmap fmap }.
Next Obligation.
  intros.
  simpl.
  equiv_trns_with (fmap (id_ (F X))); auto.
  - apply ap_preserve_eq; apply fmap_id.
  - apply fmap_id.
Qed.
Next Obligation.
  intros.
  simpl.
  eapply transitivity; [ apply fmap_compose | ].
  apply ap_preserve_eq; apply fmap_compose.
Qed.

Program Instance op_Functor C D (F: Functor C D)
: Functor C ^^op D ^^op :=
  { fobj X := F X ; fmap X Y := fmap (Functor:=F) }.
Next Obligation.
  simpl; intros.
  apply fmap_id.
Qed.
Next Obligation.
  simpl;intros.
  apply fmap_compose.
Qed.



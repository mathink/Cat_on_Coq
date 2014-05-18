Require Import 
Ssreflect.ssreflect
COC.Setoid COC.Category.

Set Implicit Arguments.
Unset Strict Implicit.

Structure Functor (C D: Category): Type :=
  make_Functor
  { fobj:> C -> D;
    fmap {X Y: C}: Map (X --> Y)  (fobj X --> fobj Y);
    
    fmap_id:
      forall (X: C), fmap id === id_(fobj X) ;

    fmap_compose:
      forall (X Y Z: C)(f: X --> Y)(g: Y --> Z),
        fmap g•fmap f === fmap (g•f) }.

Structure contravariantFunctor (C D: Category): Type :=
  { op_fobj:> C -> D;
    op_fmap {X Y: C}:> Map (X --> Y)  (op_fobj Y --> op_fobj X);
    
    op_fmap_id:
      forall (X: C), op_fmap id === id_(op_fobj X);

    op_fmap_compose:
      forall (X Y Z: C)(f: X --> Y)(g: Y --> Z),
        op_fmap f•op_fmap g === op_fmap (g•f) }.

Program Definition contFunctor_Functor {C D: Category}(opF: contravariantFunctor C D)
: Functor (op_Category C) D :=
  {| fobj X := op_fobj opF X;
     fmap X Y := op_fmap opF |}.
Next Obligation.
  by apply (op_fmap_id (C:=C)).
Qed.
Next Obligation.
  by apply (op_fmap_compose (C:=C)).
Qed.

Program Definition IdFunctor (C: Category): Functor C C :=
  {| fobj X := X;
     fmap X Y := id_Map (X --> Y) |}.
Next Obligation.
  by equiv_refl.
Qed.
Next Obligation.
  by equiv_refl.
Qed.

Program Definition ComposeFunctor {C D E: Category}
        (F: Functor C D)(G: Functor D E): Functor C E :=
  {| fmap X Y := compose_Map (fmap F) (fmap G) |}.
Next Obligation.
  apply transitivity with (fmap G (id_ (F X))); auto.
  - apply map_preserve_eq, fmap_id.
  - apply fmap_id.
Qed.
Next Obligation.
  eapply transitivity; [ apply fmap_compose | ].
  by apply map_preserve_eq, fmap_compose.
Qed.

Program Definition op_Functor C D (F: Functor C D)
: Functor C ^^op D ^^op :=
  {| fmap X Y := fmap F |}.
Next Obligation.
  rewrite /id_; apply fmap_id.
Qed.
Next Obligation.
  by apply fmap_compose.
Qed.



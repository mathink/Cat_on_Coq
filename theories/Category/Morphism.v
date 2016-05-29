Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid.
Require Import COC.Category.Category.

Variant Iso (C: Category)(X Y: C): C X Y -> C Y X -> Prop :=
| Iso_def: forall f g, g \o f == Id X -> f \o g == Id Y -> Iso f g.

Definition invertible (C: Category)(X Y: C)(f: C X Y) :=
  exists f': C Y X, (f' \o f == Id X) /\ (f \o f' == Id Y).

Definition isomorphic (C: Category)(X Y: C) :=
  exists f: C X Y, invertible f.

Definition monic (C: Category)(X Y: C)(f: C X Y) :=
  forall (W: C)(f1 f2: C W X), f \o f1 == f \o f2 -> f1 == f2.

Notation left_cancellable f := (monic f) (only parsing).

Definition epi (C: Category)(X Y: C)(f: C X Y) :=
  forall (Z: C)(f1 f2: C Y Z), f1 \o f == f2 \o f -> f1 == f2.

Notation right_cancellable f := (epi f) (only parsing).

Class isRInverse (C: Category)(X Y: C)(f: C X Y)(g: C Y X) :=
  right_inverse:> f \o g == Id Y.

Structure RInverse (C: Category)(X Y: C)(f: C X Y) :=
  {
    rinv:> C Y X;
    rinv_prf:> isRInverse f rinv
  }.
Existing Instance rinv_prf.

Notation section f := (RInverse f).

Class isLInverse (C: Category)(X Y: C)(f: C X Y)(g: C Y X) :=
  left_inverse:> g \o f == Id X.

Structure LInverse (C: Category)(X Y: C)(f: C X Y) :=
  {
    linv:> C Y X;
    linv_prf:> isLInverse f linv
  }.
Existing Instance linv_prf.

Notation retraction f := (LInverse f).

Definition idempotent (C: Category)(X: C)(f: C X X) := f \o f == f.

Definition split (C: Category)(X: C)(f: C X X) :=
  idempotent f ->
  exists V g h, f == h \o g /\ g \o h == Id V.

Lemma section_epi:
  forall (C: Category)(X Y: C)(f: C X Y),
    (exists g, isRInverse f g) -> epi f.
Proof.
  intros C X Y f [g H] Z f1 f2 Heq.
  rewrite <- catC1f.
  now rewrite <- H, <- catCa, Heq, catCa, H, catC1f.
Qed.

Lemma ratraction_monic:
  forall (C: Category)(X Y: C)(f: C X Y),
    (exists g, isLInverse f g) -> monic f.
Proof.
  intros C X Y f [g H] Z f1 f2 Heq.
  now rewrite <- catCf1, <- H, catCa, Heq, <- catCa, H, catCf1.
Qed.


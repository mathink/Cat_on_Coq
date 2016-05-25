Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid COC.Category.

From COC.AlgebraicStructures
     Require Import Binop Monoid Group Ring Field.

(** * 圏を作る **)

(** ** モノイドの圏 Mon **)
Program Canonical Structure Mon: Category :=
  Category.build (@MonoidHom.setoid)
                 (@MonoidHom.compose)
                 (@MonoidHom.id).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl in *.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.

(** ** 群の圏 Grp **)
Program Canonical Structure Grp: Category :=
  Category.build (@GroupHom.setoid)
                 (@GroupHom.compose)
                 (@GroupHom.id).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl in *.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.

(** ** 環の圏 Rng **)
Program Canonical Structure Rng: Category :=
  Category.build (@RingHom.setoid)
                 (@RingHom.compose)
                 (@RingHom.id).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl in *.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.

(** ** 体の圏 Fld **)
Program Canonical Structure Fld: Category :=
  Category.build (@FieldHom.setoid)
                 (@FieldHom.compose)
                 (@FieldHom.id).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl in *.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.

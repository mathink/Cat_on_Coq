Require Import COC.Init.Prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

(**
 ** 関係と性質
同値関係の定義に向けて、性質を表すクラスを定義していく
 **)
Class Reflexive `(R: relation X): Prop :=
  reflexivity:
    forall x: X, R x x.

Class Symmetric `(R: relation X): Prop :=
  symmetry:
    forall x y: X, R x y -> R y x.

 Class Transitive `(R: relation X): Prop :=
  transitivity:
    forall x y z: X, R x y -> R y z -> R x z.

Class Equivalence `(R: relation X): Prop :=
  {
    equiv_Reflexive:> Reflexive R;
    equiv_Symmetric:> Symmetric R;
    equiv_Transitive:> Transitive R
  }.
Existing Instance equiv_Reflexive.
Existing Instance equiv_Symmetric.
Existing Instance equiv_Transitive.

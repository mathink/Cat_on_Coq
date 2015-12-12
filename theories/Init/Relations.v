Require Import COC.Init.Prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

(**
 * 関係と性質
[Setoid] に必要な同値関係を定義するため、型クラスとしてこれらを定義する。
同値関係を一度に定義するのではなく、反射律などを経由して行なう。
これは、後に別の関係を記述するときに再利用が可能なようにするためである。

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

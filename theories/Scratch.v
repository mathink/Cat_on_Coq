(* Cat_on_Coq: redefine *)
Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Reversible Pattern Implicit.

Generalizable All Variables.

Set Universe Polymorphism.
Set Printing Universes.

(**
 * 基本となる道具
Setoid や Setoid 間の写像など、圏を定義する上で必要となる道具を定義する。
 **)
(** 
Coq が通常提供する記法も、後々一般化する。
そのため、開発においては [-nois] オプションを施している。

とはいえ何も使えないと不便なので、スコープを定め、 Local に利用する。
 **)
Delimit Scope base_scope with base.
Open Scope base_scope.

Local Notation "X -> Y" :=
  (forall (_: X), Y) (at level 99, right associativity): base_scope.

(**
 ** 関係と性質
 **)

Definition relation (X: Type) := X -> X -> Prop.

(** 
同値関係の定義に向けて、性質を表わすクラスを定義していく
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

(* eq and example of Equivalence *)
Module Eq.
  Variant eq (X: Type): relation X :=
  | eq_refl: forall x: X, eq x x.

  Lemma eq_ind:
    forall (X: Type)(P: relation X),
      (forall x: X, P x x) ->
      (forall x y: X, eq x y -> P x y).
  Proof.
    intros X P IH x y Heq.
    destruct Heq.
    exact (IH x).
  Qed.

  Instance eq_Reflexive (X: Type): Reflexive (@eq X).
  Proof.
    intro x.
    exact eq_refl.
  Qed.

  Instance eq_Symmetric (X: Type): Symmetric (@eq X).
  Proof.
    intros x y Heq.
    destruct Heq.
    exact eq_refl.
  Qed.

  Instance eq_Transitive (X: Type): Transitive (@eq X).
  Proof.
    intros x y z Heqxy Heqyz.
    destruct Heqxy.
    exact Heqyz.
  Qed.

  Instance eq_Equivalence (X: Type): Equivalence (@eq X) := {}.
End Eq.

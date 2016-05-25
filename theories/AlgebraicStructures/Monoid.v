Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.
From COC.AlgebraicStructures Require Import Binop.

(** * モノイド(Monoid)
比較的シンプル。
結合的で単位元を持つ二項演算を伴うあれ。
 **)
Module Monoid.
  Class spec (M: Setoid)(op: Binop M)(e: M) :=
    proof {
        associative:> Associative op;
        identical:> Identical op e
      }.

  Structure type :=
    make {
        carrier: Setoid;
        op: Binop carrier;
        e: carrier;

        prf: spec op e
      }.

  Module Ex.
    Existing Instance associative.
    Existing Instance identical.
    Existing Instance prf.

    Notation isMonoid := spec.
    Notation Monoid := type.

    Coercion associative: isMonoid >-> Associative.
    Coercion identical: isMonoid >-> Identical.
    Coercion carrier: Monoid >-> Setoid.
    Coercion prf: Monoid >-> isMonoid.

    Delimit Scope monoid_scope with monoid.
    Notation "x * y" := (op _ x y) (at level 40, left associativity): monoid_scope.
    Notation "'1'" := (e _): monoid_scope.
  End Ex.

  Import Ex.
  
  Section MonoidProps.
    Variable (M: Monoid).
    Open Scope monoid_scope.

    Lemma left_op:
      forall x y z: M,
        y == z -> x * y == x * z.
    Proof.
      intros.
      now rewrite H.
    Qed.

    Lemma right_op:
      forall x y z: M,
        x == y -> x * z == y * z.
    Proof.
      intros.
      now rewrite H.
    Qed.

    Lemma commute_l:
      forall `{Commute M (Monoid.op M)}(x y z: M), x * (y * z) == y * (x * z).
    Proof.
      intros; repeat rewrite associative.
      now rewrite (commute x y).
    Qed.
  End MonoidProps.

End Monoid.
Export Monoid.Ex.


(** * モノイド準同型
単位元の保存
 **)
Module MonoidHom.
  Open Scope monoid_scope.
  
  Class spec (M N: Monoid)(f: Map M N) :=
    proof {
        op: forall x y, f (x * y) == f x * f y;
        ident: f 1 == 1
      }.
  
  Class type (M N: Monoid) :=
    make {
        map: Map M N;
        prf: spec M N map
      }.

  Module Ex.
    Notation isMonoidHom := spec.
    Notation MonoidHom := type.

    Coercion map: MonoidHom >-> Map.
    Coercion prf: MonoidHom >-> isMonoidHom.

    Existing Instance prf.
  End Ex.

  Import Ex.

  Program Canonical Structure compose
          (M N L: Monoid)(f: MonoidHom M N)(g: MonoidHom N L) :=
    {|
      map := Map.compose f g;
      prf := proof _ _
    |}.
  Next Obligation.
    now rewrite !op.
  Qed.
  Next Obligation.
    now rewrite !ident.
  Qed.

  Program Canonical Structure id (M: Monoid): MonoidHom M M :=
    {|
      map := Map.id;
      prf := proof _ _
    |}.
  Next Obligation.
    reflexivity.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.

  Definition equal {M N: Monoid}: relation (MonoidHom M N) :=
    fun f g => forall x: M, f x == g x.
  Arguments equal {M N} f g /.

  Program Canonical Structure setoid (M N: Monoid): Setoid :=
    Setoid.build (@equal M N).
  Next Obligation.
    intros f x;  reflexivity.
  Qed.
  Next Obligation.
    intros f g Heq x.
    generalize (Heq x).
    now symmetry.
  Qed.
  Next Obligation.
    intros f g h Hfg Hgh x.
    rewrite (Hfg x); apply Hgh.
  Qed.
End MonoidHom.
Export MonoidHom.Ex.

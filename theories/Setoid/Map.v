Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Init.
Require Import COC.Setoid.Core.

(** * Map
[Setoid] の間のモルフィズム。

[X Y: Setoid] について、その carrier type 間の函数のうち、同値関係を保存するもの。
 **)
Module Map.
  Class spec {X Y: Setoid}(f: X -> Y): Prop :=
    substitute:
      forall (x y: X), x == y -> f x == f y.

  Structure type (X Y: Setoid) :=
    make {
        f: X -> Y;
        prf: spec f
      }.

  Notation build f := (@make _ _ f _).

  Module Ex.
    Notation isMap := spec.
    Notation Map := type.
    Coercion f: Map >-> Funclass.
    Coercion prf: Map >-> isMap.
    Existing Instance prf.

    Notation "[ x .. y :-> p ]" := 
      (build (fun x => .. (build (fun y => p)) ..))
        (at level 200, x binder, right associativity,
         format "'[' [ x .. y  :->  '/ ' p ] ']'"): cat_scope.
  End Ex.
  Import Ex.

  Definition dom {X Y}(m: Map X Y): Setoid := X.
  Definition cod {X Y}(m: Map X Y): Setoid := Y.

  Program Definition compose
          {X Y Z: Setoid}(f: Map X Y)(g: Map Y Z): Map X Z :=
    [ x :-> g (f x)].
  Next Obligation.
    intros X Y Z f g x x' Heq.
    do 2 apply substitute.
    exact Heq.
  Qed.
  Global Arguments compose {X Y Z} f g /.

  Program Definition id (X: Setoid): Map X X := [ x :-> x ].
  Next Obligation.
    intros X x y Heq; exact Heq.
  Qed.
  Global Arguments id X /.

  Definition equal {X Y: Setoid}: relation (Map X Y) :=
    fun f g => forall x: X, f x == g x.
  Arguments equal {X Y} f g /.

  Program Definition setoid (X Y: Setoid): Setoid :=
    Setoid.build (@equal X Y).
  Next Obligation.
    intros X Y f x; exact reflexivity.
  Qed.
  Next Obligation.
    intros X Y f g Heq x.
    generalize (Heq x).
    apply symmetry.
  Qed.
  Next Obligation.
    intros X Y f g h Heqfg Heqgh x.
    apply transitivity with (g x).
    - exact (Heqfg x).
    - exact (Heqgh x).
  Qed.
End Map.
Export Map.Ex.

Definition injective (X Y: Setoid)(f: Map X Y) :=
  forall (x x': X), f x == f x' -> x == x'.

Definition surjective (X Y: Setoid)(f: Map X Y) :=
  forall (y: Y), exists_ x: X, f x == y.

Definition bijective (X Y: Setoid)(f: Map X Y) :=
  injective f /\ surjective f.
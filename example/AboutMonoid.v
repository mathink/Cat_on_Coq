Set Implicit Arguments.
Unset Strict Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid COC.Category COC.AlgebraicStructures.

Section MapMonoid.
  Context (X: Setoid).

  Program Definition map_compose_binop: Binop (Map.setoid X X) :=
    Binop.build (Map.compose (X:=X)(Y:=X)).
  Next Obligation.
    intros f f' Heqf g g' Heqg x; simpl in *.
    now rewrite Heqf, Heqg.
  Qed.

  Program Instance map_compose_monoid
    : isMonoid map_compose_binop (Map.id (X:=X)).
  Next Obligation.
    now intros f g h x; simpl.
  Qed.
  Next Obligation.
    now split; intros f x; simpl.
  Qed.
End MapMonoid.

Section HomMonoid.
  Context (C: Category)(X: C).

  Program Definition hom_compose_binop: Binop (C X X) :=
    Binop.build (Category.comp (t:=C)).
  Next Obligation.
    intros f f' Heqf g g' Heqg; simpl in *.
    now rewrite Heqf, Heqg.
  Qed.

  Program Instance hom_compose_monoid
    : isMonoid hom_compose_binop (Id X).
  Next Obligation.
    intros f g h; simpl.
    now rewrite catCa.
  Qed.
  Next Obligation.
    split; intros f; simpl.
    - now rewrite catC1f.
    - now rewrite catCf1.
  Qed.
End HomMonoid.


Require Import List.
Import List.ListNotations.

Section MonoidFold.
  Context (M: Monoid).

  Open Scope monoid_scope.
  
  Fixpoint mfold (l: list M): M :=
    match l with
    | [] => 1
    | x::xs => x * mfold xs
    end.
End MonoidFold.
  
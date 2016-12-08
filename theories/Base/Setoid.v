(** * Setoid, Map **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Export Coq.Program.Basics Coq.Program.Tactics Coq.Setoids.Setoid Coq.Classes.Morphisms.

Obligation Tactic := (try split); program_simpl; try now auto.

Structure Setoid: Type :=
  {
    setoid_carrier:> Type;
    setoid_equal: setoid_carrier -> setoid_carrier -> Prop;

    setoid_prf:> Equivalence setoid_equal
  }.
Existing Instance setoid_prf.

Notation "[ 'Setoid' 'by' P 'on' A ]" := (@Build_Setoid A P _).
Notation "[ 'Setoid' 'by' P ]" := [Setoid by P on _].

Notation "(== 'in' A )" := (setoid_equal A).
Notation "x == y 'in' A" := (setoid_equal A x y) (at level 70, y at next level, no associativity).
Notation "(==)" := (== in _).
Notation "x == y" := (x == y in _) (at level 70, no associativity).

(** Examples **)
Program Definition eq_setoid (X: Type) :=
  [Setoid by @eq X].

Program Definition function (X Y: Type): Setoid :=
  [Setoid by `(forall x, f x = g x) on X -> Y].
Next Obligation.
  intros f g h Heqfg Heqgh x.
  now rewrite Heqfg.
Qed.
Canonical Structure function.

Inductive empty := .

Program Definition empty_setoid: Setoid :=
  [Setoid by (fun e e' => match e, e' with end) on empty].

Inductive unit := tt.

Program Definition unit_setoid: Setoid :=
  [Setoid by (fun x y => True) on unit].

(** Map **)
Class IsMap {X Y: Setoid}(f: X -> Y) :=
  {
    map_proper:> Proper ((==) ==> (==)) f
  }.

Structure Map (X Y: Setoid): Type :=
  {
    map_fun:> X -> Y;

    map_prf:> IsMap map_fun
  }.
Existing Instance map_prf.

Notation "[ 'Map' 'by' f ]" := (@Build_Map _ _ f _).
Notation "[ x 'in' X :-> m ]" := [Map by fun (x: X) => m].
Notation "[ x :-> m ]" := ([ x in _ :-> m]).

Program Definition Map_compose (X Y Z: Setoid)(f: Map X Y)(g: Map Y Z): Map X Z :=
  [ x :-> g (f x)].
Next Obligation.
  intros x y Heq; simpl.
  now rewrite Heq.
Qed.

Program Definition Map_id (X: Setoid): Map X X :=
  [ x :-> x ].

Program Definition Map_setoid (X Y: Setoid): Setoid :=
  [Setoid by `(forall x, f x == g x) on Map X Y].
Next Obligation.
  intros f g h Heqfg Heqgh x.
  now rewrite Heqfg.
Qed.
Canonical Structure Map_setoid.
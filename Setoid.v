Require Import
Coq.Relations.Relation_Definitions
Coq.Classes.RelationClasses.
Require Export Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.

Create HintDb setoid.
Hint Unfold Reflexive Symmetric Transitive: setoid.
Notation make_Equivalence eq := (@Build_Equivalence _ eq _ _ _).
Existing Instance Equivalence_Reflexive.
Existing Instance Equivalence_Symmetric.
Existing Instance Equivalence_Transitive.

Ltac equiv_refl := apply reflexivity.
Ltac equiv_symm := apply symmetry; auto.
Ltac equiv_trns := apply transitivity.
Ltac equiv_trns_with H := apply transitivity with H; auto.

Ltac equiv_tac := 
  match goal with
    | |- Equivalence _ => apply Build_Equivalence
  end.

Ltac start :=
  try equiv_tac;
  autounfold with setoid.


(* Definition of Setoid *)
Class Setoid_Spec (t: Type) :=
  { equal:> relation t;
    setoid_eq_equiv :> Equivalence equal }.
Existing Instance setoid_eq_equiv.

Structure Setoid: Type :=
  make_Setoid
  { carrier:> Type;
    setoid_spec :> Setoid_Spec carrier }.
Coercion make_Setoid: Setoid_Spec >-> Setoid.
Notation setoid_equal x y := (@equal _ _ x y) .
Existing Instance setoid_spec.

Notation "x == y" := (setoid_equal x y) (at level 80, no associativity).

(* Definition of Map *)

Structure Map (X Y: Setoid): Type :=
  make_Map
  { map_function:> X -> Y;
    map_preserve_eq:
      forall (x x': X)(Heq: x == x'),
        map_function x == map_function x' }.

Definition Map_eq {X Y: Setoid}(f g: Map X Y) :=
  forall x: X, f x == g x.

Program Canonical Structure MapSetoid (X Y: Setoid): Setoid :=
  {| equal := @Map_eq X Y |}.
Next Obligation.
  split.
  - intros f x; apply reflexivity.
  - intros f g Heq x; apply symmetry; apply Heq.
  - intros f g h Heq Heq' x; apply transitivity with (g x);
    [apply Heq | apply Heq'].
Qed.

Program Canonical Structure  ComposeMap {X Y Z: Setoid}
        (f: Map X Y)(g: Map Y Z): Map X Z :=
  {| map_function := (fun x: X => g (f x)) |}.
Next Obligation. 
  repeat apply map_preserve_eq; assumption.
Qed.

Program Canonical Structure IdMap (X: Setoid): Map X X :=
  {| map_function := fun x => x |}.


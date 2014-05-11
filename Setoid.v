(*
   Categorical Structure on Coq.

   - Setoid.v
  *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.

Create HintDb setoid.
Hint Unfold Reflexive Symmetric Transitive: setoid.
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
Structure Setoid: Type :=
  make_Setoid
  { carrier:> Type;
    equal: relation carrier;
    prf_equiv : Equivalence equal }.
Arguments equal {setoid}(x y): rename.
Notation "x == y" := (equal x y) (at level 80, no associativity).
Existing Instance prf_equiv.

Definition reflexivity_setoid (s: Setoid) :=
  @reflexivity s _ (@Equivalence_Reflexive s (@equal s) (prf_equiv s)).

(* Definition of Map *)
Structure Map (X Y: Setoid): Type :=
  make_Map
  { ap:> X -> Y;
    ap_preserve_eq:
    forall (x x': X)(Heq: x == x'), ap x == ap x' }.

Definition Map_eq {X Y: Setoid}(f g: Map X Y) :=
  forall x: X, f x == g x.

Program Instance Map_eq_equiv (X Y: Setoid):
  Equivalence (@Map_eq X Y).
Next Obligation.
  intros f x; apply reflexivity.
Qed.
Next Obligation.
  intros f g Heq x; apply symmetry; apply Heq.
Qed.
Next Obligation.
  intros f g h Heq Heq' x; apply transitivity with (g x);
  [apply Heq | apply Heq'].
Qed.

Canonical Structure MapSetoid (X Y: Setoid): Setoid :=
  make_Setoid (Map_eq_equiv X Y).

Program Definition  ComposeMap {X Y Z: Setoid}
        (f: Map X Y)(g: Map Y Z): Map X Z :=
  {| ap := (fun x: X => g (f x)) |}.
Next Obligation.
  repeat apply ap_preserve_eq; assumption.
Qed.

Canonical Structure ComposeMap.

Program Definition IdMap (X: Setoid): Map X X :=
  {| ap := fun x => x |}.

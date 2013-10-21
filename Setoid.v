(*
   Categorical Structure on Coq.

   - Setoid.v
  *)

Require Import Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.

Create HintDb setoid.
Hint Unfold Reflexive Symmetric Transitive: setoid.
Hint Resolve Build_Equivalence: setoid.

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
Class Setoid: Type :=
  { carrier:> Type;
    equal: carrier -> carrier -> Prop;
    prf_equiv :> Equivalence equal }.
Coercion carrier: Setoid >-> Sortclass.
Notation "x == y" := (equal x y) (at level 80, no associativity).


(* Definition of Map *)
Class Map (X Y: Setoid): Type :=
  { ap: X -> Y;
    ap_preserve_eq:
    forall (x x': X)(Heq: x == x'), ap x == ap x' }.
Coercion ap: Map >-> Funclass.

Program Instance MapSetoid (X Y: Setoid): Setoid :=
  { carrier := Map X Y; equal := (fun f g => forall x: X, f x == g x) }.
Next Obligation.
  start.
  - intros f x; equiv_refl; auto.
  - intros f g Heq x; equiv_symm; apply Heq.
  - intros f g h Heq Heq' x; equiv_trns_with (g x); auto.
Qed.

Program Instance ComposeMap {X Y Z: Setoid}
        (f: Map X Y)(g: Map Y Z): Map X Z :=
  { ap := (fun x => g (f x)) }.
Next Obligation.
  repeat apply ap_preserve_eq; assumption.
Qed.

Program Instance IdMap (X: Setoid): Map X X :=
  { ap := fun x => x }.

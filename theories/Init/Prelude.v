(* Cat_on_Coq: redefine *)
Require Export Coq.Init.Notations.
Require Export Coq.Init.Logic.
(* Require Export Coq.Init.Datatypes. *)
Require Export Coq.Init.Tactics.
Require Export Coq.Init.Specif.
Require Coq.Program.Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
(* Set Reversible Pattern Implicit. *)
Set Primitive Projections.
Set Universe Polymorphism.

(*  *)
Unset Nonrecursive Elimination Schemes.

Obligation Tactic := idtac.

Generalizable All Variables.

Delimit Scope base_scope with base.
Open Scope base_scope.


Definition dom {X Y: Type}(f: X -> Y) := X.
Definition cod {X Y: Type}(f: X -> Y) := X.

Notation predicate X := (X -> Prop).
Notation relation X := (X -> predicate X).

Variant and (A B: Prop): Prop :=
| conj: A -> B -> and A B.
Infix "/\" := and.

Notation "P <-> Q" := ((P -> Q)/\(Q -> P)).

(*
 Specif にある sig は Universe Polymorphic ではない。
 Polymorphic な sig が必要になるので、ここで定義する。
 *)
Inductive ex (A: Type)(P: A -> Prop): Prop :=
| ex_intro: forall x: A, P x -> ex (A:=A) P.

Notation "'exists_' x .. y , p" :=
  (ex (fun x => .. (ex (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'exists_'  '/ ' x .. y , '/ ' p ']'"): type_scope.


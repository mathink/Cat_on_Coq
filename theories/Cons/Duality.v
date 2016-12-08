(** * Terminal Object **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.
From COC.Cons Require Import Initial Terminal.

Program Definition terminal_from_initial (C: Category)(i: Initial C): Terminal C^op :=
  [Terminal by (initial_univ i)].
Next Obligation.
  now apply initial_uniqueness.
Qed.

Program Definition initial_from_terminal (C: Category)(t: Terminal C): Initial C^op :=
  [Initial by (terminal_univ t)].
Next Obligation.
  now apply terminal_uniqueness.
Qed.

(** * Initial Object **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

Class IsInitial (C: Category)
      (obj: C)
      (univ: forall X: C, C obj X) :=
  {
    initial_uniqueness:
      forall (X: C)(f: C obj X),
        f == univ X
  }.

Structure Initial (C: Category) :=
  {
    initial_obj:> C;
    initial_univ: forall X: C, C initial_obj X;

    initial_prf:> IsInitial initial_univ
  }.
Existing Instance initial_prf.

Notation "[ 'Initial' i 'by' univ ]" := (@Build_Initial _ i univ _).
Notation "[ 'Initial' 'by' univ ]" := [Initial _ by univ].

Lemma initial_isomorphic:
  forall (C: Category)(i i': Initial C),
    i === i' in C.
Proof.
  intros C i i'; simpl; unfold isomorphic.
  exists (initial_univ i i'), (initial_univ i' i); split.
  - rewrite (initial_uniqueness (Id i)).
    now apply initial_uniqueness.
  - rewrite (initial_uniqueness (Id i')).
    now apply initial_uniqueness.
Qed.

(** Examples **)
Program Definition initial_of_Types: Initial Types :=
  [Initial empty by (fun (X: Type)(e: empty) => match e with end)].

Program Definition initial_of_Setoids: Initial Setoids :=
  [Initial empty_setoid
    by (fun (X: Setoid) => [e in empty :-> match e with end])].

Program Definition Zero: Category :=
  [Category by (fun (e e': empty) => match e, e' with end)
   with (fun X Y Z f g => match X with end),
        (fun X => match X with end)].

Program Definition FromZero (C: Category): Zero --> C :=
  [Functor by (fun X Y f => match X with end)
   with (fun (X: empty) => match X with end)].

Program Definition initial_of_Cat: Initial Cat :=
  [Initial Zero by @FromZero].

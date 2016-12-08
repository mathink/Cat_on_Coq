(** * Terminal Object **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

Class IsTerminal (C: Category)
      (obj: C)
      (univ: forall X: C, C X obj) :=
  {
    terminal_uniqueness:
      forall (X: C)(f: C X obj),
        f == univ X
  }.

Structure Terminal (C: Category) :=
  {
    terminal_obj:> C;
    terminal_univ: forall X: C, C X terminal_obj;

    terminal_prf:> IsTerminal terminal_univ
  }.
Existing Instance terminal_prf.

Notation "[ 'Terminal' t 'by' univ ]" := (@Build_Terminal _ t univ _).
Notation "[ 'Terminal' 'by' univ ]" := [Terminal _ by univ].

Lemma terminal_isomorphic:
  forall (C: Category)(t t': Terminal C),
    t === t' in C.
Proof.
  intros C t t'; simpl; unfold isomorphic.
  exists (terminal_univ t' t), (terminal_univ t t'); split.
  - rewrite (terminal_uniqueness (Id t)).
    now apply terminal_uniqueness.
  - rewrite (terminal_uniqueness (Id t')).
    now apply terminal_uniqueness.
Qed.

(** Examples **)
Program Definition terminal_of_Types: Terminal Types :=
  [Terminal unit by (fun (X: Type)(_: X) => tt)].
Next Obligation.
  now destruct (f x).
Qed.

Program Definition terminal_of_Setoids: Terminal Setoids :=
  [Terminal unit_setoid by (fun (X: Setoid) => [_ in X :-> tt])].

Program Definition One: Category :=
  [Category by (fun _ _ => unit_setoid)
   with (fun X Y Z f g => match X, Y, Z with tt, tt, tt => tt end),
        (fun X => match X with tt => tt end)].

Program Definition ToOne (C: Category): C --> One :=
  [* in C |-> tt in One].

Program Definition terminal_of_Cat: Terminal Cat :=
  [Terminal One by ToOne].
Next Obligation.
  rename X into C, f into F, X0 into X, f0 into f.
  destruct (fmap F f), (F X), (F Y).
  now apply hom_eq_refl.
Qed.

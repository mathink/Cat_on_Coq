(** * Ran **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

Class IsRan
      (C D E: Category)
      (F: C --> E)(K: C --> D)
      (ranF: D --> E)
      (ranN: (ranF \o K) ==> F)
      (ranU: forall {S: D --> E},
          (S \o K) ==> F -> S ==> ranF) :=
  {
    ran_universality:
      forall (S: D --> E)(e: (S \o K) ==> F),
        ranN \o{Fun _ _} (ranU e o> K) == e;
    ran_uniqueness:
      forall (S: D --> E)(e: (S \o K) ==> F)(u: S ==> ranF),
        ranN \o{Fun _ _} (u o> K) == e -> u == ranU e
  }.

Structure Ran (C D E: Category)(F: C --> E)(K: C --> D): Type :=
  {
    ranF: D --> E;
    ranN: (ranF \o K) ==> F;
    ranU: forall {S: D --> E},
        (S \o K) ==> F -> S ==> ranF;

    ran_prf:> IsRan ranN (@ranU)
  }.
Notation "[ 'Ran' 'of' F 'along' K 'by' ranU 'with' ranF , ranN ]" :=
  (@Build_Ran _ _ _ F K ranF ranN ranU _).
Notation "[ 'Ran' 'of' F 'along' K 'by' ranU ]" :=
  [Ran of F along K by ranU with _, _].
Notation "[ 'Ran' 'by' ranU 'with' ranF , ranN ]" :=
  [Ran of _ along _ by ranU with ranF, ranN].
Notation "[ 'Ran' 'by' ranU ]" := [Ran by ranU with _,_].

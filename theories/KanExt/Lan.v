(** * Lan **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

Class IsLan
      (C D E: Category)
      (F: C --> E)(K: C --> D)
      (lanF: D --> E)
      (lanN: F ==> (lanF \o K))
      (lanU: forall {S: D --> E},
          F ==> (S \o K) -> lanF ==> S) :=
  {
    lan_universality:
      forall (S: D --> E)(e: F ==> (S \o K)),
        (lanU e o> K) \o{Fun _ _} lanN == e;
    lan_uniqueness:
      forall (S: D --> E)(e: F ==> (S \o K))(u: lanF ==> S),
        (u o> K) \o{Fun _ _} lanN == e -> u == lanU e
  }.

Structure Lan (C D E: Category)(F: C --> E)(K: C --> D): Type :=
  {
    lanF: D --> E;
    lanN: F ==> (lanF \o K);
    lanU: forall {S: D --> E},
        F ==> (S \o K) -> lanF ==> S;

    lan_prf:> IsLan lanN (@lanU)
  }.
Notation "[ 'Lan' 'of' F 'along' K 'by' lanU 'with' lanF , lanN ]" :=
  (@Build_Lan _ _ _ F K lanF lanN lanU _).
Notation "[ 'Lan' 'by' lanU 'with' lanF , lanN ]" :=
  [Lan of _ along _ by lanU with lanF, lanN].


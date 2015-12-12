Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.

Module Product.
  Class spec (C: Category)(X Y: C)(P: C)(pi1: C P X)(pi2: C P Y) :=
    proof {
        ump: forall Z (f: C Z X)(g: C Z Y),
          exists!_ fg: C Z P, pi1 \o fg == f /\ pi2 \o fg == g
      }.

  Structure type {C: Category}(X Y: C) :=
    make {
        obj: C;
        p1: C obj X;
        p2: C obj Y;

        prf: spec p1 p2
      }.

  Module Ex.
    Notation isProduct := spec.
    Notation Product := type.

    Coercion obj: Product >-> Category.obj.
    Coercion prf: Product >-> isProduct.

    Notation pi1 := Product.p1.
    Notation pi2 := Product.p2.

    Existing Instance prf.

    Arguments ump {C X Y P pi1 pi2}(spec){Z}(f g): clear implicits.
  End Ex.

  Import Ex.

  Lemma uniqueness:
    forall (C: Category)(X Y: C)(P Q: Product X Y),
      isomorphic C P Q.
  Proof.
    intros; unfold isomorphic, invertible.
    destruct (Product.ump Q (pi1 P)(pi2 P)) as [f [[Heqf1 Heqf2] _]]; exists f.
    destruct (Product.ump P (pi1 Q)(pi2 Q)) as [g [[Heqg1 Heqg2] _]]; exists g.
    split.
    - destruct (Product.ump P (pi1 P)(pi2 P)) as [h [_ H]].
      eapply transitivity; [apply symmetry, H | apply H].
      + split.
        * eapply transitivity; [apply symmetry, catCa |].
          eapply transitivity; [apply catCsc, Heqg1 | apply Heqf1].
        * eapply transitivity; [apply symmetry, catCa |].
          eapply transitivity; [apply catCsc, Heqg2 | apply Heqf2].
      + split; apply catC1f.
    - destruct (Product.ump Q (pi1 Q)(pi2 Q)) as [h [_ H]].
      eapply transitivity; [apply symmetry, H | apply H].
      + split.
        * eapply transitivity; [apply symmetry, catCa |].
          eapply transitivity; [apply catCsc, Heqf1 | apply Heqg1].
        * eapply transitivity; [apply symmetry, catCa |].
          eapply transitivity; [apply catCsc, Heqf2 | apply Heqg2].
      + split; apply catC1f.
  Qed.
End Product.
Export Product.Ex.

Module Coproduct.
  Class spec (C: Category)(X Y: C)(Cp: C)(inj1: C X Cp)(inj2: C Y Cp) :=
    proof {
        ump: forall Z (f: C X Z)(g: C Y Z),
          exists!_ f_g: C Cp Z, f_g \o inj1 == f /\ f_g \o inj2 == g
      }.

  Structure type {C: Category}(X Y: C) :=
    make {
        obj: C;
        i1: C X obj;
        i2: C Y obj;

        prf: spec i1 i2
      }.

  Module Ex.
    Notation isCoproduct := spec.
    Notation Coproduct := type.

    Coercion obj: Coproduct >-> Category.obj.
    Coercion prf: Coproduct >-> isCoproduct.

    Existing Instance prf.

    Notation inj1 := i1.
    Notation inj2 := i2.

    Arguments ump {C X Y Cp inj1 inj2}(spec){Z}(f g): clear implicits.
  End Ex.

  Import Ex.

  Lemma uniqueness (C: Category)(X Y: C)(P Q: Coproduct X Y):
    isomorphic C P Q.
  Proof.
    intros; unfold isomorphic, invertible.
    destruct (ump P (inj1 Q) (inj2 Q)) as [f [[Heqf1 Heqf2] _]]; exists f.
    destruct (ump Q (inj1 P) (inj2 P)) as [g [[Heqg1 Heqg2] _]]; exists g.
    split.
    - destruct (ump P (inj1 P) (inj2 P)) as [h [_ H]].
      eapply transitivity; [apply symmetry, H | apply H].
      + split.
        * eapply transitivity; [apply catCa |].
          eapply transitivity; [apply catCsd, Heqf1 | apply Heqg1].
        * eapply transitivity; [apply catCa |].
          eapply transitivity; [apply catCsd, Heqf2 | apply Heqg2].
      + split; apply catCf1.
    - destruct (ump Q (inj1 Q) (inj2 Q)) as [h [_ H]].
      eapply transitivity; [apply symmetry, H | apply H].
      + split.
        * eapply transitivity; [apply catCa |].
          eapply transitivity; [apply catCsd, Heqg1 | apply Heqf1].
        * eapply transitivity; [apply catCa |].
          eapply transitivity; [apply catCsd, Heqg2 | apply Heqf2].
      + split; apply catCf1.
  Qed.
End Coproduct.
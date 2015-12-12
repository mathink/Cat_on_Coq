Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.

(** * イコライザ(Equalizer)
#$f,g: X\rightarrow$# のイコライザとは
#$f \circ eq = g \circ eq$# なる組 #$(Eq,eq: Eq \rightarrow X)$# で、
以下の普遍性を満たすもの。
#\[
\xymatrix{
Eq \ar[r]^{eq} & X \ar@/^4pt/[r]^f \ar@/_4pt/[r]_g & Y \\
Z \ar@{-->}[u]^{z'} \ar[ur]_z & &
}
\]#
 **)
Module Equalizer.
  Class spec (C: Category)(X Y: C)(f g: C X Y)(Eq: C)(eq: C Eq X) :=
    proof {
        equalize: f \o eq == g \o eq;
        ump: forall Z (z: C Z X),
            f \o z == g \o z -> exists!_ z': C Z Eq, eq \o z' == z
      }.

  Structure type (C: Category)(X Y: C)(f g: C X Y) :=
    {
      obj: C;
      arr: C obj X;

      prf: spec f g arr
    }.

  Module Ex.
    Notation isEqualizer := spec.
    Notation Equalizer := type.

    Coercion obj: Equalizer >-> Category.obj.
    Coercion arr: Equalizer >-> Setoid.carrier.
    Coercion prf: Equalizer >-> isEqualizer.

    Existing Instance prf.
    Arguments ump {C X Y f g Eq eq}(spec){Z}(z) _: clear implicits.
  End Ex.
  Import Ex.

  Lemma uniqueness (C: Category)(X Y: C)(f g: C X Y)(E E': Equalizer f g):
    isomorphic C E E'.
  Proof.
    unfold isomorphic, invertible.
    destruct (ump E' E (equalize)) as [eq [Heq _]]; exists eq.
    destruct (ump E E' (equalize)) as [eq' [Heq' _]]; exists eq'.
    split.
    - destruct (ump E E equalize) as [h [_ H]].
      eapply transitivity; [apply symmetry, H | apply H].
      + eapply transitivity; [apply symmetry, catCa |].
        eapply transitivity; [apply catCsc, Heq' | apply Heq].
      + apply catC1f.
    - destruct (ump E' E' equalize) as [h [_ H]].
      eapply transitivity; [apply symmetry, H | apply H].
      + eapply transitivity; [apply symmetry, catCa |].
        eapply transitivity; [apply catCsc, Heq | apply Heq'].
      + apply catC1f.
  Qed.
End Equalizer.
Export Equalizer.Ex.

(** * コイコライザ(Coequalizer)
イコライザの双対的な概念である。

#$f,g: X\rightarrow$# のコイコライザとは
#$coeq \circ f = coeq \circ g$# なる組 #$(Coeq, coeq: Y \rightarrow Coeq)$# で、
以下の普遍性を満たすもの。
#\[
\xymatrix{
X \ar@/^4pt/[r]^f \ar@/_4pt/[r]_g & Y \ar[r]^{coeq} \ar[dr]_z & Coeq \ar@{-->}[d]^{z'}\\
& & Z
}
\]#
 **)
Module Coequalizer.
  Class spec (C: Category)(X Y: C)(f g: C X Y)(Coeq: C)(coeq: C Y Coeq) :=
    proof {
        coequalize: coeq \o f == coeq \o g;
        ump: forall Z (z: C Y Z),
            z \o f == z \o g -> exists!_ z': C Coeq Z, z' \o coeq == z
      }.

  Class type (C: Category)(X Y: C)(f g: C X Y) :=
    make {
        obj: C;
        arr: C Y obj;

        prf: spec f g arr
      }.
  
  Module Ex.
    Notation isCoequalizer := spec.
    Notation Coequalizer := type.

    Coercion obj: Coequalizer >-> Category.obj.
    Coercion arr: Coequalizer >-> Setoid.carrier.
    Coercion prf: Coequalizer >-> isCoequalizer.

    Existing Instance prf.
    Arguments ump {C X Y f g Coeq coeq}(spec){Z}(z) _: clear implicits.
  End Ex.

  Import Ex.

    Lemma uniqueness (C: Category)(X Y: C)(f g: C X Y)(E E': Coequalizer f g):
    isomorphic C E E'.
  Proof.
    unfold isomorphic, invertible.
    destruct (ump E E' (coequalize)) as [coeq [Hcoeq _]]; exists coeq.
    destruct (ump E' E (coequalize)) as [coeq' [Hcoeq' _]]; exists coeq'.
    split.
    - destruct (ump E E coequalize) as [h [_ H]].
      eapply transitivity; [apply symmetry, H | apply H].
      + eapply transitivity; [apply catCa |].
        eapply transitivity; [apply catCsd, Hcoeq | apply Hcoeq'].
      + apply catCf1.
    - destruct (ump E' E' coequalize) as [h [_ H]].
      eapply transitivity; [apply symmetry, H | apply H].
      + eapply transitivity; [apply catCa |].
        eapply transitivity; [apply catCsd, Hcoeq' | apply Hcoeq].
      + apply catCf1.
  Qed.

End Coequalizer.
Export Coequalizer.Ex.

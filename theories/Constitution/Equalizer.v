Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Setoid
        COC.Category.

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
  Class spec (C: Category)(X Y: C)(f g: C X Y)(Eq: C)(eq: C Eq X)(univ: forall {Z}, C Z X -> C Z Eq) :=
    proof {
        univ_subst:> forall Z, Proper ((==) ==> (==)) (@univ Z);
        equalize: f \o eq == g \o eq;
        ump: forall Z (z: C Z X),
            f \o z == g \o z -> eq \o (univ z) == z;
        uniq: forall Z (z: C Z X),
            f \o z == g \o z -> 
            forall (z': C Z Eq), eq \o z' == z -> z' == univ z
      }.

  Structure type (C: Category)(X Y: C)(f g: C X Y) :=
    {
      obj: C;
      arr: C obj X;
      univ: forall {Z}, C Z X -> C Z obj;

      prf: spec f g arr (@univ)
    }.

  Module Ex.
    Notation isEqualizer := spec.
    Notation Equalizer := type.

    Coercion obj: Equalizer >-> Category.obj.
    Coercion arr: Equalizer >-> Setoid.carrier.
    Coercion prf: Equalizer >-> isEqualizer.

    Existing Instance prf.
    Arguments ump {C X Y f g Eq eq univ}(spec){Z}(z) _: clear implicits.
    Arguments uniq {C X Y f g Eq eq univ}(spec){Z}(z) _ _ _: clear implicits.
  End Ex.
  Import Ex.

  Lemma uniqueness (C: Category)(X Y: C)(f g: C X Y)(E E': Equalizer f g):
    isomorphic C E E'.
  Proof.
    unfold isomorphic, invertible.
    set (univ E' E) as h.
    set (univ E E') as h'.
    exists h, h'.
    generalize (ump E' E equalize); intro H.
    generalize (ump E E' equalize); intro H'.
    split.
    - generalize (uniq E E equalize); intro Hid.
      rewrite (Hid (h' \o h)).
      + rewrite (Hid (Id E)); try now idtac.
        now rewrite catC1f.
      + subst h h'.
        now rewrite <- catCa, H', H.
    - generalize (uniq E' E' equalize); intro Hid.
      rewrite (Hid (h \o h')).
      + rewrite (Hid (Id E')); try now idtac.
        now rewrite catC1f.
      + subst h h'.
        now rewrite <- catCa, H, H'.
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
  Class spec (C: Category)(X Y: C)(f g: C X Y)(Coeq: C)(coeq: C Y Coeq)(univ: forall {Z}, C Y Z -> C Coeq Z) :=
    proof {
        univ_subst:> forall Z, Proper ((==) ==> (==)) (@univ Z);
        coequalize: coeq \o f == coeq \o g;
        ump: forall Z (z: C Y Z),
            z \o f == z \o g -> (univ z) \o coeq == z;

        uniq: forall Z (z: C Y Z),
            z \o f == z \o g -> forall (z': C Coeq Z), z' \o coeq == z -> z' == univ z
      }.

  Class type (C: Category)(X Y: C)(f g: C X Y) :=
    make {
        obj: C;
        arr: C Y obj;
        univ: forall {Z: C}, C Y Z -> C obj Z;

        prf: spec f g arr (@univ)
      }.
  
  Module Ex.
    Notation isCoequalizer := spec.
    Notation Coequalizer := type.

    Coercion obj: Coequalizer >-> Category.obj.
    Coercion arr: Coequalizer >-> Setoid.carrier.
    Coercion prf: Coequalizer >-> isCoequalizer.

    Existing Instance prf.
    Arguments ump {C X Y f g Coeq coeq univ}(spec){Z}(z) _: clear implicits.
    Arguments uniq {C X Y f g Coeq coeq univ}(spec){Z}(z) _ _ _: clear implicits.
    Arguments univ {C X Y f g}(type){Z}(z): clear implicits.
  End Ex.

  Import Ex.

  Lemma uniqueness (C: Category)(X Y: C)(f g: C X Y)(E E': Coequalizer f g):
    isomorphic C E E'.
  Proof.
    unfold isomorphic, invertible.
    set (univ E E') as h.
    set (univ E' E) as h'.
    exists h, h'.
    generalize (ump E E' coequalize); intro H.
    generalize (ump E' E coequalize); intro H'.
    split.
    - generalize (uniq E E coequalize); intro Hid.
      rewrite (Hid (h' \o h)).
      + rewrite (Hid (Id E)); try now idtac.
        now rewrite catCf1.
      + subst h h'.
        now rewrite catCa, H, H'.
    - generalize (uniq E' E' coequalize); intro Hid.
      rewrite (Hid (h \o h')).
      + rewrite (Hid (Id E')); try now idtac.
        now rewrite catCf1.
      + subst h h'.
        now rewrite catCa, H', H.
  Qed.
End Coequalizer.
Export Coequalizer.Ex.

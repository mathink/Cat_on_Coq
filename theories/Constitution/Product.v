Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid COC.Category.

Module Product.
  Class spec (C: Category)(X Y: C)(P: C)(pi1: C P X)(pi2: C P Y)(univ: forall {Z}, C Z X -> C Z Y -> C Z P) :=
    proof {
        univ_subst:> forall Z, Proper ((==) ==> (==) ==> (==)) (@univ Z);
        ump: forall Z (f: C Z X)(g: C Z Y),
               pi1 \o (univ f g) == f /\ pi2 \o (univ f g) == g;
        uniq: forall Z (f: C Z X)(g: C Z Y)(fg: C Z P),
                pi1 \o fg == f /\ pi2 \o fg == g ->
                fg == univ f g
      }.

  Structure type {C: Category}(X Y: C) :=
    make {
        obj: C;
        p1: C obj X;
        p2: C obj Y;
        univ: forall {Z}, C Z X -> C Z Y -> C Z obj;

        prf: spec p1 p2 (@univ)
      }.

  Module Ex.
    Notation isProduct := spec.
    Notation Product := type.

    Coercion obj: Product >-> Category.obj.
    Coercion prf: Product >-> isProduct.

    Notation pi1 := Product.p1.
    Notation pi2 := Product.p2.

    Existing Instance prf.

    (* Notation "<: f , g :>" := (univ _ f g). *)
    Arguments ump {C X Y P pi1 pi2 univ}(spec){Z}(f g): clear implicits.
    Arguments uniq {C X Y P pi1 pi2 univ}(spec){Z}(f g fg _): clear implicits.
  End Ex.

  Import Ex.

  Lemma uniqueness:
    forall (C: Category)(X Y: C)(P Q: Product X Y),
      isomorphic C P Q.
  Proof.
    intros; unfold isomorphic, invertible.
    set (univ Q (pi1 P) (pi2 P)) as f.
    set (univ P (pi1 Q) (pi2 Q)) as g.
    generalize (ump Q (pi1 P) (pi2 P)); intros [Hf1 Hf2].
    generalize (ump P (pi1 Q) (pi2 Q)); intros [Hg1 Hg2].
    exists f, g; split.
    - rewrite (uniq P (pi1 P) (pi2 P) (Id P)).
      + apply (uniq P (pi1 P) (pi2 P) (g \o f)).
        split.
        * subst f g.
          now rewrite <- catCa, Hg1.
        * subst f g.
          now rewrite <- catCa, Hg2.
      + now split; rewrite catC1f.
    - rewrite (uniq Q (pi1 Q) (pi2 Q) (Id Q)).
      + apply (uniq Q (pi1 Q) (pi2 Q) (f \o g)).
        split.
        * subst f g.
          now rewrite <- catCa, Hf1.
        * subst f g.
          now rewrite <- catCa, Hf2.
      + now split; rewrite catC1f.
  Qed.

  Definition hom (C: Category)(prod: forall X Y, Product X Y)
             (X Y Z W: C)(f: C X Y)(g: C Z W): C (prod X Z) (prod Y W) :=
    univ (prod Y W) (f \o pi1 (prod X Z)) (g \o pi2 (prod X Z)).
End Product.
Export Product.Ex.

Module Coproduct.
  Class spec (C: Category)(X Y: C)(Cp: C)(inj1: C X Cp)(inj2: C Y Cp)(univ: forall {Z}, C X Z -> C Y Z -> C Cp Z) :=
    proof {
        univ_subst:> forall Z, Proper ((==) ==> (==) ==> (==)) (@univ Z);
        ump: forall Z (f: C X Z)(g: C Y Z),
            univ f g \o inj1 == f /\ univ f g \o inj2 == g;
        uniq: forall Z (f: C X Z)(g: C Y Z)(f_g: C Cp Z),
            f_g \o inj1 == f /\ f_g \o inj2 == g -> f_g == univ f g
      }.

  Structure type {C: Category}(X Y: C) :=
    make {
        obj: C;
        i1: C X obj;
        i2: C Y obj;
        univ: forall {Z}, C X Z -> C Y Z -> C obj Z;

        prf: spec i1 i2 (@univ)
      }.

  Module Ex.
    Notation isCoproduct := spec.
    Notation Coproduct := type.

    Coercion obj: Coproduct >-> Category.obj.
    Coercion prf: Coproduct >-> isCoproduct.

    Existing Instance prf.

    Notation inj1 := i1.
    Notation inj2 := i2.

    Arguments ump {C X Y Cp inj1 inj2 univ}(spec){Z}(f g): clear implicits.
    Arguments uniq {C X Y Cp inj1 inj2 univ}(spec){Z}(f g) _ _: clear implicits.
    Arguments univ {C X Y}(t){Z}(f g): clear implicits.
  End Ex.

  Import Ex.

  Lemma uniqueness (C: Category)(X Y: C)(P Q: Coproduct X Y):
    isomorphic C P Q.
  Proof.
    intros; unfold isomorphic, invertible.
    set (univ P (inj1 Q) (inj2 Q)) as f.
    set (univ Q (inj1 P) (inj2 P)) as g.
    generalize (ump Q (inj1 P) (inj2 P)); intros [Hf1 Hf2].
    generalize (ump P (inj1 Q) (inj2 Q)); intros [Hg1 Hg2].
    exists f, g; split.
    - rewrite (uniq P (inj1 P) (inj2 P) (Id P)).
      + apply (uniq P (inj1 P) (inj2 P) (g \o f)).
        split.
        * subst f g.
          now rewrite catCa, Hg1.
        * subst f g.
          now rewrite catCa, Hg2.
      + now split; rewrite catCf1.
    - rewrite (uniq Q (inj1 Q) (inj2 Q) (Id Q)).
      + apply (uniq Q (inj1 Q) (inj2 Q) (f \o g)).
        split.
        * subst f g.
          now rewrite catCa, Hf1.
        * subst f g.
          now rewrite catCa, Hf2.
      + now split; rewrite catCf1.
  Qed.        

  Definition hom (C: Category)(coprod: forall X Y, Coproduct X Y)
             (X Y Z W: C)(f: C X Y)(g: C Z W): C (coprod X Z) (coprod Y W) :=
    univ (coprod X Z) (inj1 (coprod Y W) \o f) (inj2 (coprod Y W) \o g).
End Coproduct.
Export Coproduct.Ex.

(* duality *)
Instance product_op_coproduct (C: Category)(X Y: C)(P: Product X Y): isCoproduct (C:=Category.op C) (Product.p1 P) (Product.p2 P) (@Product.univ _ _ _ P).
Proof.
  split; simpl.
  - now apply (Product.univ_subst).
  - now intros; apply (Product.ump P).
  - now simpl; intros; apply (Product.uniq P).
Qed.

Instance coproduct_op_product (C: Category)(X Y: C)(P: Coproduct X Y): isProduct (C:=Category.op C) (Coproduct.i1 P) (Coproduct.i2 P) (@Coproduct.univ _ _ _ P).
Proof.
  split; simpl.
  - now apply (Coproduct.univ_subst).
  - now intros; apply (Coproduct.ump P).
  - now simpl; intros; apply (Coproduct.uniq P).
Qed.
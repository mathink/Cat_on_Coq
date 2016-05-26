Set Implicit Arguments.
Unset Strict Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category COC.Constitution.

Module Exponential.
  Class spec (C: Category)(prod: forall X Y, Product X Y)(Y Z: C)
        (exp: C)(ev: C (prod exp Y) Z)
        (univ: forall (X: C)(f: C (prod X Y) Z), C X exp) :=
    proof {
        univ_subst: forall X, Proper ((==) ==> (==)) (@univ X);
        ump: forall (X: C)(f: C (prod X Y) Z),
            ev \o (Product.hom prod (@univ _ f) (Id Y)) == f;
        uniq: forall (X: C)(f: C (prod X Y) Z)(f': C X exp),
            ev \o (Product.hom prod f' (Id Y)) == f ->
            f' == @univ _ f;
      }.

  Structure type (C: Category)(prod: forall X Y, Product X Y)(Y Z: C) :=
    make {
        obj: C;
        ev: C (prod obj Y) Z;

        univ: forall (X: C)(f: C (prod X Y) Z), C X obj;

        prf: spec ev (@univ)
      }.

  Module Ex.
    Notation isExponential := spec.
    Notation Exponential := type.

    Coercion obj: Exponential >-> Category.obj.
    Coercion prf: Exponential >-> isExponential.

    Existing Instance prf.

    (* optional *)
    Notation isExp := isExponential.
    Notation Exp := Exponential.
  End Ex.

End Exponential.
Export Exponential.Ex.
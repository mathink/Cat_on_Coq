Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.

Module Equalizer.
  Class spec (C: Category)(X Y: C)(f g: C X Y)(E: C)(e: C E X) :=
    proof {
        equalize: f \o e == g \o e;
        ump: forall Z (z: C Z X),
            f \o z == g \o z -> exists!_ z': C Z E, e \o z' == z
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
  End Ex.
End Equalizer.
Export Equalizer.Ex.
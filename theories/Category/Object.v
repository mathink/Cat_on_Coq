Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid.
Require Import COC.Category.Core.

Module Terminal.
  Class spec (C: Category)(t: C)(f: forall X: C, C X t): Prop :=
    terminality:
      forall (X: C)(g: C X t), f X == g.

  Structure type (C: Category) :=
    make {
        object: C;
        morphism: forall X: C, C X object;

        prf: spec (@morphism)
      }.

  Module Ex.
    Notation isTerminal := spec.
    Notation Terminal := type.
    Coercion object: Terminal >-> Category.obj.
    Coercion prf: Terminal >-> isTerminal.
    Existing Instance prf.
    Notation "'!' X" := (morphism _ X) (at level 20, no associativity).
  End Ex.
End Terminal.
Export Terminal.Ex.


Module Initial.
  Class spec (C: Category)(s: C)(f: forall X: C, C s X): Prop :=
    initiality:
      forall (X: C)(g: C s X), f X == g.

  Structure type (C: Category) :=
    make {
        object: C;
        morphism: forall X: C, C object X;

        prf: spec (@morphism)
      }.

  Module Ex.
    Notation isInitial := spec.
    Notation Initial := type.
    Coercion object: Initial >-> Category.obj.
    Coercion prf: Initial >-> isInitial.
    Existing Instance prf.
    Notation "'¡' X" := (morphism _ X) (at level 20, no associativity).
  End Ex.
End Initial.
Export Initial.Ex.

Module Null.
  Class spec (C: Category)(z: C)(f: forall X: C, C z X)(g: forall X: C, C X z): Prop :=
    {
      is_Initial:> isInitial f;
      is_Terminal:> isTerminal g
    }.

  Structure type (C: Category) :=
    make {
        object: C;
        imorphism: forall X: C, C object X;
        tmorphism: forall X: C, C X object;

        prf: spec (@imorphism) (@tmorphism)
      }.

  Module Ex.
    Notation isNull := spec.
    Notation Null := type.
    Coercion object: Null >-> Category.obj.
    Coercion prf: Null >-> isNull.
    Coercion is_Initial: isNull >-> isInitial.
    Coercion is_Terminal: isNull >-> isTerminal.
    Existing Instance prf.
    Existing Instance is_Initial.
    Existing Instance is_Terminal.
  End Ex.
  Import Ex.

  Definition initial (C: Category)(z: Null C): Initial C := Initial.make z.
  Definition terminal (C: Category)(z: Null C): Terminal C := Terminal.make z.
  
End Null.
Export Null.Ex.


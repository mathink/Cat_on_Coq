Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid.
Require Import COC.Category.Core.

Module Initial.
  Class spec (C: Category)(i: C)(u: forall c, C i c) :=
    proof {
        ump: forall c (f: C i c), f == u c
      }.

  Structure type (C: Category) :=
    make {
        obj: C;
        univ: forall c, C obj c;

        prf: spec (@univ)
      }.

  Module Ex.
    Notation isInitial := spec.
    Notation Initial := type.

    Coercion obj: Initial >-> Category.obj.
    Coercion prf: Initial >-> isInitial.

    Existing Instance prf.

    Arguments univ {C}(t c): clear implicits.
  End Ex.

End Initial.
Export Initial.Ex.

Module Terminal.
  Class spec (C: Category)(t: C)(u: forall c, C c t) :=
    proof {
        ump: forall c (f: C c t), f == u c
      }.

  Structure type (C: Category) :=
    make {
        obj: C;
        univ: forall c, C c obj;

        prf: spec (@univ)
      }.

  Module Ex.
    Notation isTerminal := spec.
    Notation Terminal := type.

    Coercion obj: Terminal >-> Category.obj.
    Coercion prf: Terminal >-> isTerminal.

    Existing Instance prf.

    Arguments univ {C}(t c): clear implicits.
  End Ex.

End Terminal.
Export Terminal.Ex.

Module Zero.
  Class spec (C: Category)(z: C)(i: forall c, C z c)(t: forall c, C c z) :=
    proof {
        is_initial:> isInitial i;
        is_terminal:> isTerminal t
      }.

  Structure type (C: Category) :=
    make {
        obj: C;
        init: forall c, C obj c;
        term: forall c, C c obj;
        
        prf: spec (@init) (@term)
      }.

  Module Ex.
    Notation isZero := spec.
    Notation Zero := type.

    Coercion obj: Zero >-> Category.obj.
    Coercion prf: Zero >-> isZero.

    Coercion is_initial: isZero >-> isInitial.
    Coercion is_terminal: isZero >-> isTerminal.

    Existing Instance prf.

    Arguments init {C}(t c): clear implicits.
    Arguments term {C}(t c): clear implicits.
  End Ex.

End Zero.
Export Zero.Ex.


Definition zero (C: Category)(z: Zero C)(X Y: C): C X Y :=
  Zero.init z Y \o Zero.term z X.
Arguments zero {C}(z X Y): clear implicits.

Lemma zero_comp_zero_dom:
  forall (C: Category)(z: Zero C)(X Y Z: C)(f: C X Y),
    zero z Y Z \o f == zero z X Z.
Proof.
  intros; unfold zero.
  eapply transitivity; [apply catCa |].
  apply catCsd.
  apply Terminal.ump.
Qed.

Lemma zero_comp_zero_cod:
  forall (C: Category)(z: Zero C)(X Y Z: C)(g: C Y Z),
    g \o zero z X Y == zero z X Z.
Proof.
  intros; unfold zero.
  eapply transitivity; [apply symmetry, catCa |].
  apply catCsc.
  apply Initial.ump.
Qed.

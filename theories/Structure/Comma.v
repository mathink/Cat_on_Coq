Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.


Module Comma.
  (* 
      E -- T -> C <- S -- D
   *)
  Record obj (E C D: Category)(T: Functor E C)(S: Functor D C) :=
    triple { dom: E; cod: D; morph: C (T dom) (S cod)}.

  Module Ex.
    Coercion morph: obj >-> Setoid.carrier.
  End Ex.    
  Import Ex.
  
  Class spec (E C D: Category)(T: Functor E C)(S: Functor D C)
        (f g: obj T S)(k: E (dom f) (dom g))(h: D (cod f) (cod g)) :=
    proof {
        comm: g \o fmap T k == fmap S h \o f
      }.

  Structure type (E C D: Category)(T: Functor E C)(S: Functor D C)(f g: obj T S) :=
    make {
        dmorph: E (dom f) (dom g);
        cmorph: D (cod f) (cod g);

        prf: spec dmorph cmorph
      }.

  Module MorphEx.
    Coercion prf: type >-> spec.
    Existing Instance prf.

    Notation build f g := (@make _ _ _ _ _ _ _ f g (@proof _ _ _ _ _ _ _ _ _ _)).
  End MorphEx.
  Import MorphEx.

  
  Program Definition compose {E C D: Category}(T: Functor E C)(S: Functor D C)
          (f g h: obj T S)(kh1: type f g)(kh2: type g h): type f h :=
    build (dmorph kh2 \o dmorph kh1) (cmorph kh2 \o cmorph kh1).
  Next Obligation.
    intros.
    eapply transitivity.
    - eapply transitivity; [apply Category.comp_subst |].
      + apply Functor.fmap_comp.
      + apply reflexivity.
      + eapply transitivity.
        * apply symmetry, Category.comp_assoc.
        * apply Category.comp_subst; [apply reflexivity |].
          apply comm.
    - eapply transitivity; [apply Category.comp_assoc |].
      apply symmetry.
      eapply transitivity.
      eapply transitivity; [apply Category.comp_subst |].
      + apply reflexivity.
      + apply Functor.fmap_comp.
      + eapply transitivity; [apply Category.comp_assoc |].
        apply Category.comp_subst; [| apply reflexivity].
        apply symmetry, comm.
      + apply reflexivity.
  Qed.
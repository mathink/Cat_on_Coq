Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid.
Require Import COC.Category.Core COC.Category.Functor.

(** 
 ** 自然変換
流れ的にね。
 **)
(*
 NOTE:
 自然変換の型パラメータは、カノニカルなものを利用する。
 すなわち、 Coq の Eq で解決できるものを使うということ。
  Natrans 型パラメータに 函数のみを取ることで、例えば合成の順序などの違いを無視できるようになる
 *)

Module Natrans.
  Class canonical_spec
        (C D: Category)
        (Fo: C -> D)(Fa: Fmap C D Fo)
        (Go: C -> D)(Ga: Fmap C D Go)
        (natrans: forall X: C, D (Fo X) (Go X)) :=
    proof {
        dom_isFunctor: isFunctor Fa;
        cod_isFunctor: isFunctor Ga;
        naturality:
          forall (X Y: C)(f: C X Y),
            (natrans Y \o Fa _ _ f == Ga _ _ f \o natrans X :> D _ _)%category
      }.

  Structure canonical {C D: Category}
            (Fo: C -> D)(Fa: Fmap C D Fo)(Go: C -> D)(Ga: Fmap C D Go)
    :=
    make {
        natrans (X: C): D (Fo X) (Go X);
        prf: canonical_spec Fa Ga (@natrans)
      }.

  Notation canonical_build natrans := (@make _ _ _ _ _ _ natrans _).

  Definition spec (C D: Category)
             (F G: Functor C D)
             (natrans: forall X: C, D (F X) (G X)) :=
    @canonical_spec
      C D
      (@Functor.fobj _ _ F) (@Functor.fmap _ _ F)
      (@Functor.fobj _ _ G) (@Functor.fmap _ _ G)
      (@natrans).

  Definition type {C D: Category}(F G: Functor C D) :=
    (@canonical C D
                (@Functor.fobj _ _ F) (@Functor.fmap _ _ F)
                (@Functor.fobj _ _ G) (@Functor.fmap _ _ G)).

  Notation build F G natrans :=
    (@make _ _ _ _ _ _ natrans (@proof _ _ _ _ _ _ natrans F G _)).

  Module Ex.
    Notation Natrans := type.
    Notation isNatrans := spec.
    Coercion natrans: canonical >-> Funclass.
    Coercion prf: canonical >-> canonical_spec.
    Existing Instance prf.
    Existing Instance dom_isFunctor.
    Existing Instance cod_isFunctor.
  End Ex.

  Import Ex.

  Definition dom {C D: Category}{F G: Functor C D}(S: Natrans F G) := F.
  Definition cod {C D: Category}{F G: Functor C D}(S: Natrans F G) := G.


  Program Definition canonical_compose
          {C D: Category}
          {Fo Go Ho: C -> D}
          {Fa: Fmap C D Fo}{Ga: Fmap C D Go}{Ha: Fmap C D Ho}
          (S: canonical Fa Ga)(T: canonical Ga Ha)
    : canonical Fa Ha :=
    canonical_build (fun X => T X \o S X).
  Next Obligation.
    intros; split; [apply S | apply T |].
    intros X Y f; simpl.
    eapply transitivity;
      [ apply Category.comp_assoc |].
    eapply transitivity;
      [ apply Category.comp_subst |].
    - apply naturality.
    - apply reflexivity.
    - eapply transitivity;
      [ apply symmetry,Category.comp_assoc |].
      eapply transitivity;
        [ apply Category.comp_subst |].
      + apply reflexivity.
      + apply naturality.
      + apply Category.comp_assoc.
  Qed.

  Program Definition compose {C D: Category}{F G H: Functor C D}(S: Natrans F G)(T: Natrans G H): Natrans F H :=
    build F H (canonical_compose S T).
  Next Obligation.
    intros.
    apply naturality.
  Qed.

  Program Definition id {C D: Category}(F: Functor C D): Natrans F F :=
    build F F (fun X => Id (F X)).
  Next Obligation.
    intros C D F X Y f; simpl.
    eapply transitivity;
      [ apply Category.comp_id_cod
      | apply symmetry, Category.comp_id_dom ].
  Qed.

  Definition equal {C D: Category}(F G: Functor C D): relation (Natrans F G)
    := (fun (S T: Natrans F G) => forall X: C, S X == T X).

  Program Definition setoid {C D: Category}(F G: Functor C D) :=
    Setoid.build (@equal C D F G).
  Next Obligation.
    intros C D F G S X; apply reflexivity.
  Qed.
  Next Obligation.
    intros C D F G S T Heq X; generalize (Heq X); apply symmetry.
  Qed.
  Next Obligation.
    intros C D F G S T U Heq Heq' X;
    generalize (Heq X) (Heq' X); apply transitivity.
  Qed.
End Natrans.
Export Natrans.Ex.

Module NaturalIso.
  
  Class spec {C D: Category}{F G: Functor C D}
        (S: Natrans F G)(T: Natrans G F) :=
    iso: forall X: C, Iso (S X) (T X).

  Structure type {C D: Category}(F G: Functor C D) :=
    make {
        natrans: Natrans F G;
        inv: Natrans G F;

        prf: spec natrans inv
      }.

  Module Ex.
    Notation isNaturalIso := spec.
    Notation NaturalIso := type.
    Existing Instance prf.
    Coercion natrans: type >-> Natrans.
    Coercion prf: type >-> spec.
  End Ex.

End NaturalIso.
Export NaturalIso.Ex.

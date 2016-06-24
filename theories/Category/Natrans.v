Set Implicit Arguments.
Unset Strict Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid.
Require Import COC.Category.Category COC.Category.Functor.

(** 
 ** 自然変換
流れ的にね。
 **)
(**
 NOTE:
 自然変換の型パラメータは、カノニカルなものを利用する。
 すなわち、 Coq の eq で解決できるものを使うということ。
 型パラメータに 函数のみを取ることで、例えば合成の順序の違いなどを無視できるようになる
 **)

Module Natrans.
  Class spec
        (C D: Category)
        (F G: Functor C D)
        (natrans: forall X: C, D (F X) (G X)) :=
    proof {
        naturality:
          forall (X Y: C)(f: C X Y),
            (natrans Y \o fmap F f == fmap G f \o natrans X :> D _ _)
      }.

  Structure type {C D: Category}(F G: Functor C D) :=
    make {
        natrans (X: C): D (F X) (G X);
        prf: spec (@natrans)
      }.

  Notation build F G natrans := (@make _ _ F G natrans (@proof _ _ F G natrans _)).

  Module Ex.
    Notation Natrans := type.
    Notation isNatrans := spec.
    Coercion natrans: Natrans >-> Funclass.
    Coercion prf: type >-> spec.
    Existing Instance prf.
  End Ex.

  Import Ex.

  Definition dom {C D: Category}{F G: Functor C D}(S: Natrans F G) := F.
  Definition cod {C D: Category}{F G: Functor C D}(S: Natrans F G) := G.


  Program Definition compose {C D: Category}{F G H: Functor C D}(S: Natrans F G)(T: Natrans G H): Natrans F H :=
    build F H (fun X => T X \o S X).
  Next Obligation.
    rewrite catCa, naturality, <- catCa.
    now rewrite <- catCa, <- naturality.
  Qed.

  Program Definition id {C D: Category}(F: Functor C D): Natrans F F :=
    build F F (fun X => Id (F X)).
  Next Obligation.
    now rewrite catCf1, catC1f.
  Qed.

  Definition equal {C D: Category}(F G: Functor C D): relation (Natrans F G)
    := (fun (S T: Natrans F G) => forall X: C, S X == T X).

  Program Definition setoid {C D: Category}(F G: Functor C D) :=
    Setoid.build (@equal C D F G).
  Next Obligation.
    intros S X; reflexivity.
  Qed.
  Next Obligation.
    intros S T Heq X; symmetry; apply Heq. 
  Qed.
  Next Obligation.
    intros S T U Heq Heq' X; rewrite (Heq X), (Heq' X); reflexivity.
  Qed.
End Natrans.
Export Natrans.Ex.

Require Import COC.Category.Morphism.

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




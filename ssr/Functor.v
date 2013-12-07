(* 
   Definitions of Structure of (Locally Small) Category.
 *)

Require Import 
Ssreflect.ssreflect
Ssreflect.ssrfun
Ssreflect.eqtype
Ssreflect.ssrbool

Setoid
Category.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module Functor.

  Section Properties.

    Variables (C D: category)
              (fobj: C -> D)
              (farr: forall {X Y: C}, Hom X Y --> Hom (fobj X) (fobj Y)).
    Arguments farr {X Y}.
    Definition functor_ident :=
      forall (X: C), farr (ident X) === ident (fobj X).

    Definition functor_compose :=
      forall (X Y Z: C)(f: Hom X Y)(g: Hom Y Z),
        farr (g•f) === farr g•farr f.

  End Properties.

  Structure mixin_of
            (C D: category)
            (fobj: C -> D)
            (farr: forall {X Y: C}, Hom X Y --> Hom (fobj X) (fobj Y)) :=
    Mixin
      { _: functor_ident (@farr);
        _: functor_compose (@farr) }.
  Notation class_of := mixin_of (only parsing).

  Section ClassDef.
    Structure type (C D: category) :=
      Pack
        { fobj;
          farr;
          _: @class_of C D fobj farr;
          _: C -> D;
          _: forall {X Y: C}, Hom X Y --> Hom (fobj X) (fobj Y) }.
    Local Coercion fobj: type >-> Funclass.
    Variables (C D: category)
              (fo: C -> D)
              (fa: forall {X Y: C}, Hom X Y --> Hom (fo X) (fo Y))
              (t: type C D).

    Definition class :=
      let: Pack _ _ c _ _ := t return class_of (farr t) in c.

    Definition pack c := @Pack C D fo fa c fo fa.

  End ClassDef.

  Module Exports.
    Coercion fobj: type >-> Funclass.
    Notation functor := type.
    Notation FunctorMixin := Mixin.
    Notation FunctorType Fo Fa m := (@pack _ _ Fo Fa m).
    Definition fmap {C D: category}{F: functor C D}
               {X Y: C}(f: Hom X Y): Hom (F X) (F Y) := @farr C D F X Y f.
    Arguments fmap {C D}(F){X Y}(f).
  End Exports.    
End Functor.
Export Functor.Exports.

Require Import Ssreflect.seq.

Section ListFunctor.
  
  Section map_as_morphism.
    Variables (dT cT: Sets).

    Lemma map_Morphism_wd:
      Morphism.well_defined (@map dT cT).
    Proof.
      rewrite/Morphism.well_defined /setoid_eq /= /ext_eq /=.
      move=> f g Heq; elim=> [//=| h t IH /=].
      by rewrite (Heq h) IH.
    Qed.

    Canonical map_MorphismMixin := MorphismMixin map_Morphism_wd.
    Canonical map_Morphism := Eval hnf in MorphismType map_MorphismMixin.
  End map_as_morphism.

  Lemma list_functor_ident:
    Functor.functor_ident (@map_Morphism).
  Proof.
    rewrite/Functor.functor_ident /= /setoid_eq /= /ext_eq.
    move=> X; elim=> [//=| h t IH /=].
    by rewrite IH /=.
  Qed.

  Lemma list_functor_compose:
    Functor.functor_compose (@map_Morphism).
  Proof.
    rewrite/Functor.functor_compose /= /setoid_eq /= /ext_eq.
    move=> X Y Z f g ; elim=> [//=| h t IH /=].
    by rewrite IH /=.
  Qed.

  Canonical seq_FunctorMixin := FunctorMixin list_functor_ident list_functor_compose.
  Canonical seq := Eval hnf in FunctorType list _ seq_FunctorMixin.
End ListFunctor.

Eval compute in  (fmap seq S [:: 1; 2 ]).
Eval compute in  (fmap seq negb [:: true; false; false; true; false ]).

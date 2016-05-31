Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Setoid
        COC.Category
        COC.Construction
        COC.Constitution.

Program Definition HomF (C: Category): Bifunctor (Category.op C) C Setoids :=
  Functor.build 
    (fun XY => let (X,Y) := XY in C X Y)
    (fun XY XY' fg => let (f,g) := fg in [: h :-> g \o{C} h \o{C} f]).
Next Obligation.
  revert XY XY' fg.
  intros [X Y] [X' Y'] [f g]; simpl; intros h h' Heq; simpl in *.
  now rewrite Heq.
Qed.
Next Obligation.
  revert X Y.
  intros [X Y] [X' Y'] [f g] [f' g'] [Heqf Heqg] h; simpl in *.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  revert X Y Z f g x.
  intros [X1 Y1] [X2 Y2] [X3 Y3] [f1 g1] [f2 g2] h; simpl in *.
  now rewrite !catCa.
Qed.
Next Obligation.
  revert X x; intros [X Y] f; simpl.
  now rewrite catC1f, catCf1.
Qed.

Module Adjunction.
  Class spec
             (C D: Category)(F: Functor C D)(G: Functor D C)
             (phi: forall {c: C}{d: D}, Map (D (F c) d) (C c (G d)))
             (psi: forall {c: C}{d: D}, Map (C c (G d)) (D (F c) d)) :=
    proof {
        iso_phi_psi:
          forall (c: C)(d: D)(f: D (F c) d),
            psi (phi f) == f;
        iso_psi_phi:
          forall (c: C)(d: D)(g: C c (G d)),
            phi (psi g) == g;

        phi_naturality:
          forall (c c': C)(d d': D)(f : C c' c)(g: D d d')(h: D (F c) d),
            phi (g \o h \o fmap F f) == fmap G g \o phi h \o f;

        psi_naturality:
          forall (c c': C)(d d': D)(f : C c' c)(g: D d d')(h: C c (G d)),
            psi (fmap G g \o h \o f) == g \o psi h \o fmap F f
      }.

  Structure type (C D: Category)(F: Functor C D)(G: Functor D C) :=
    make {
        phi: forall {c: C}{d: D}, Map (D (F c) d) (C c (G d));
        psi: forall {c: C}{d: D}, Map (C c (G d)) (D (F c) d);

        prf: spec (@phi) (@psi)
      }.

  Module Ex.
    Notation isAdjunction := spec.
    Notation Adjunction := type.
    Coercion prf: type >-> spec.
    Existing Instance prf.
  End Ex.

  Import Ex.

  (** 
#$Hom_D(-,-)\circ F\times Id_D$#
 **)
  Definition phiF (C D: Category)(F: Functor C D) :=
    (HomF D \o{Cat} (Prod.functor (Functor.op F) (@Functor.id D))).

  (** 
#$Hom_C(-,-)\circ Id_{C^op}\times G$#
 **)
  Definition psiF (C D: Category)(G: Functor D C) :=
    (HomF C \o{Cat} (Prod.functor (@Functor.id (Category.op C)) G)).

  Program Definition phi_Natrans
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G)
    : Natrans (phiF F) (psiF G):=
    Natrans.build (phiF F) (psiF G) (fun cd => let (c,d) := cd in phi adj (c:=c)(d:=d)).
  Next Obligation.
    revert X Y f x.
    intros [c d] [c' d'] [f g] h; simpl in *.
    now rewrite phi_naturality.
  Qed.

  Program Definition psi_Natrans
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G)
    : Natrans (psiF G) (phiF F):=
    Natrans.build (psiF G) (phiF F) (fun cd => let (c,d) := cd in psi adj (c:=c)(d:=d)).
  Next Obligation.
    revert X Y f x.
    intros [c d] [c' d'] [f g] h; simpl in *.
    now rewrite psi_naturality.
  Qed.

  Program Definition eta
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G):
    Natrans (@Functor.id C) (G \o{Cat} F) :=
    Natrans.build (@Functor.id C) (G \o{Cat} F) (fun c: C => phi adj (Id_ D (F c))).
  Next Obligation.
    intros; simpl.
    rewrite <- catCf1.
    rewrite <- (Functor.fmap_id (F Y)).
    rewrite <- phi_naturality.
    rewrite !catCf1.
    symmetry.
    rewrite <- catC1f, catCa.
    rewrite <- phi_naturality.
    now rewrite fn1, !catC1f.
  Qed.

  Program Definition eta_UATo
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G)(c: C)
    : [UA c :=> G ] :=
    UATo.build (eta adj c) (fun d f => psi adj f).
  Next Obligation.
    intros f g H.
    now rewrite H.
  Qed.
  Next Obligation.
    rewrite <- catC1f, catCa.
    rewrite <- phi_naturality.
    rewrite fn1, !catC1f.
    now rewrite iso_psi_phi.
  Qed.
  Next Obligation.
    rewrite <- H.
    rewrite <- (catC1f (f:=(fmap G f' \o (phi adj) (Id F c)))).
    rewrite catCa.
    rewrite <- phi_naturality.
    rewrite fn1, !catC1f.
    now rewrite iso_phi_psi.
  Qed.

  Program Definition epsilon
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G):
    Natrans (F \o{Cat} G) (@Functor.id D)  :=
    Natrans.build (F \o{Cat} G) (@Functor.id D) (fun d: D => psi adj (Id_ C (G d))).
  Next Obligation.
    intros; simpl.
    rewrite <- catCf1.
    rewrite <- psi_naturality.
    rewrite fn1, !catCf1.
    symmetry.
    rewrite <- catC1f, <- fn1, catCa.
    rewrite <- psi_naturality.
    now rewrite !catC1f.
  Qed.

  Program Definition epsilon_UAFrom
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G)(d: D)
    : [UA d <=: F ] :=
    UAFrom.build (epsilon adj d) (fun d f => phi adj f).
  Next Obligation.
    intros f g H.
    now rewrite H.
  Qed.
  Next Obligation.
    rewrite <- catCf1.
    rewrite <- psi_naturality.
    rewrite fn1, !catCf1.
    now rewrite iso_phi_psi.
  Qed.
  Next Obligation.
    rewrite <- H.
    rewrite <- (catCf1 (f:=((psi adj) (Id G d) \o fmap F f'))).
    rewrite <- psi_naturality.
    rewrite fn1, !catCf1.
    now rewrite iso_psi_phi.
  Qed.

End Adjunction.
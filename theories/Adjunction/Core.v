Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Construction.

Program Definition HomF (C: Category): Functor (Category.op C [x] C) Setoids :=
  Functor.build 
    (fun XY => let (X,Y) := XY in C X Y)
    (fun XY XY' fg => let (f,g) := fg in [ h :-> g \o{C} h \o{C} f]).
Next Obligation.
  intros C [X Y] [X' Y'] [f g]; simpl; intros h h' Heq; simpl in *.
  apply Category.comp_subst_dom, Category.comp_subst_cod, Heq.
Qed.
Next Obligation.
  intros C [X Y] [X' Y'] [f g] [f' g'] [Heqf Heqg] h; simpl in *.
  apply Category.comp_subst; [apply Category.comp_subst_dom, Heqf | apply Heqg].
Qed.
Next Obligation.
  simpl.
  intros C [X1 Y1] [X2 Y2] [X3 Y3] [f1 g1] [f2 g2] h; simpl in *.
  eapply transitivity; [apply Category.comp_assoc |].
  apply Category.comp_subst_dom.
  eapply transitivity; [| apply symmetry, Category.comp_assoc].
  apply Category.comp_subst_dom.
  apply symmetry, Category.comp_assoc.
Qed.
Next Obligation.
  intros C [X Y]; simpl.
  intros h; simpl.
  eapply transitivity; [apply Category.comp_id_cod | apply Category.comp_id_dom].
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

  Definition phiF (C D: Category)(F: Functor C D) :=
    (HomF D \o{Cat} (Prod.functor (Functor.op F) (@Functor.id D))).

  Definition psiF (C D: Category)(G: Functor D C) :=
    (HomF C \o{Cat} (Prod.functor (@Functor.id (Category.op C)) G)).

  Program Definition phi_Natrans
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G)
    : Natrans (phiF F) (psiF G):=
    Natrans.build (phiF F) (psiF G) (fun cd => let (c,d) := cd in phi adj (c:=c)(d:=d)).
  Next Obligation.
    intros C D F G adj [c d] [c' d'] [f g]; simpl in *.
    intros h; simpl.
    apply phi_naturality.
  Qed.

  Program Definition psi_Natrans
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G)
    : Natrans (psiF G) (phiF F):=
    Natrans.build (psiF G) (phiF F) (fun cd => let (c,d) := cd in psi adj (c:=c)(d:=d)).
  Next Obligation.
    intros C D F G adj [c d] [c' d'] [f g]; simpl in *.
    intros h; simpl.
    apply psi_naturality.
  Qed.

  Program Definition eta
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G):
    Natrans (@Functor.id C) (G \o{Cat} F) :=
    Natrans.build (@Functor.id C) (G \o{Cat} F) (fun c: C => phi adj (Id_ D (F c))).
  Next Obligation.
    intros; simpl.

    assert (H: (phi adj) (Id F Y) \o f == fmap G (Id _) \o (phi adj) (Id F Y) \o f).
    {
      eapply transitivity;
      [ apply symmetry, Category.comp_id_cod
      | apply Category.comp_subst_cod, symmetry, Functor.fmap_id].
    }
    eapply transitivity; [apply H |]; clear H.
    eapply symmetry, transitivity; [| apply phi_naturality]; apply symmetry.

    eapply transitivity; [apply Map.substitute, Category.comp_id_cod |].
    eapply transitivity; [apply Map.substitute, Category.comp_id_cod |].

    eapply transitivity; [| apply Category.comp_id_dom].
    eapply transitivity; [| apply symmetry, Category.comp_assoc].
    eapply transitivity; [| apply phi_naturality].
    eapply transitivity; [| apply Map.substitute, Category.comp_subst_dom, symmetry, Category.comp_id_cod].
    eapply transitivity; [| apply Map.substitute, Category.comp_subst_dom, symmetry, Functor.fmap_id].
    eapply transitivity; [| apply Map.substitute, symmetry, Category.comp_id_dom].

    apply reflexivity.
  Qed.

  Program Definition eta_UATo
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G)(c: C)
    : [UA c :=> G ] :=
    UATo.build (eta adj c).
  Next Obligation.
    intros; simpl.
    exists (psi adj f); split.
    - eapply transitivity; [apply symmetry, Category.comp_id_dom |].
      eapply transitivity; [apply Category.comp_assoc |].
      eapply transitivity; [apply symmetry, phi_naturality |].
      eapply transitivity; [apply Map.substitute, Category.comp_subst_dom, Category.comp_id_cod |].
      eapply transitivity; [apply Map.substitute, Category.comp_subst_dom, Functor.fmap_id |].
      eapply transitivity; [apply Map.substitute, Category.comp_id_dom |].
      apply iso_psi_phi.
    - intros g Heq; simpl.
      eapply transitivity; [| apply (iso_phi_psi (spec:=adj))].
      apply Map.substitute.
      eapply transitivity; [apply symmetry, Heq |].
      eapply transitivity; [apply symmetry, Category.comp_id_dom |].
      eapply transitivity; [apply Category.comp_assoc |].
      eapply transitivity; [apply symmetry, phi_naturality |].
      apply Map.substitute.
      eapply transitivity; [apply Category.comp_subst_dom, Category.comp_id_cod |].
      eapply transitivity; [apply Category.comp_subst_dom, Functor.fmap_id | apply Category.comp_id_dom].
  Qed.

  Program Definition epsilon
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G):
    Natrans (F \o{Cat} G) (@Functor.id D)  :=
    Natrans.build (F \o{Cat} G) (@Functor.id D) (fun d: D => psi adj (Id_ C (G d))).
  Next Obligation.
    intros; simpl.

    eapply transitivity; [apply symmetry, Category.comp_id_cod |].
    eapply transitivity; [apply symmetry, psi_naturality |].
    eapply transitivity; [apply Map.substitute, Category.comp_subst_cod, Functor.fmap_id |].
    eapply transitivity; [apply Map.substitute, Category.comp_id_cod |].
    eapply transitivity; [apply Map.substitute, Category.comp_id_cod |].

    eapply transitivity; [| apply Category.comp_id_dom].
    eapply transitivity; [| apply Category.comp_subst_dom, Functor.fmap_id].
    eapply transitivity; [| apply symmetry, Category.comp_assoc].
    eapply transitivity; [| apply psi_naturality].

    apply Map.substitute.
    eapply transitivity; [| apply symmetry, Category.comp_subst_dom, Category.comp_id_dom].
    apply symmetry, Category.comp_id_dom.
  Qed.

  Program Definition epsilon_UAFrom
          (C D: Category)(F: Functor C D)(G: Functor D C)(adj: Adjunction F G)(d: D)
    : [UA d <=: F ] :=
    UAFrom.build (epsilon adj d).
  Next Obligation.
    intros.
    rename d0 into c.
    exists (phi adj f); split; simpl.
    - eapply transitivity; [apply symmetry, Category.comp_id_cod |].
      eapply transitivity; [apply symmetry, psi_naturality |].
      eapply transitivity; [| apply (iso_phi_psi (spec:=adj))].
      apply Map.substitute.
      eapply transitivity; [apply Category.comp_subst_cod, Functor.fmap_id |].
      eapply transitivity; [apply Category.comp_id_cod |].
      apply Category.comp_id_cod.
    - intros g Heq; simpl.
      eapply transitivity; [| apply (iso_psi_phi (spec:=adj))].
      apply Map.substitute.
      eapply transitivity; [apply symmetry, Heq |].
      eapply transitivity; [apply symmetry, Category.comp_id_cod |].
      eapply transitivity; [apply symmetry, psi_naturality |].
      apply Map.substitute.
      eapply transitivity; [apply Category.comp_subst_cod, Functor.fmap_id |].
      eapply transitivity; [apply Category.comp_id_cod |].
      apply Category.comp_id_cod.
  Qed.

End Adjunction.
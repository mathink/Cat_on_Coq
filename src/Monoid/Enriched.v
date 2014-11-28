(* -*- mode: coq -*- *)
(* Time-stamp: <2014/11/28 9:37:17> *)
(*
  Enriched.v
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Generalizable All Variables.

Require Import Category Functor Natrans Monoidal.

Class isEnrichedCategory
      (V: MonoidalCategory)
      (eobj: Type)
      (ehom: eobj -> eobj -> V)
      (ecomp: forall (X Y Z: eobj), V (ehom Y Z [x] ehom X Y) (ehom X Z))
      (eident: forall X: eobj, V (mcI V) (ehom X X)) :=
  {
    ecomp_assoc:
      forall (X Y Z W: eobj),
        ecomp X Y W \o (ecomp Y Z W)[x V](Id (ehom X Y))
        ==
        ecomp X Z W \o (Id (ehom Z W))[x V](ecomp X Y Z) \o mcA V;

    ecomp_unital_l:
      forall (X Y: eobj),
        ecomp X Y Y \o (eident Y)[x V](Id (ehom X Y)) ==
        mc1X V (ehom X Y);

    ecomp_unital_r:
      forall (X Y: eobj),
        ecomp X X Y \o (Id (ehom X Y))[x V](eident X) ==
        mcX1 V (ehom X Y)
    
  }.

Structure EnrichedCategory (V: MonoidalCategory) :=
  {
    eobj:> Type;
    ehom: eobj -> eobj -> V;

    ecomp: forall (X Y Z: eobj), V (ehom Y Z [x] ehom X Y) (ehom X Z);
    eident: forall X: eobj, V (mcI V) (ehom X X);

    prf_EnrichedCategory:> isEnrichedCategory ecomp eident
  }.
Arguments ecomp {V EC X Y Z}: rename.
Arguments eident {V EC}(X): rename.


Definition ECHom `(C: EnrichedCategory V)(X Y: C): Setoid := V (mcI V) (ehom X Y) .

Instance Compose_ECHom `(C: EnrichedCategory V): Compose (@ECHom V C) :=
  {
    compose X Y Z f g := ecomp \o g [x V] f \o mc1XR V (mcI V)
  }.
Proof.
  intros X Y Z f f' Heqf g g' Heqg; simpl.
  assert (g[x V]f == g'[x V]f').
  - apply eq_arg; simpl; split; assumption.
  - rewrite H; reflexivity.
Defined.


Instance Identity_ECHom `(C: EnrichedCategory V): Identity (@ECHom V C) :=
  {
    identity := @eident V C
  }.

Lemma tensor_Iso `(V: MonoidalCategory):
  forall (X Y Z W: V)(f: V X Y)(f': V Y X)(g: V Z W)(g': V W Z),
    Iso f f' -> Iso g g' ->
    Iso (g [x V] f) (g' [x V] f').
Proof.
  do 8 intro; simpl;
  intros [HIsof HIsof'] [HIsog HIsog']; simpl; split;
  rewrite <- tensor_comp; simpl; rewrite <- fmap_ident;
  apply eq_arg; simpl; split; assumption.
Qed.  

Lemma monoidal_coherence_unit_inv `(V: MonoidalCategory):
  forall X Y: V,
    mcA V \o (mcX1R V X [x V] Id Y) == Id X [x V] mc1XR V Y.
Proof.
  intros.
  rewrite <- (identity_cod (mcA V (X:=X)(Y:=mcI V)(Z:=Y))).
  assert
    (Iso (Id X [x V] mc1X V Y) (Id X [x V] mc1XR V Y)).
  {
    simpl; split; rewrite <- tensor_comp, <- fmap_ident;
    apply eq_arg; simpl; split; try apply identity_dom;
    generalize (lam_iso (isMonoidal:=V) Y);
    simpl; intros [H H']; assumption.
  }
  destruct H as [Heq _].
  rewrite <- Heq; clear Heq.
  rewrite compose_assoc.
  rewrite compose_assoc.
  rewrite <- (compose_assoc _ (mcA V) _).
  rewrite <- (monoidal_coherence_unit (isMonoidal:=V)).
  assert
    (Iso (mcX1R V X [x V] Id Y) (mcX1 V X [x V] Id Y)).
  {
    simpl; split; rewrite <- tensor_comp, <- fmap_ident;
    apply eq_arg; simpl; split; try apply identity_cod;
    generalize (raw_iso (isMonoidal:=V) X);
    simpl; intros [H H']; assumption.
  }
  destruct H as [Heq _].
  rewrite Heq; clear Heq.
  apply identity_dom.
Qed.    

Lemma assoc_lam `(V: MonoidalCategory):
  forall X Y: V,
    mc1X V X [x V] Id Y == mc1X V (X [x] Y) \o mcA V.
Proof.
  intros X Y; simpl.
  assert (
      Id (mcI V) [x V] (mc1X V X [x V] Id Y)
      == Id (mcI V) [x V] mc1X V (X [x] Y)
            \o Id (mcI V) [x V] (mcA V)
    ).
  {
    
  }

  
  
(*   generalize (assoc_naturality (V:=V) (Id Y) (Id X) (Id X)); simpl. *)
(*   intro H. *)
(*   rewrite H. *)
  
(* Lemma lam_raw_unit `(V: MonoidalCategory): *)
(*   mc1X V (mcI V) == mcX1 V (mcI V). *)
(* Proof. *)
  

  
Instance EC_IsCategory `(C: EnrichedCategory V)
: isCategory (Compose_ECHom C) (Identity_ECHom C).
Proof.
  split.
  - intros X Y Z W f g h; simpl.
    assert (
        (ecomp \o (h [x V] g) \o mc1XR V (mcI V)) [x V] f
        ==
        (ecomp [x V] Id (ehom X Y))
          \o (((h [x V] g) \o mc1XR V (mcI V)) [x V] f)
      ).
    {
      rewrite <- tensor_comp.
      apply eq_arg; simpl; split;
      [reflexivity | symmetry; apply identity_cod].
    }
    rewrite H; clear H.
    rewrite <- compose_assoc.
    rewrite (ecomp_assoc (isEnrichedCategory := C)).
    rewrite compose_assoc.
    rewrite compose_assoc.

    assert (
        ((h [x V] g) \o (mc1XR V (mcI V))) [x V] f
        ==
        ((h [x V] g) [x V] f) \o (mc1XR V (mcI V) [x V] Id (mcI V))
      ).
    {
      rewrite <- tensor_comp.
      apply eq_arg; simpl; split;
      [reflexivity | symmetry; apply identity_dom].
    }
    rewrite H; clear H.

    rewrite <- (compose_assoc _ _ (mcA V)).
    rewrite <- (compose_assoc _ _ (mcA V)).
    rewrite assoc_naturality.
    rewrite compose_assoc.
    rewrite compose_assoc.
    rewrite <- (compose_assoc _ _ (mcA V)).

    (* need: lam_I == raw_I  *)

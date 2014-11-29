(* -*- mode: coq -*- *)
(*
  MonoidObj.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable All Variables.

Set Universe Polymorphism.

Require Import Category Functor Natrans Monoidal.

Class isMonoid `(V: MonoidalCategory)
      (M: V)(mul: V (mcX V (M,M)) M)(uni: V (mcI V) M) :=
  {
    mon_assoc:
      mul \o (mul [x V] Id M) == mul \o (Id M [x V] mul) \o mcA V;

    mon_unit_l:
      mc1X V M == mul \o (uni [x V] Id M);
    mon_unit_r:
      mcX1 V M == mul \o (Id M [x V] uni)
  }.

Structure Monoid `(V: MonoidalCategory) :=
  {
    mon_obj:> V;
    mon_mul: V (mcX V (mon_obj, mon_obj)) mon_obj;
    mon_uni: V (mcI V) mon_obj;

    prf_Monoid:> isMonoid mon_mul mon_uni
  }.


Require Import Monad.

Section MonoidObjectOfCategoryOfEndofunctor.

  Context (C: Category).

  Definition Endo := C :=> C.

  Let Fobj (FG: Endo [*] Endo): Endo
    := compose_Functor (fst FG) (snd FG).

  Program Definition Comp_fmap: Fmap (Endo [*] Endo) Endo Fobj :=
    fun (FG FG': Endo [*] Endo) => [ ST :-> h_compose_Natrans_dc (fst ST) (snd ST) ].
  Next Obligation.
    revert f f0; intros g1 g2; simpl.
    intros [S1 S2] [T1 T2] [Heq1 Heq2] X; simpl in *.
    rewrite (Heq1 X), (Heq2 (f1 X)).
    reflexivity.
  Qed.

  Instance Comp_IsFunctor: isFunctor Comp_fmap.
  Proof.
    split.
    - intros [F F'] [G G'] [H H'] [S S'] [T T'] X; simpl in *.
      rewrite <- (naturality T').
      rewrite <- compose_assoc, <- (naturality T').
      rewrite <- (compose_assoc (S' (F X))).
      rewrite (fmap_comp G').
      rewrite <- compose_assoc.
      reflexivity.
    - intros [F F']; simpl; intros.
      rewrite identity_dom; apply (fmap_ident F').
  Qed.

  Definition Comp: Functor (Endo [*] Endo) Endo :=
    Build_Functor Comp_IsFunctor.
  
  Program Definition Comp_assoc: Assoc Comp :=
    fun (F G H: Endo) => [: X :=> Id _ :].
  Next Obligation.
    now intros X Y f; simpl; rewrite identity_cod, identity_dom.
  Qed.

  Program Definition Comp_assoc_inv: Assoc_Inv Comp :=
    fun (F G H: Endo) => [: X :=> Id _ :].
  Next Obligation.
    now intros X Y f; simpl; rewrite identity_cod, identity_dom.
  Qed.

  Instance Comp_assoc_isAssoc: isAssoc Comp_assoc Comp_assoc_inv.
  Proof.
    split; simpl; intros.
    - rewrite identity_dom, identity_cod.
      rewrite <- compose_assoc, <- (fmap_comp Z').
      reflexivity.
    - split; intros; apply identity_dom.
  Qed.

  Program Definition Fun_lam: Natrans (BCR Comp (id_Functor C)) (id_Functor Endo) :=
    [: F X :=> Id (F X) :].
  Next Obligation.
    intros X Y f; simpl; rewrite identity_dom; apply identity_cod.
  Qed.  
  Next Obligation.
    intros F G S X; simpl; rewrite identity_dom, identity_cod, (fmap_ident G).
    apply identity_cod.
  Qed.

  Program Definition Fun_lam_inv: Natrans (id_Functor Endo) (BCR Comp (id_Functor C)) :=
    [: F X :=> Id (F X) :].
  Next Obligation.
    intros X Y f; simpl; rewrite identity_dom; apply identity_cod.
  Qed.  
  Next Obligation.
    intros F G S X; simpl; rewrite identity_dom, identity_cod, (fmap_ident G).
    symmetry; apply identity_cod.
  Qed.

  Program Definition Fun_raw: Natrans (BCL Comp (id_Functor C)) (id_Functor Endo) :=
    [: F X :=> Id (F X) :].
  Next Obligation.
    intros X Y f; simpl; rewrite identity_dom; apply identity_cod.
  Qed.  
  Next Obligation.
    intros F G S X; simpl; rewrite identity_dom, identity_cod; reflexivity.
  Qed.

  Program Definition Fun_raw_inv: Natrans (id_Functor Endo) (BCL Comp (id_Functor C)) :=
    [: F X :=> Id (F X) :].
  Next Obligation.
    intros X Y f; simpl; rewrite identity_dom; apply identity_cod.
  Qed.  
  Next Obligation.
    intros F G S X; simpl; rewrite identity_dom, identity_cod.
    symmetry; apply identity_dom.
  Qed.

  Instance Endo_IsMonoidal
  : isMonoidal Comp_assoc Comp_assoc_inv
               Fun_lam Fun_lam_inv Fun_raw Fun_raw_inv.
  Proof.
    split; simpl.
    - now apply Comp_assoc_isAssoc.
    - now intro F; split; intro X; apply identity_dom.
    - now intro F; split; intro X; apply identity_cod.
    - intros F G H I X.
      repeat rewrite (fmap_ident _).
      repeat rewrite identity_dom.
      reflexivity.
    - intros F G X.
      rewrite (fmap_ident _).
      repeat rewrite identity_dom.
      reflexivity.
  Qed.

  Canonical Structure Endo_MC: MonoidalCategory :=
    Build_MonoidalCategory Endo_IsMonoidal.

  Section FromMonoid.
    
    Context (m: Monoid Endo_MC).
    Let Endo_eta: Natrans _ _ := (mon_uni m).
    Let Endo_mu: Natrans _ _ := (mon_mul m).
    
    Instance Monoid_IsMonad: isMonad Endo_eta Endo_mu.
    Proof.
      split; simpl.
      - intro X.
        unfold Endo_eta, Endo_mu.
        generalize (mon_unit_r (isMonoid:=m) X); simpl.
        rewrite (fmap_ident _), identity_cod.
        intro H; symmetry; apply H.
      - intro X.
        unfold Endo_eta, Endo_mu.
        generalize (mon_unit_l (isMonoid:=m) X); simpl.
        rewrite identity_dom.
        intro H; symmetry; apply H.
      - intro X.
        unfold Endo_eta, Endo_mu.
        generalize (mon_assoc (isMonoid:=m) X); simpl.
        do 2 rewrite identity_dom.
        rewrite (fmap_ident _), identity_cod.
        intro H; apply H.
    Qed.

    Definition Monoid_Monad: Monad C := Build_Monad Monoid_IsMonad.

  End FromMonoid.

  Section FromMonad.
    
    Context (m: Monad C).

    Instance Monad_IsMonoid: isMonad (monad_eta m) (monad_mu m ).
    Proof.
      split.
      - intros X.
        rewrite (mu_eta_T (isMonad:=m) X).
        reflexivity.
      - intros X.
        rewrite (mu_T_eta (isMonad:=m) X).
        reflexivity.
      - intros X.
        rewrite (mu_T_mu (isMonad:=m) X).
        reflexivity.
    Qed.

    Definition Monad_Monoid: Monad C :=
      Build_Monad Monad_IsMonoid.

  End FromMonad.

End MonoidObjectOfCategoryOfEndofunctor.

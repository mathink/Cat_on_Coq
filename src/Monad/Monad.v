(* -*- mode: coq -*- *)
(* Time-stamp: <2014/11/20 23:59:19> *)
(*
  Monad.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Require Import Category Functor Natrans.

(** * モナド、クライスリ圏  *)
Generalizable All Variables.

(** ** モナド *)
Class isMonad (C: Category)
      (T: Functor C C)
      (eta: Natrans (Id C) T)
      (mu: Natrans (T \o T) T): Prop :=
  { mu_eta_T:
      forall X: C,
        mu X \o eta (T X) == Id (T X);

    mu_T_eta:
      forall X: C,
        mu X \o fmap T (eta X) == Id (T X);

    mu_T_mu:
      forall X: C,
        mu X \o fmap T (mu X) == mu X \o mu (T X) }.

Structure Monad (C: Category) :=
  { monad_functor:> Functor C C;
    monad_eta: Natrans (Id C) monad_functor;
    monad_mu: Natrans (monad_functor \o monad_functor) monad_functor;

    prf_Monad: isMonad monad_eta monad_mu }.
Existing Instance prf_Monad.


(** ** クライスリ圏  *)
Section KleisliCategory.

  Context `(m: Monad C).
  Notation CK := (fun X Y: C => C X (m Y)).

  Instance KCompose: Compose CK :=
    { compose X Y Z f g := monad_mu m Z \o fmap m g \o (f: C X (m Y)) }.
  Proof.
    now intros X Y Z f f' Heqf g g' Heqg; rewrite Heqf, Heqg.
  Defined.

  Instance KIdentity: Identity CK :=
    { identity := @monad_eta C m }.

  Instance Kleisli_IsCategory: isCategory KCompose KIdentity.
  Proof.
    split; intros; simpl.
    - rewrite <- (compose_assoc _ _ (fmap m h)).
      rewrite <- (naturality (natrans:=monad_mu m)); simpl.
      rewrite compose_assoc.
      rewrite <- (compose_assoc f (fmap m g)).
      rewrite <- fmap_comp. 
      rewrite <- (compose_assoc _ (monad_mu m (m W)) (monad_mu m W)).
      rewrite <- mu_T_mu, compose_assoc.
      rewrite (fmap_comp g); simpl.
      rewrite <- (compose_assoc _ _ (fmap m (monad_mu m W))).
      rewrite <- (compose_assoc (fmap m g)).
      do 2 rewrite <- fmap_comp.
      rewrite compose_assoc.
      reflexivity.
    - rewrite <- (naturality (natrans:=monad_eta m) f).
      rewrite <- compose_assoc.
      rewrite mu_eta_T.
      now rewrite identity_cod; simpl.
    - rewrite <- compose_assoc.
      transitivity ((monad_mu m Y \o (fmap m (monad_eta m Y))) \o f); [reflexivity |].
      now rewrite mu_T_eta, identity_cod.
  Qed.      

  Definition KleisliCatgory: Category :=
    Build_Category Kleisli_IsCategory.
  
End KleisliCategory.


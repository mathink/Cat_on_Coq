(* -*- mode: coq -*- *)
(* Time-stamp: <2014/11/29 16:58:33> *)
(*
  KTMonad.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.


Require Import Category Functor Natrans Monad Kleisli.

Generalizable All Variables.

(** * Equivalence between Monad & Kleisli triple *)
Program Definition bind_Monad `(m: Monad C)
: forall X Y, Map (C X (m Y)) (C (m X) (m Y)) :=
  fun X Y => [ f  :-> monad_mu m Y \o fmap m f].
Next Obligation.
  now intros f f' Heqf; simpl; rewrite Heqf.
Qed.

Program Instance isKTfromMonad `(m: Monad C)
: isKT (monad_eta m) (bind_Monad m).
Next Obligation.
  now rewrite <- mu_T_eta.
Qed.
Next Obligation.
  rewrite compose_assoc, <- (naturality (monad_eta m) (f:=f)); simpl.
  rewrite <- compose_assoc, (mu_eta_T (mu:=monad_mu m) (eta:=monad_eta m) Y).
  now rewrite identity_cod.
Qed.
Next Obligation.
  simpl.
  do 2 rewrite (fmap_comp m); simpl.
  rewrite <-(compose_assoc _ (fmap m _ \o _) _ ).
  rewrite <-(compose_assoc _ (fmap m _) _ ).
  rewrite mu_T_mu.
  rewrite (compose_assoc _ (fmap m _) _), (compose_assoc _ (monad_mu m (m Z))).
  rewrite (naturality (monad_mu m) (f:=g)).
  repeat rewrite compose_assoc.
  reflexivity.
Qed.

Definition KTfromMonad `(m: Monad C): KT C :=
  Build_KT (isKTfromMonad m).


Program Definition fmap_KT `(T: KT C): Fmap C C T :=
  fun X Y => [ f :-> bind T (emb T Y \o f) ].
Next Obligation.
  now intros f f' Heqf; rewrite Heqf.
Qed.

Instance KT_IsFunctor `(T: KT C): isFunctor (fmap_KT T).
Proof.
  split; simpl; intros.
  - rewrite bind_assoc.
    rewrite <-(compose_assoc _ (emb T Y)).
    rewrite emb_bind, compose_assoc.
    reflexivity.
  - now rewrite identity_dom, bind_emb.
Qed.

Definition KT_F `(T: KT C): Functor C C :=
  Build_Functor (KT_IsFunctor T).

Program Definition KTeta `(T: KT C): Natrans (Id C) (KT_F T) := [: X :=> emb T X :].
Next Obligation.
  intros X Y f; simpl.
  now rewrite emb_bind.
Qed.

Program Definition KTmu `(T: KT C): Natrans (KT_F T \o KT_F T) (KT_F T) :=
  [: X :=> bind T (Id (T X)) :].
Next Obligation.
  intros X Y f; simpl.
  now rewrite bind_assoc, <- compose_assoc, emb_bind, identity_cod, bind_assoc, identity_dom.
Qed.  

Instance isMonadfromKT `(T: KT C): isMonad (KTeta T) (KTmu T).
Proof.
  split; simpl; intros.
  - now rewrite emb_bind.
  - now rewrite bind_assoc, <-compose_assoc, emb_bind, identity_cod, bind_emb.
  - now rewrite bind_assoc, <- compose_assoc, emb_bind, bind_assoc, identity_cod, identity_dom.
Qed.

Definition MonadfromKT `(T: KT C): Monad C := Build_Monad (isMonadfromKT T).

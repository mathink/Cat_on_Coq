(* -*- mode: coq -*- *)
(* Time-stamp: <2014/9/23 15:21:37> *)
(*
  Yoneda.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Generalizable All Variables.

Require Import Category Functor Natrans.

(** * Yoneda's Lemma

    Nat(C(X,-), F) == F X

    *)

(** ** Evaluation Functor *)
Section EF.
  Context (B C: Category).
  Let P := (C :=> B) [*] C.

  Program Definition fmap_EvalFunctor
  : Fmap P B (fun FX: (C :=> B) [*] C => fst FX (snd FX)) :=
    fun (FX GY: (C :=> B) [*] C) =>
      [ Sf :-> fmap (fst GY) (snd Sf) \o natrans (fst Sf) (snd FX) ].
  Next Obligation.
    revert f0 o0 f o; intros F X F' X'; simpl.
    intros [S f] [T g]; simpl; intros [HeqST Heqfg].
    now rewrite (HeqST X), Heqfg.
  Qed.

  Instance Eval_IsFunctor: isFunctor fmap_EvalFunctor.
  Proof.
    split.
    - intros [F X] [G Y] [H Z] [S f] [T g]; simpl in *.
      repeat rewrite <- compose_assoc.
      repeat rewrite <- naturality.
      repeat rewrite compose_assoc.
      repeat rewrite naturality.
      rewrite fmap_comp.
      repeat rewrite compose_assoc.
      reflexivity.
    - intros [F X]; simpl.
      now rewrite fmap_ident, identity_cod.
  Qed.


  Definition EvalFunctor: Functor ((C :=> B) [*] C) B :=
    Build_Functor Eval_IsFunctor.

End EF.

(** ** Natrans to Setoids  *)
Section NF.
  Context (C: Category).
  

  Definition fobj_NFunctor (FX: (C :=> Setoids) [*] C): Setoids :=
    (C :=> Setoids) Hom(snd FX,-) (fst FX).
  
  Program Definition fmap_NF_natrans
          (FX GY: (C :=> Setoids) [*] C) (* F G: Functor C Setoids, X Y: C *)
          (Sf: ((C :=> Setoids) [*] C) FX GY) (* S: Natrans F G, f: C X Y *)
          (alpha: fobj_NFunctor FX) (* alpha Y: Setoids (C X Y) FY *)
  : Natrans Hom(snd GY,-) (fst GY) :=
    [: X :=> fst Sf X \o alpha X \o fmap Hom(-,X) (snd Sf) :].
  Next Obligation.
    revert f0 o0 f o n c alpha; simpl; intros F X G Y S f T Z W h g; simpl.
    generalize (@naturality C Setoids F G S _ _ _ h ((T Z) (g \o f))); simpl;
    intro H; rewrite <- H; clear H.
    generalize (@naturality C Setoids _ _ T _ _ _ h (g \o f)); simpl;
    intro H; rewrite <- H; clear H.
    now rewrite compose_assoc.
  Qed.    

  Program Definition fmap_NFunctor
  : Fmap ((C :=> Setoids) [*] C) Setoids fobj_NFunctor :=
    fun FX GY =>
      [Sf alpha :-> fmap_NF_natrans Sf alpha ].
  Next Obligation.
    revert f0 o0 f o n c; simpl; intros F X G Y S f T T' HeqT Z h; simpl.
    now rewrite (HeqT Z).
  Qed.
  Next Obligation.
    revert f0 o0 f o; simpl; intros F X G Y Sf Sf' [HeqS Heqf] T Z h; simpl.
    now rewrite <- (HeqS Z ((T Z) (h \o snd Sf'))), <- Heqf.
  Qed.    

  Instance NF_IsFunctor: isFunctor fmap_NFunctor.
  Proof.
    split.
    - intros [F X] [G Y] [H Z] [S f] [T g]; simpl in *.
      now intros Mu W h; rewrite compose_assoc.
    - now intros [F X]; simpl; intros Mu Y f; rewrite identity_dom.
  Qed.

  Definition NFunctor: Functor ((C :=> Setoids) [*] C) Setoids :=
    Build_Functor NF_IsFunctor.

End NF.


(** ** Yoneda's Lemma *)
Section Yoneda.

  Context {C: Category}.

  Section IsoOnSetoids.

    Context (F: Functor C Setoids)(X: C).

    (** ** Nat(C(X,-), F) -> F X *)
    Program Definition yoneda
    : Map (NFunctor C (F,X)) (EvalFunctor Setoids C (F,X)) :=
      [ alpha :-> alpha X (Id X) ].
    Next Obligation.
      now intros S S' Heq; rewrite (Heq _ _).
    Qed.

    (** ** F X -> Nat(C(X,-), F) *)
    Program Definition inv_yoneda
    : Map (EvalFunctor Setoids C (F,X)) (NFunctor C (F,X)) :=
      [ x :-> [: Y :=> [ f :-> fmap F f x] :] ].
    Next Obligation.
      intros f f' Heqf; simpl.
      assert (fmap F f == fmap F f') by now rewrite Heqf.
      now apply H.
    Qed.
    Next Obligation.
      intros Y Z g f; simpl in *.
      assert (fmap F (g \o f) == fmap F g \o fmap F f) by now rewrite fmap_comp.
      now apply H.
    Qed.    
    Next Obligation.
      intros x y Heq Y f; simpl in *.
      now rewrite Heq.
    Qed.    


    Lemma yoneda_lemma_aux:
      Iso (C:=Setoids) yoneda inv_yoneda.
    Proof.
      split; simpl.
      - intros N Y f; simpl.
        transitivity ((fmap F f \o N X) (Id X)); [now auto |].
        rewrite <- (naturality (natrans:=N) f (Id X)); simpl.
        now simpl; rewrite identity_dom.
      - intros; simpl.
        assert (fmap F (Id X) == Id (F X)) by now rewrite fmap_ident.
        now apply H.
    Qed.

    (** ** Nat(C(X,-), F) == F X *)
    Lemma yoneda_lemma:
      iso (C:=Setoids) (NFunctor C (F,X)) (EvalFunctor Setoids C (F,X)).
    Proof.
      now unfold iso; exists yoneda, inv_yoneda; apply yoneda_lemma_aux.
    Qed.

  End IsoOnSetoids.

  
  Program Definition yoneda_Natrans
  : Natrans (NFunctor C) (EvalFunctor Setoids C) :=
    [: FX :=> yoneda (fst FX) (snd FX) :].
  Next Obligation.
    intros [F1 X1] [F2 X2] [S f] T; simpl in *.
    rewrite identity_cod.
    transitivity ((fmap F2 f \o (S X1)) (T X1 (Id X1))); [| now idtac].
    rewrite <- (naturality (natrans:=S) f (T X1 (Id X1))); simpl.
    apply eq_arg.
    transitivity ((fmap F1 f \o (T X1)) (Id X1)); [| now idtac].
    rewrite <- (naturality (natrans:=T) f (Id X1)); simpl.
    now rewrite identity_dom.
  Qed.

  (** ** Nat(C(X,-), F) == F X is natural on F, X *)
  Lemma yoneda_is_natural_isomorphism:
    natural_isomorphism yoneda_Natrans.
  Proof.
    intros [F X]; simpl; exists (inv_yoneda F X); apply yoneda_lemma_aux.
  Qed.

End Yoneda.


Program Definition HomNatrans (C: Category)(Y X: C)(f: (op C) Y X)
: Fun _ _ (HomFunctor (C:=C) Y) (HomFunctor (C:=C) X) :=
  [: Z :=> [ g :-> g \o{C} f ] :].
Next Obligation.
  now intros g g' Heq; rewrite Heq.
Qed.
Next Obligation.
  now intros Z W h g; simpl in *; rewrite compose_assoc.
Qed.

Program Definition CoHomNatrans (C: Category)(X Y: C)(f: C X Y)
: Fun _ _ Hom(-,X) Hom(-,Y) :=
  [: Z :=> [ (g: C Z X) :-> f \o{C} g ] :].
Next Obligation.
  now intros g g' Heq; rewrite Heq.
Qed.
Next Obligation.
  now intros Z W h g; simpl in *; rewrite compose_assoc.
Qed.


(** ** Yoneda Functor  *)
Section YonedaFunctor.

  Context {C: Category}(F: Functor C Setoids).

  Program Definition fmap_yoneda
  : Fmap (op C) (C :=> Setoids) (fun (X: C) => Hom(X,-)) :=
    fun Y X => [ f :-> HomNatrans f ].
  Next Obligation.
    intros f f' Heqf Z g; simpl.
    now rewrite Heqf.
  Qed.

  Instance yoneda_IsFunctor: isFunctor fmap_yoneda.
  Proof.
    split; simpl.
    - now intros X Y Z f g W h; rewrite compose_assoc.
    - now intros X Y f; rewrite <- (identity_dom f) at 2.
  Qed.

  Definition yonedaFunctor: Functor (op C) (C :=> Setoids) :=
    Build_Functor yoneda_IsFunctor.
  
  Lemma yoneda_is_fullyfaithful:
    fullyfaithful yonedaFunctor.
  Proof.
    split.
    - simpl; intros X Y S.
      exists (S X (Id X)); intros Z f.
      generalize (@naturality _ _ _ _ S _ X Z f (Id X)); simpl; intro H.
      now rewrite <- H, identity_dom.
    - simpl; intros Y X f1 f2 Heq.
      rewrite <- (identity_cod f1), <- (identity_cod f2).
      now apply Heq.
  Qed.

  Program Definition fmap_inv_yoneda
  : Fmap C (op C :=> Setoids) (fun X => Hom(-,X)) :=
    fun X Y => [ f :-> CoHomNatrans f ].
  Next Obligation.
    intros f f' Heqf Z g; simpl.
    now rewrite Heqf.
  Qed.

  Instance inv_yoneda_IsFunctor: isFunctor fmap_inv_yoneda.
  Proof.
    split.
    - now intros X Y Z f g ; simpl; intros W e; rewrite compose_assoc.
    - now simpl; intros X Y f; rewrite <- (identity_cod f) at 2.
  Qed.

  Definition inv_yonedaFunctor: Functor C (op C :=> Setoids) :=
    Build_Functor inv_yoneda_IsFunctor.


  Lemma inv_yoneda_is_faithful:
    faithful inv_yonedaFunctor.
  Proof.
    simpl.
    intros X Y f1 f2 Heq.
    rewrite <- (identity_dom f1), <- (identity_dom f2).
    now apply Heq.
  Qed.

End YonedaFunctor.

(* -*- mode: coq -*- *)
(*
  Monoidal.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Generalizable All Variables.

Require Import Category Functor Natrans.

Definition Assoc (C: Category)(Op: Functor (C [*] C) C) :=
  forall X Y Z, C (Op (Op (X, Y), Z)) (Op (X, Op (Y, Z))).

Section BiComp_1.
  Context (C: Category)(F: Functor (C [*] C) C)(Y Z: C).

  Program Definition fmap_BiLeft: Fmap C C (fun X => F (F (X,Y), Z))
  := fun X X' =>[ f :->
                    fmap F
                    ((fmap F ((f , Id Y): (C [*] C) (X,Y) (X',Y)), Id Z)
                     : (C [*] C) (F (X,Y), Z) (F (X',Y), Z)) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [| reflexivity].
    apply eq_arg; simpl; split; [assumption | reflexivity].
  Qed.

  Instance BiLeft_IsFunctor: isFunctor fmap_BiLeft.
  Proof.
    split.
    - intros X X' X'' f f'; simpl.
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; simpl; [| symmetry; apply identity_dom].
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; [reflexivity | symmetry; apply identity_dom].
    - intros X; simpl.
      rewrite <- fmap_ident; apply eq_arg; simpl; split; simpl; [| reflexivity].
      rewrite <- fmap_ident; apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BiLeft: Functor C C := Build_Functor BiLeft_IsFunctor.

  
  Program Definition fmap_BiRight: Fmap C C (fun X => F (X, F (Y, Z)))
    := fun X X' =>[ f :->
                      fmap F
                      ((f, fmap F ((Id Y, Id Z): (C [*] C) (Y, Z) (Y, Z)))
                       : (C [*] C) (X, F (Y, Z)) (X', F (Y, Z))) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [assumption | reflexivity].
  Qed.

  Instance BiRight_IsFunctor: isFunctor fmap_BiRight.
  Proof.
    split.
    - intros X X' X'' f f'; simpl.
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; [reflexivity |].
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      now apply eq_arg; simpl; split; symmetry; apply identity_dom.
    - intros X; simpl.
      rewrite <- fmap_ident; apply eq_arg; simpl; split; simpl; [reflexivity |].
      rewrite <- fmap_ident; apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BiRight: Functor C C := Build_Functor BiRight_IsFunctor.

End BiComp_1.
  
Class isMonoidal
      (C: Category)
      (Tensor: Functor (C [*] C) C)
      (Unit: C)
      (assoc: Assoc Tensor)
      (lam: forall X: C, C (Tensor (Unit, X)) X)
      (raw: forall X: C, C (Tensor (X, Unit)) X) :=
  {
    assoc_naturality_1:
      forall Y Z: C,
        isNatrans (F:=BiLeft Tensor Y Z) (G:=BiRight Tensor Y Z)
                  (fun X => assoc X Y Z)
  }.
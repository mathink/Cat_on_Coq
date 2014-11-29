(* -*- mode: coq -*- *)
(* Time-stamp: <2014/11/29 12:46:47> *)
(*
  Functor.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Category.

Set Universe Polymorphism.

(** * 函手：圏の間のモルフィズム  *)
(** 射関数の型を Notation でまとめておく。  *)
Notation Fmap C D Fobj := (forall X Y, Map (C X Y) (D (Fobj X) (Fobj Y))).

Class isFunctor (C D: Category)(fobj: C -> D)(fmap: Fmap C D fobj): Prop :=
  { fmap_comp:
      forall (X Y Z: C)(f: C X Y)(g: C Y Z),
        fmap X Z (g \o f) == (fmap Y Z g) \o (fmap X Y f);
    
    fmap_ident:
      forall X: C,
        fmap X X (Id X) == Id (fobj X) }.
Arguments fmap_comp {C D fobj fmap}(F X Y Z f g): rename.
Arguments fmap_ident {C D fobj fmap}(F X): rename.

Structure Functor (C D: Category) :=
  { fobj: C -> D;
    fmap: Fmap C D fobj;

    prf_Functor:> isFunctor fmap }.
Existing Instance prf_Functor.
Coercion fobj: Functor >-> Funclass.
Arguments fmap {C D}(F){X Y}: rename.

Notation makeFunctor fmap :=
  (@Build_Functor _ _ _ fmap _).

Instance compose_IsFunctor (C D E: Category)
         (F: Functor C D)(G: Functor D E)
: isFunctor (fun (X Y: C) => fmap G \o fmap F).
Proof.
  split; simpl; intros.
  - rewrite (fmap_comp F); rewrite (fmap_comp G); reflexivity.
  - rewrite (fmap_ident F); rewrite (fmap_ident G); reflexivity.
Qed.

Definition compose_Functor (C D E: Category)
           (F: Functor C D)(G: Functor D E): Functor C E :=
  Build_Functor (compose_IsFunctor F G).

Program Definition id_Functor (C: Category): Functor C C :=
  makeFunctor (fun X Y => @id_Map (C X Y)).
Next Obligation.
  now split; simpl; intros.
Qed.


(** *** Equality for Functor *)
(* いわゆる heterogeneous equality ? (要調査) *)
Inductive eq_Hom (C : Category)(X Y: C)(f: C X Y):
  forall (Z W: C), C Z W -> Prop :=
| eq_Hom_def:
    forall (g: C X Y), f == g -> eq_Hom f g.
Infix "==_H" := eq_Hom (at level 70).

Lemma eq_Hom_refl:
  forall (C: Category)(df cf: C)(bf: C df cf),
    bf ==_H bf.
Proof.
  intros C df cf bf; apply eq_Hom_def; reflexivity.
Qed.

Lemma eq_Hom_symm:
  forall (C: Category)
         (df cf: C)(bf: C df cf)
         (dg cg: C)(bg: C dg cg),
    bf ==_H bg -> bg ==_H bf.
Proof.
  intros C df cf bf dg cg bg [g Heq].
  apply eq_Hom_def; apply symmetry; assumption.
Qed.

Lemma eq_Hom_trans:
  forall (C : Category)
         (df cf: C)(bf: C df cf)
         (dg cg: C)(bg: C dg cg)
         (dh ch: C)(bh: C dh ch),
    bf ==_H bg -> bg ==_H bh -> bf ==_H bh.
Proof.
  intros C df cf bf dg cg bg dh ch bh [g Heqg] [h Heqh].
  apply eq_Hom_def.
  rewrite Heqg; assumption.
Qed.

Inductive arrow (C: Category) :=
| arrow_triple (dom cod: C)(body: C dom cod).

Definition eq_arrow {C: Category}: relation (arrow C) :=
  fun (f g: arrow C) =>
    let (_,_,bf) := f in
    let (_,_,bg) := g in
    bf ==_H bg.

Definition equal_Functor {C D: Category}(F G : Functor C D) :=
  forall (X Y: C)(f: C X Y),
    eq_arrow (arrow_triple (fmap F f)) (arrow_triple (fmap G f)).
Arguments equal_Functor {C D} / F G.

Instance equal_Functor_Equiv (C D: Category)
: Equivalence (equal_Functor (C:=C)(D:=D)).
Proof.
  split.
  - intros F X Y f; simpl; now apply eq_Hom_refl.
  - intros F G Heq X Y f; simpl; apply eq_Hom_symm; now apply Heq.
  - intros F G H HeqFG HeqGH X Y f; simpl.
    generalize (HeqGH _ _ f); simpl.
    now apply eq_Hom_trans, HeqFG.
Qed.

Canonical Structure Setoid_Functor (C D: Category): Setoid :=
  Build_Setoid (equal_Functor_Equiv C D).

Notation "(-F->)" := Setoid_Functor.
Notation "C -F-> D" := (Setoid_Functor C D) (at level 60, right associativity).


Instance Compose_Functor: Compose (-F->) :=
  { compose := compose_Functor }.
Proof.
  intros C D E F F' HeqF G G' HeqG X Y f; simpl.
  destruct (HeqF X Y f); simpl.
  eapply eq_Hom_trans.
  - apply eq_Hom_def.
    rewrite H; reflexivity.
  - destruct (HeqG _ _ g); simpl.
    apply eq_Hom_def; assumption.
Defined.


Instance Identity_Functor: Identity (-F->) :=
  { identity := id_Functor }.

(** ** Attributes of Functor  *)
Section FunctorAttributes.

  Context {C D: Category}(F: Functor C D).

  Definition full :=
    forall (X Y: C)(g: D (F X) (F Y)),
      exists f: C X Y, fmap F f == g.

  Definition faithful :=
    forall (X Y: C)(f1 f2: C X Y),
      fmap F f1 == fmap F f2 -> f1 == f2.
  
  Definition fullyfaithful := full /\ faithful.

End FunctorAttributes.
Arguments full {C D} / F.
Arguments faithful {C D} / F.
Arguments fullyfaithful {C D}/F.


Lemma full_comp (C D E: Category)(F: Functor C D)(G: Functor D E):
  full F -> full G -> full (G \o F).
Proof.
  simpl; intros HF HG X Y g.
  destruct (HG _ _ g) as [f' Heqf'].
  destruct (HF _ _ f') as [f Heqf].
  exists f; rewrite Heqf, Heqf'.
  reflexivity.
Qed.

Lemma faithful_comp (C D E: Category)(F: Functor C D)(G: Functor D E):
  faithful F -> faithful G -> faithful (G \o F).
Proof.
  simpl; intros HF HG X Y f1 f2 Heq.
  apply HG in Heq.
  now apply HF.
Qed.

Lemma full_is_surjective {C D: Category}(F: Functor C D):
  (forall X Y: C, surjective (fmap F (X:=X)(Y:=Y))) <-> full F.
Proof.
  now split; intros H X Y g; apply H.
Qed.

Lemma faithful_is_injective {C D: Category}(F: Functor C D):
  (forall X Y: C, injective (fmap F (X:=X)(Y:=Y))) <-> faithful F.
Proof.
  now split; intros H X Y g; apply H.
Qed.


(** *** Example: Cat  *)
Instance Cat_IsCategory: isCategory Compose_Functor Identity_Functor.
Proof.
  split.
  - now intros X Y Z W f g h x.
  - now intros X Y f x.
  - now intros X Y f x.
Defined.

Definition Cat: Category := Build_Category Cat_IsCategory.

(** ** Hom Functor *)
(** *** covariant functor  *)
Program Definition fmap_HomFunctor (C: Category)(X: C)
: Fmap C Setoids (fun Y => C X Y) :=
  fun Y Z => [ g f :-> g \o f ].
Next Obligation.
  now intros f f' Heq; rewrite Heq.
Qed.  
Next Obligation.
  now intros g g' Heqg f; simpl; rewrite Heqg.
Qed.

Instance Hom_IsFunctor (C: Category)(X: C)
: isFunctor (C:=C) (D:=Setoids) (fmap_HomFunctor X).
Proof.
  split.
  - now simpl; intros Y Z W g h f; rewrite compose_assoc.
  - now simpl; intros Y f; rewrite identity_cod.
Qed.

Definition HomFunctor (C: Category)(X: C): Functor C Setoids :=
  Build_Functor (Hom_IsFunctor X).

(** *** contravariant functor  *)
Program Definition fmap_OpHomFunctor (C: Category)(Y: C)
: Fmap (op C) Setoids (fun X => C X Y) :=
  fun (W X: C) => [ (f: C X W) (g: C W Y) :-> g \o f ].
Next Obligation.
   now intros g g' Heq; rewrite Heq.
Qed.  
Next Obligation.
  now intros f f' Heqf g; simpl; rewrite Heqf.
Qed.

Instance OpHom_IsFunctor (C: Category)(Y: C)
: isFunctor (C:=op C) (D:=Setoids) (fmap_OpHomFunctor Y).
Proof.
  split.
  - now simpl; intros V W X g h f; rewrite compose_assoc.
  - now simpl; intros X f; rewrite <- (identity_dom f) at 2.
Qed.

Definition OpHomFunctor (C: Category)(Y: C): Functor (op C) Setoids :=
  Build_Functor (OpHom_IsFunctor Y).

Notation "'Hom' ( X , - )" := (HomFunctor X).
Notation "'Hom' ( - , Y )" := (OpHomFunctor Y).

(* -*- mode: coq -*- *)
(* Time-stamp: <2014/9/24 1:53:26> *)
(*
  Cone.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Require Import Category Functor.

(** * 極限と余極限  *)
(** ** 錐と余錐 *)
Section Cone.

  (** J :: index category, D :: diagram in C *)
  Context (J C: Category)(D: Functor J C).


  (** *** 底 J への錐 *)
  Class isICone (iapex: C)(igen: forall i: J, C iapex (D i)) :=
    icone_commute:
      forall (i j: J)(u: J i j),
        fmap D u \o igen i == igen j.

  Structure ICone :=
    { iapex:> C;
      igen: forall i: J, C iapex (D i);

      prf_ICone: isICone igen }.
  Global Existing Instance prf_ICone.

  
  Class isICMap (c d: ICone)(f: C c d) :=
    icmap_commute:
      forall i: J,
        igen d i \o f == igen c i.

  Structure ICMap (c d: ICone) :=
    { icmap_body:> C c d;
      
      prf_ICMap: isICMap icmap_body }.
  Global Existing Instance prf_ICMap.
  
  Definition equal_ICMap (c d: ICone)(f g: ICMap c d) := f == g.
  Arguments equal_ICMap c d / f g.
  Instance equal_ICMap_Equiv (c d: ICone): Equivalence (@equal_ICMap c d).
  Proof.
    split; simpl; auto.
    - intro; reflexivity.
    - intros f g H; symmetry; exact H.
    - intros f g h Hfg Hgh; transitivity (g: C c d); [exact Hfg | exact Hgh].
  Qed.
  
  Canonical Structure Setoid_ICMap (c d: ICone) :=
    Build_Setoid (equal_ICMap_Equiv c d).

  Program Definition compose_ICMap (c d e: ICone)(f: ICMap c d)(g: ICMap d e): ICMap c e :=
    {| icmap_body := (g: C d e) \o (f: C c d) |}.
  Next Obligation.
    now intro i; rewrite <- compose_assoc, icmap_commute, icmap_commute.
  Qed.
  Canonical Structure compose_ICMap.

  Program Definition id_ICMap (c: ICone): ICMap c c :=
    {| icmap_body := ident c |}.
  Next Obligation.
    intro i. 
    now rewrite <- (identity_dom (igen c i)) at 2.
  Qed.
  Canonical Structure id_ICMap.

  Instance Compose_ICMap: Compose Setoid_ICMap :=
    { compose X Y Z f g := compose_ICMap f g }.
  Proof.
    now simpl; intros X Y Z f f' Heqf g g' Heqg; simpl; rewrite Heqf, Heqg.
  Defined.

  Program Instance Identity_ICMap: Identity Setoid_ICMap :=
    { identity X := id_ICMap X }.

  (** 錐の圏 *)
  Instance IC_IsCategory: isCategory Compose_ICMap Identity_ICMap.
  Proof.
    split; simpl; intros.
    - now rewrite compose_assoc.
    - now rewrite <- (identity_dom (f: C X Y)) at 2.
    - now rewrite <- (identity_cod (f: C X Y)) at 2.
  Qed.

  Definition ICone_Cat: Category := Build_Category IC_IsCategory.
  Canonical Structure ICone_Cat.

  (** 極限とは錐の圏の終対象である。  *)
  Definition Limit := Terminal ICone_Cat.


  (** *** 底 J からの錐(余錐) *)
  Class isFCone (fapex: C)(fgen: forall i: J, C (D i) fapex) :=
    fcone_commute:
      forall (i j: J)(u: J i j),
        fgen j \o fmap D u == fgen i.

  Structure FCone :=
    { fapex:> C;
      fgen: forall i: J, C (D i) fapex;

      prf_FCone: isFCone fgen }.
  Global Existing Instance prf_FCone.

  Class isFCMap (c d: FCone)(f: C c d) :=
    fcmap_commute:
      forall i: J,
        f \o fgen c i == fgen d i.

  Structure FCMap (c d: FCone) :=
    { fcmap_body:> C c d;
      
      prf_FCMap: isFCMap fcmap_body }.
  Global Existing Instance prf_FCMap.
  
  Definition equal_FCMap (c d: FCone)(f g: FCMap c d) := f == g.
  Arguments equal_FCMap c d / f g.
  Instance equal_FCMap_Equiv (c d: FCone): Equivalence (@equal_FCMap c d).
  Proof.
    split; simpl; auto.
    - intro; reflexivity.
    - intros f g H; symmetry; exact H.
    - intros f g h Hfg Hgh; transitivity (g: C c d); [exact Hfg | exact Hgh].
  Qed.
  
  Canonical Structure Setoid_FCMap (c d: FCone) :=
    Build_Setoid (equal_FCMap_Equiv c d).

  Program Definition compose_FCMap (c d e: FCone)(f: FCMap c d)(g: FCMap d e): FCMap c e :=
    {| fcmap_body := (g: C d e) \o (f: C c d) |}.
  Next Obligation.
    now intro i; rewrite compose_assoc, fcmap_commute, fcmap_commute.
  Qed.
  Canonical Structure compose_FCMap.

  Program Definition id_FCMap (c: FCone): FCMap c c :=
    {| fcmap_body := ident c |}.
  Next Obligation.
    intro i. 
    now rewrite <- (identity_cod (fgen c i)) at 2.
  Qed.
  Canonical Structure id_FCMap.

  Instance Compose_FCMap: Compose Setoid_FCMap :=
    { compose X Y Z f g := compose_FCMap f g }.
  Proof.
    now simpl; intros X Y Z f f' Heqf g g' Heqg; simpl; rewrite Heqf, Heqg.
  Defined.

  Program Instance Identity_FCMap: Identity Setoid_FCMap :=
    { identity X := id_FCMap X }.

  Instance FC_IsCategory: isCategory Compose_FCMap Identity_FCMap.
  Proof.
    split; simpl; intros.
    - now rewrite compose_assoc.
    - now rewrite <- (identity_dom (f: C X Y)) at 2.
    - now rewrite <- (identity_cod (f: C X Y)) at 2.
  Qed.

  Definition FCone_Cat: Category := Build_Category FC_IsCategory.
  Canonical Structure FCone_Cat.

  (** 余極限とは余錐の圏の始対象である。  *)
  Definition CoLimit := Initial FCone_Cat.

End Cone.

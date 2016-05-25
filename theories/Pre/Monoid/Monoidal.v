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


Definition BiFunctor (C1 C2 D: Category) := Functor (C1 [*] C2) D.
Notation biFmap F f1 f2 := (fmap F (f1 [*_,_] f2)).

Section BiComp_1.
  (* (-xY)xZ : C -> C *)
  (* -x(YxZ) : C -> C *)
  Context (C: Category)(F: Functor (C [*] C) C)(Y Z: C).

  Program Definition fmap_BC1d: Fmap C C (fun X => F (F (X,Y), Z))
  := fun X X' =>[ f :-> biFmap F (biFmap F f (Id Y)) (Id Z) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [| reflexivity].
    apply eq_arg; simpl; split; [assumption | reflexivity].
  Qed.

  Instance BC1d_IsFunctor: isFunctor fmap_BC1d.
  Proof.
    split.
    - intros X X' X'' f f'; simpl.
      rewrite <- (identity_dom (Id Y)) at 1.
      rewrite <- (fmap_comp F).
      apply eq_arg; simpl; split; simpl; [| symmetry; apply identity_dom].
      rewrite <- (fmap_comp F).
      rewrite identity_dom.
      apply eq_arg; simpl; split; [reflexivity | symmetry; apply identity_dom].
    - intros X; simpl.
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; simpl; [| reflexivity].
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BC1d: Functor C C := Build_Functor BC1d_IsFunctor.

  
  Program Definition fmap_BC1c: Fmap C C (fun X => F (X, F (Y, Z)))
    := fun X X' =>[ f :-> biFmap F f (biFmap F (Id Y) (Id Z)) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [assumption | reflexivity].
  Qed.

  Instance BC1c_IsFunctor: isFunctor fmap_BC1c.
  Proof.
    split.
    - intros X X' X'' f f'; simpl.
      rewrite <- (fmap_comp F).
      apply eq_arg; simpl; split; [reflexivity |].
      rewrite <- (fmap_comp F).
      now apply eq_arg; simpl; split; symmetry; apply identity_dom.
    - intros X; simpl.
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; simpl; [reflexivity |].
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BC1c: Functor C C := Build_Functor BC1c_IsFunctor.

End BiComp_1.

Section BiComp_2.
  (* (Xx-)xZ : C -> C *)
  (* Xx(-xZ) : C -> C *)
  Context (C: Category)(F: Functor (C [*] C) C)(X Z: C).

  Program Definition fmap_BC2d: Fmap C C (fun Y => F (F (X,Y), Z))
  := fun Y Y' =>[ f :-> biFmap F (biFmap F (Id X) f) (Id Z) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [| reflexivity].
    apply eq_arg; simpl; split; [reflexivity | assumption].
  Qed.

  Instance BC2d_IsFunctor: isFunctor fmap_BC2d.
  Proof.
    split.
    - intros Y Y' Y'' f f'; simpl.
      rewrite <- (fmap_comp F).      apply eq_arg; simpl; split; simpl; [| symmetry; apply identity_dom].
      rewrite <- (fmap_comp F).      apply eq_arg; simpl; split; [symmetry; apply identity_dom | reflexivity].
    - intros Y; simpl.
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; simpl; [| reflexivity].
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BC2d: Functor C C := Build_Functor BC2d_IsFunctor.

  
  Program Definition fmap_BC2c: Fmap C C (fun Y => F (X, F (Y, Z)))
    := fun Y Y' =>[ f :-> biFmap F (Id X) (biFmap F f (Id Z)) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [reflexivity |].
    apply eq_arg; simpl; split; [assumption | reflexivity].
  Qed.

  Instance BC2c_IsFunctor: isFunctor fmap_BC2c.
  Proof.
    split.
    - intros Y Y' Y'' f f'; simpl.
      rewrite <- (fmap_comp F).      apply eq_arg; simpl; split; [symmetry; apply identity_dom |].
      rewrite <- (fmap_comp F).      apply eq_arg; simpl; split; [reflexivity | symmetry; apply identity_dom].
    - intros Y; simpl.
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; simpl; [reflexivity |].
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BC2c: Functor C C := Build_Functor BC2c_IsFunctor.

End BiComp_2.

Section BiComp_3.
  (* (XxY)x- : C -> C *)
  (* Xx(Yx-) : C -> C *)
  Context (C: Category)(F: Functor (C [*] C) C)(X Y: C).

  Program Definition fmap_BC3d: Fmap C C (fun Z => F (F (X, Y), Z))
  := fun Z Z' =>[ f :-> biFmap F (biFmap F (Id X) (Id Y)) f ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [reflexivity | assumption].
  Qed.

  Instance BC3d_IsFunctor: isFunctor fmap_BC3d.
  Proof.
    split.
    - intros Z Z' Z'' f f'; simpl.
      rewrite <- (fmap_comp F); apply eq_arg; simpl; split; simpl; [| reflexivity]. 
      rewrite <- (fmap_comp F); apply eq_arg; simpl; split; simpl; symmetry; apply identity_dom.
    - intros Z; simpl.
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; simpl; [| reflexivity].
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BC3d: Functor C C := Build_Functor BC3d_IsFunctor.
  
  Program Definition fmap_BC3c: Fmap C C (fun Z => F (X, F (Y, Z)))
    := fun Z Z' =>[ f :-> biFmap F (Id X) (biFmap F (Id Y) f) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [reflexivity |].
    apply eq_arg; simpl; split; [reflexivity | assumption].
  Qed.

  Instance BC3c_IsFunctor: isFunctor fmap_BC3c.
  Proof.
    split.
    - intros Z Z' Z'' f f'; simpl.
      rewrite <- (fmap_comp F); apply eq_arg; simpl; split; [symmetry; apply identity_dom |].
      rewrite <- (fmap_comp F); apply eq_arg; simpl; split; [symmetry; apply identity_dom| reflexivity].
    - intros Z; simpl.
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; simpl; [reflexivity |].
      rewrite <- (fmap_ident F); apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BC3c: Functor C C := Build_Functor BC3c_IsFunctor.

End BiComp_3.

Definition Assoc (C: Category)(Op: Functor (C [*] C) C) :=
  forall X Y Z, C (Op (Op (X, Y), Z)) (Op (X, Op (Y, Z))).

Definition Assoc_Inv (C: Category)(Op: Functor (C [*] C) C) :=
  forall X Y Z, C (Op (X, Op (Y, Z))) (Op (Op (X, Y), Z)).

Class isAssoc
      (C: Category)
      (Tensor: Functor (C [*] C) C)
      (assoc: Assoc Tensor)
      (assoc_inv: Assoc_Inv Tensor):=
  {
    assoc_naturality:
      forall (X X' Y Y' Z Z': C)(f: C X X')(g: C Y Y')(h: C Z Z'),
        assoc X' Y' Z' \o biFmap Tensor (biFmap Tensor f g) h
        == biFmap Tensor f (biFmap Tensor g h) \o assoc X Y Z;

    assoc_iso:
      forall (X Y Z: C),
        Iso (assoc X Y Z) (assoc_inv X Y Z)
  }.

    (** naturality of [assoc] 
    assoc_naturality_1:
      forall Y Z: C,
        isNatrans (F:=BC1d Tensor Y Z) (G:=BC1c Tensor Y Z)
                  (fun X => assoc X Y Z);
    assoc_1 (Y Z: C): Natrans (BC1d Tensor Y Z) (BC1c Tensor Y Z) :=
      Build_Natrans (assoc_naturality_1 Y Z);
    assoc_isomorphic_1:
      forall Y Z, natural_isomorphism (assoc_1 Y Z);
    
    assoc_naturality_2:
      forall X Z: C,
        isNatrans (F:=BC2d Tensor X Z) (G:=BC2c Tensor X Z)
                  (fun Y => assoc X Y Z);
    assoc_2 (X Z: C): Natrans (BC2d Tensor X Z) (BC2c Tensor X Z) :=
      Build_Natrans (assoc_naturality_2 X Z);
    assoc_isomorphic_2:
      forall X Z, natural_isomorphism (assoc_2 X Z);

    assoc_naturality_3:
      forall X Y: C,
        isNatrans (F:=BC3d Tensor X Y) (G:=BC3c Tensor X Y)
                  (fun Z => assoc X Y Z);
    assoc_3 (X Y: C): Natrans (BC3d Tensor X Y) (BC3c Tensor X Y) :=
      Build_Natrans (assoc_naturality_3 X Y);
    assoc_isomorphic_3:
      forall X Y, natural_isomorphism (assoc_3 X Y)
     *)


Program Definition fmap_BCL (C: Category)(F: Functor (C [*] C) C)(Y: C)
: Fmap C C (fun X => F (X,Y)) :=
  fun X X' => [ f :-> fmap F ((f, Id Y): (C [*] C) (X, Y) (X', Y))].
Next Obligation.
  intros f f' Heqf.
  apply eq_arg; simpl; split; [assumption | reflexivity].
Qed.

Instance BCL_IsFunctor (C: Category)(F: Functor (C [*] C) C)(Y: C)
: isFunctor (fmap_BCL F Y).
Proof.
  split.
  - intros X X' X'' f f'; simpl.
    rewrite <- (fmap_comp F).
    apply eq_arg; simpl; split; [reflexivity | symmetry; apply identity_dom].
  - intro X; simpl.
    rewrite <- (fmap_ident F); simpl.
    apply eq_arg; simpl; split; reflexivity.
Qed.

Definition BCL `(F: Functor (C [*] C) C)(Y: C) := Build_Functor (BCL_IsFunctor F Y).

Program Definition fmap_BCR (C: Category)(F: Functor (C [*] C) C)(X: C)
: Fmap C C (fun Y => F (X,Y)) :=
  fun Y Y' => [ f :-> fmap F ((Id X, f): (C [*] C) (X, Y) (X, Y'))].
Next Obligation.
  intros f f' Heqf.
  apply eq_arg; simpl; split; [reflexivity | assumption].
Qed.

Instance BCR_IsFunctor (C: Category)(F: Functor (C [*] C) C)(X: C)
: isFunctor (fmap_BCR F X).
Proof.
  split.
  - intros Y Y' Y'' f f'; simpl.
    rewrite <- (fmap_comp F); simpl.
    apply eq_arg; simpl; split; [symmetry; apply identity_dom | reflexivity].
  - intro Y; simpl.
    rewrite <- (fmap_ident F); simpl.
    apply eq_arg; simpl; split; reflexivity.
Qed.

Definition BCR `(F: Functor (C [*] C) C)(X: C) := Build_Functor (BCR_IsFunctor F X).

Class isMonoidal
      `(Tensor: Functor (C [*] C) C)
      (assoc: Assoc Tensor)
      (assoc_inv: Assoc_Inv Tensor)
      (Unit: C)
      (lam: Natrans (BCR Tensor Unit) (Identity_Functor C))
      (lam_inv: Natrans (Identity_Functor C) (BCR Tensor Unit))
      (raw: Natrans (BCL Tensor Unit) (Identity_Functor C))
      (raw_inv: Natrans (Identity_Functor C) (BCL Tensor Unit)) :=
  {
    assoc_associative: isAssoc assoc assoc_inv;
    lam_iso: forall X, Iso (lam X) (lam_inv X);
    raw_iso: forall X, Iso (raw X) (raw_inv X);

    (** coherence condition  *)
    monoidal_coherence_assoc:
      forall (X Y Z W: C),
        assoc X Y (Tensor (Z, W)) \o assoc (Tensor (X, Y)) Z W ==
        biFmap Tensor (Id X) (assoc Y Z W)
             \o assoc X (Tensor (Y, Z)) W
             \o biFmap Tensor (assoc X Y Z) (Id W);

    monoidal_coherence_unit:
      forall X Y: C,
        biFmap Tensor (raw X) (Id Y) ==
        biFmap Tensor (Id X) (lam Y) \o assoc X Unit Y
  }.
Existing Instance assoc_associative.
Coercion assoc_associative: isMonoidal >-> isAssoc.

Structure MonoidalCategory :=
  {
    mcCat:> Category;
    mcX: Functor (mcCat [*] mcCat) mcCat;
    mcA: Assoc mcX;
    mcAR: Assoc_Inv mcX;
    mcI: mcCat;
    mc1X: Natrans (BCR mcX mcI) (Identity_Functor mcCat);
    mc1XR: Natrans (Identity_Functor mcCat) (BCR mcX mcI);
    mcX1: Natrans (BCL mcX mcI) (Identity_Functor mcCat);
    mcX1R: Natrans (Identity_Functor mcCat) (BCL mcX mcI);
    prf_MonoidalCategory:> isMonoidal mcA mcAR mc1X mc1XR mcX1 mcX1R
  }.
Notation "X [x] Y" := (mcX _ (X,Y)) (at level 55, right associativity).
Notation "g [ 'x' V ] f" := (fmap (mcX V) ((g, f): (V [*] V) (_,_) (_,_))) (at level 55, right associativity).

Arguments mcA (V){X Y Z}: rename.

Lemma tensor_comp_id `(V: MonoidalCategory):
  forall (X X' Y Y': V)(f: V X X')(g: V Y Y'),
    g [x V] f == (g [x V] (Id X')) \o ((Id Y) [x V] f).
Proof.
  intros; simpl.
  rewrite <- (fmap_comp (mcX V)).
  apply eq_arg; simpl; split; symmetry;
  [apply identity_dom | apply identity_cod].
Qed.


Lemma tensor_comp_l `(V: MonoidalCategory):
  forall (X Y Z X': V)(f: V X Y)(g: V Y Z),
    (g \o f) [x V] Id X' == g [x V] Id X' \o f [x V] Id X'.
Proof.
  intros; simpl.
  rewrite <- (fmap_comp (mcX V)).
  apply eq_arg; simpl; split;
  [reflexivity | symmetry; apply identity_cod].
Qed.

Lemma tensor_comp `(V: MonoidalCategory):
  forall (X Y Z X' Y' Z': V)(f: V X Y)(g: V Y Z)
         (f': V X' Y')(g': V Y' Z'),
    (g \o f) [x V] (g' \o f') == g [x V] g' \o f [x V] f'.
Proof.
  intros; simpl.
  rewrite <- (fmap_comp (mcX V)).
  apply eq_arg; simpl; split; reflexivity.
Qed.

(*
Lemma assoc_naturality `(V: MonoidalCategory):
  forall (X X' Y Y' Z Z': V)(f: V X X')(g: V Y Y')(h: V Z Z'),
    mcA V \o (h [x V] g) [x V] f == h [x V] (g [x V] f) \o mcA V.
Proof.
  intros; simpl.
  rewrite (tensor_comp_id f (h[x V]g)); simpl.
  assert
    ((h [x V] g)[x V]Id X'
     == (h [x V] (Id Y') \o (Id Z) [x V] g) [x V] Id X')
    by 
      (apply eq_arg; split; simpl;
       [apply (tensor_comp_id g h) | reflexivity]).
  rewrite H; clear H; simpl.

  rewrite <- (compose_assoc _ _ (mcA V)); simpl.
  rewrite (tensor_comp_l X' (Id Z [x V] g)(h [x V] Id Y')).
  rewrite <- compose_assoc.
  generalize
    (naturality (assoc_1 (isAssoc:=V) Y' X') (f:=h)); simpl; intro H.
  rewrite H; clear H.
  rewrite compose_assoc.
  rewrite <- (fmap_comp (mcX V)); simpl.
  rewrite compose_assoc.
  rewrite (tensor_comp (Id (Z [x] Y)) (Id Z [x V] g)  f (Id X')).

  rewrite <- (compose_assoc _ _ (mcA V)).
  generalize
    (naturality (assoc_2 (isAssoc:=V) Z X') (f:=g)); simpl; intro H.
  rewrite H; clear H.
  rewrite compose_assoc.
  
  generalize
    (naturality (assoc_3 (isAssoc:=V) Z Y) (f:=f)); simpl; intro H.
  assert
    ((Id Z [x V] Id Y)[x V] f
     ==
     Id (Z [x] Y) [x V] f)
    by (apply eq_arg; simpl; split;
        [rewrite <- (fmap_ident (mcX V)) |]; reflexivity).
  rewrite H0 in H; clear H0.
  rewrite H; clear H.
  rewrite <- compose_assoc.
  rewrite <- compose_assoc.
  rewrite <- tensor_comp.
  rewrite <- tensor_comp.

  rewrite identity_dom.
  rewrite identity_dom.

  apply compose_Proper; [reflexivity |].
  apply eq_arg; simpl; split; [reflexivity |].

  rewrite <- tensor_comp.
  rewrite <- tensor_comp.
  apply eq_arg; simpl; split; rewrite identity_dom, identity_cod; reflexivity.

Qed.
 *)

Class isSymmetricMonoidal (V: MonoidalCategory)
      (comm: forall X Y: V, V (X [x] Y) (Y [x] X)) :=
  {
    comm_IsNatrans_l:
      forall Y: V, isNatrans (F:=BCL (mcX V) Y) (G:=BCR (mcX V) Y) (fun X => comm X Y);
    comm_natrans_l (Y: V): Natrans (BCL (mcX V) Y) (BCR (mcX V) Y) :=
      Build_Natrans (comm_IsNatrans_l Y);
    comm_IsNatrans_r:
      forall X: V, isNatrans (F:=BCR (mcX V) X) (G:=BCL (mcX V) X) (fun Y => comm X Y);
    comm_natrans_r (X: V): Natrans (BCR (mcX V) X) (BCL (mcX V) X) :=
      Build_Natrans (comm_IsNatrans_r X);

    (* coherence condition *)

    symm_monoidal_coherence_comm_assoc:
      forall (X Y Z: V),
        mcA V \o comm X (Y [x] Z) \o mcA V ==
        (Id Y) [x V] (comm X Z)
             \o mcA V \o (comm X Y) [x V] (Id Z);

    symm_monoidal_coherence_comm_ident:
      forall (X Y: V),
        comm Y X \o comm X Y == Id (X [x] Y)
  }.

Structure SymMonoidalCategory :=
  {
    smcMC:> MonoidalCategory;
    smcC: forall X Y: smcMC, smcMC (X [x] Y) (Y [x] X);

    prf_SymMonoidalCategory:> isSymmetricMonoidal smcC
  }.



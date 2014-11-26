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

Section BiComp_1.
  (* (-xY)xZ : C -> C *)
  (* -x(YxZ) : C -> C *)
  Context (C: Category)(F: Functor (C [*] C) C)(Y Z: C).

  Program Definition fmap_BC1d: Fmap C C (fun X => F (F (X,Y), Z))
  := fun X X' =>[ f :->
                    fmap F
                    ((fmap F ((f , Id Y): (C [*] C) (X,Y) (X',Y)), Id Z)
                     : (C [*] C) (F (X,Y), Z) (F (X',Y), Z)) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [| reflexivity].
    apply eq_arg; simpl; split; [assumption | reflexivity].
  Qed.

  Instance BC1d_IsFunctor: isFunctor fmap_BC1d.
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

  Definition BC1d: Functor C C := Build_Functor BC1d_IsFunctor.

  
  Program Definition fmap_BC1c: Fmap C C (fun X => F (X, F (Y, Z)))
    := fun X X' =>[ f :->
                      fmap F
                      ((f, fmap F ((Id Y, Id Z): (C [*] C) (Y, Z) (Y, Z)))
                       : (C [*] C) (X, F (Y, Z)) (X', F (Y, Z))) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [assumption | reflexivity].
  Qed.

  Instance BC1c_IsFunctor: isFunctor fmap_BC1c.
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

  Definition BC1c: Functor C C := Build_Functor BC1c_IsFunctor.

End BiComp_1.

Section BiComp_2.
  (* (Xx-)xZ : C -> C *)
  (* Xx(-xZ) : C -> C *)
  Context (C: Category)(F: Functor (C [*] C) C)(X Z: C).

  Program Definition fmap_BC2d: Fmap C C (fun Y => F (F (X,Y), Z))
  := fun Y Y' =>[ f :->
                    fmap F
                    ((fmap F ((Id X, f): (C [*] C) (X,Y) (X,Y')), Id Z)
                     : (C [*] C) (F (X,Y), Z) (F (X,Y'), Z)) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [| reflexivity].
    apply eq_arg; simpl; split; [reflexivity | assumption].
  Qed.

  Instance BC2d_IsFunctor: isFunctor fmap_BC2d.
  Proof.
    split.
    - intros Y Y' Y'' f f'; simpl.
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; simpl; [| symmetry; apply identity_dom].
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; [symmetry; apply identity_dom | reflexivity].
    - intros Y; simpl.
      rewrite <- fmap_ident; apply eq_arg; simpl; split; simpl; [| reflexivity].
      rewrite <- fmap_ident; apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BC2d: Functor C C := Build_Functor BC2d_IsFunctor.

  
  Program Definition fmap_BC2c: Fmap C C (fun Y => F (X, F (Y, Z)))
    := fun Y Y' =>[ f :->
                      fmap F
                      ((Id X, fmap F ((f, Id Z): (C [*] C) (Y, Z) (Y', Z)))
                       : (C [*] C) (X, F (Y, Z)) (X, F (Y', Z))) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [reflexivity |].
    apply eq_arg; simpl; split; [assumption | reflexivity].
  Qed.

  Instance BC2c_IsFunctor: isFunctor fmap_BC2c.
  Proof.
    split.
    - intros Y Y' Y'' f f'; simpl.
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; [symmetry; apply identity_dom |].
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; [reflexivity | symmetry; apply identity_dom].
    - intros Y; simpl.
      rewrite <- fmap_ident; apply eq_arg; simpl; split; simpl; [reflexivity |].
      rewrite <- fmap_ident; apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BC2c: Functor C C := Build_Functor BC2c_IsFunctor.

End BiComp_2.

Section BiComp_3.
  (* (XxY)x- : C -> C *)
  (* Xx(Yx-) : C -> C *)
  Context (C: Category)(F: Functor (C [*] C) C)(X Y: C).

  Program Definition fmap_BC3d: Fmap C C (fun Z => F (F (X, Y), Z))
  := fun Z Z' =>[ f :->
                    fmap F
                    ((fmap F ((Id X, Id Y): (C [*] C) (X, Y) (X, Y)), f)
                     : (C [*] C) (F (X, Y), Z) (F (X, Y), Z')) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [reflexivity | assumption].
  Qed.

  Instance BC3d_IsFunctor: isFunctor fmap_BC3d.
  Proof.
    split.
    - intros Z Z' Z'' f f'; simpl.
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; simpl; [| reflexivity]. 
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; simpl; symmetry; apply identity_dom.
    - intros Z; simpl.
      rewrite <- fmap_ident; apply eq_arg; simpl; split; simpl; [| reflexivity].
      rewrite <- fmap_ident; apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BC3d: Functor C C := Build_Functor BC3d_IsFunctor.
  
  Program Definition fmap_BC3c: Fmap C C (fun Z => F (X, F (Y, Z)))
    := fun Z Z' =>[ f :->
                      fmap F
                      ((Id X, fmap F ((Id Y, f): (C [*] C) (Y, Z) (Y, Z')))
                       : (C [*] C) (X, F (Y, Z)) (X, F (Y, Z'))) ].
  Next Obligation.
    intros f f' Heqf.
    apply eq_arg; simpl; split; [reflexivity |].
    apply eq_arg; simpl; split; [reflexivity | assumption].
  Qed.

  Instance BC3c_IsFunctor: isFunctor fmap_BC3c.
  Proof.
    split.
    - intros Z Z' Z'' f f'; simpl.
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; [symmetry; apply identity_dom |].
      rewrite <- (fmap_comp (isFunctor := prf_Functor F)).
      apply eq_arg; simpl; split; [symmetry; apply identity_dom| reflexivity].
    - intros Z; simpl.
      rewrite <- fmap_ident; apply eq_arg; simpl; split; simpl; [reflexivity |].
      rewrite <- fmap_ident; apply eq_arg; simpl; split; reflexivity.
  Qed.

  Definition BC3c: Functor C C := Build_Functor BC3c_IsFunctor.

End BiComp_3.


Definition Assoc (C: Category)(Op: Functor (C [*] C) C) :=
  forall X Y Z, C (Op (Op (X, Y), Z)) (Op (X, Op (Y, Z))).

Class isAssociativeBiFunctor
      (C: Category)
      (Tensor: Functor (C [*] C) C)
      (assoc: Assoc Tensor) :=
  {
    (** naturality of [assoc] *)
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
  }.


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
    rewrite <- (fmap_comp (isFunctor := prf_Functor F)); simpl.
    apply eq_arg; simpl; split; [reflexivity | symmetry; apply identity_dom].
  - intro X; simpl.
    rewrite <- (fmap_ident (isFunctor := prf_Functor F)); simpl.
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
    rewrite <- (fmap_comp (isFunctor := prf_Functor F)); simpl.
    apply eq_arg; simpl; split; [symmetry; apply identity_dom | reflexivity].
  - intro Y; simpl.
    rewrite <- (fmap_ident (isFunctor := prf_Functor F)); simpl.
    apply eq_arg; simpl; split; reflexivity.
Qed.

Definition BCR `(F: Functor (C [*] C) C)(X: C) := Build_Functor (BCR_IsFunctor F X).

Class isMonoidal
      `(Tensor: Functor (C [*] C) C)
      (assoc: Assoc Tensor)
      (Unit: C)
      (lam: Natrans (BCR Tensor Unit) (Identity_Functor C))
      (lam_inv: Natrans (Identity_Functor C) (BCR Tensor Unit))
      (raw: Natrans (BCL Tensor Unit) (Identity_Functor C))
      (raw_inv: Natrans (Identity_Functor C) (BCL Tensor Unit)) :=
  {
    assoc_associative: isAssociativeBiFunctor assoc;
    lam_iso: forall X, Iso (lam X) (lam_inv X);
    raw_iso: forall X, Iso (raw X) (raw_inv X);

    (** coherence condition  *)
    monoidal_coherence_assoc:
      forall (X Y Z W: C),
        assoc X Y (Tensor (Z, W)) \o assoc (Tensor (X, Y)) Z W ==
        fmap Tensor ((Id X, assoc Y Z W): (C [*] C) (X, _) (X, _))
             \o assoc X (Tensor (Y, Z)) W
             \o fmap Tensor ((assoc X Y Z, Id W): (C [*] C) (_,W) (_, W));

    monoidal_coherence_unit:
      forall X Y: C,
        fmap Tensor ((raw X, Id Y): (C [*] C) (_,Y) (_,Y)) ==
        fmap Tensor ((Id X, lam Y): (C [*] C) (X,_) (X,_)) \o assoc X Unit Y
  }.

Structure MonoidalCategory :=
  {
    mcCat:> Category;
    mcX: Functor (mcCat [*] mcCat) mcCat;
    mcA: Assoc mcX;
    mcI: mcCat;
    mc1X: Natrans (BCR mcX mcI) (Identity_Functor mcCat);
    mc1XR: Natrans (Identity_Functor mcCat) (BCR mcX mcI);
    mcX1: Natrans (BCL mcX mcI) (Identity_Functor mcCat);
    mcX1R: Natrans (Identity_Functor mcCat) (BCL mcX mcI);
    prf_MonidalCategory:> isMonoidal mcA mc1X mc1XR mcX1 mcX1R
  }.
Notation "X [x] Y" := (mcX _ (X,Y)) (at level 55, right associativity).

Class isSymmetricMonoidal (C: MonoidalCategory)
      (comm: forall X Y: C, C (X [x] Y) (Y [x] X)) :=
  {
    comm_IsNatrans_l:
      forall Y: C, isNatrans (F:=BCL (mcX C) Y) (G:=BCR (mcX C) Y) (fun X => comm X Y);
    comm_natrans_l (Y: C): Natrans (BCL (mcX C) Y) (BCR (mcX C) Y) :=
      Build_Natrans (comm_IsNatrans_l Y);
    comm_IsNatrans_r:
      forall X: C, isNatrans (F:=BCR (mcX C) X) (G:=BCL (mcX C) X) (fun Y => comm X Y);
    comm_natrans_r (X: C): Natrans (BCR (mcX C) X) (BCL (mcX C) X) :=
      Build_Natrans (comm_IsNatrans_r X);

    (* coherence condition *)

    symm_monoidal_coherence_comm_assoc:
      forall (X Y Z: C),
        mcA Y Z X \o comm X (Y [x] Z) \o mcA X Y Z ==
        fmap (mcX C) ((Id Y, comm X Z): (C [*] C) (Y,_) (Y,_))
             \o mcA Y X Z \o fmap (mcX C) ((comm X Y, Id Z): (C [*] C) (_,Z) (_,Z));

    symm_monoidal_coherence_comm_ident:
      forall (X Y: C),
        comm Y X \o comm X Y == Id (X [x] Y)
  }.

Structure SymMonoidalCategory :=
  {
    smcMC:> MonoidalCategory;
    smcC: forall X Y: smcMC, smcMC (X [x] Y) (Y [x] X);

    prf_SymMonoidalCategory:> isSymmetricMonoidal smcC
  }.

Class isEnrichedCategory
      (V: MonoidalCategory)
      (eobj: Type)
      (ehom: eobj -> eobj -> V)
      (ecomp: forall (X Y Z: eobj), V (ehom Y Z [x] ehom X Y) (ehom X Z))
      (eident: forall X: eobj, V (mcI V) (ehom X X)) :=
  {
    ecomp_assoc:
      forall (X Y Z W: eobj),
        ecomp X Y W \o fmap (mcX V) ((ecomp Y Z W, Id (ehom X Y))
                                     : (V [*] V) (_,ehom X Y) (_,ehom X Y)) ==
        ecomp X Z W \o fmap (mcX V) ((Id (ehom Z W), ecomp X Y Z)
                                     : (V [*] V) (ehom Z W,_) (ehom Z W,_))
              \o mcA (ehom Z W) (ehom Y Z) (ehom X Y);

    ecomp_unital_l:
      forall (X Y: eobj),
        ecomp X Y Y
              \o fmap (mcX V) ((eident Y, Id (ehom X Y)): (V [*] V) (mcI V,_) (ehom Y Y,_)) ==
        mc1X V (ehom X Y);

    ecomp_unital_r:
      forall (X Y: eobj),
        ecomp X X Y
              \o fmap (mcX V) ((Id (ehom X Y), eident X): (V [*] V) (_,mcI V) (_,ehom X X)) ==
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

Definition ECHom `(C: EnrichedCategory V)(X Y: C): Setoid := V (mcI V) (ehom X Y) .
Instance Compose_ECHom `(C: EnrichedCategory V): Compose (@ECHom V C) :=
  {
    compose X Y Z f g :=
      ecomp X Y Z
            \o fmap (mcX V) ((g,  f): (V [*] V) (mcI V, mcI V) (ehom Y Z, ehom X Y))
            \o mc1XR V (mcI V)
  }.
Proof.
  intros X Y Z f f' Heqf g g' Heqg; simpl.
  assert ((fmap (mcX V)) ((g, f): (V [*] V) (mcI V, mcI V) (ehom Y Z, ehom X Y)) == (fmap (mcX V)) ((g', f'): (V [*] V) (mcI V, mcI V) (ehom Y Z, ehom X Y))).
  - apply eq_arg; simpl; split; assumption.
  - rewrite H; reflexivity.
Defined.

Instance Identity_ECHom `(C: EnrichedCategory V): Identity (@ECHom V C) :=
  {
    identity := @eident V C
  }.

Instance EC_IsCategory `(C: EnrichedCategory V)
: isCategory (Compose_ECHom C) (Identity_ECHom C).
Proof.
  split.
  - intros X Y Z W f g h; simpl.
    (* TODO *)
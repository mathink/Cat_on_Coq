Require Import 
Ssreflect.ssreflect
Ssreflect.eqtype
Ssreflect.ssrbool
Setoid Category Functor Cone.

Set Implicit Arguments.
(* Unset Strict Implicit. *)

Section Algebra.

  Variable (C: Category)(F: Functor C C).

  Structure Algebra :=
    { alg_obj:> C;
      alg_arr: F alg_obj --> alg_obj }.

  Structure Algebra_Map_base (X Y: Algebra) :=
    make_Algebra_Map_base
    { alg_map:> X --> Y;
      alg_map_commute:
        alg_arr Y•fmap F alg_map === alg_map•alg_arr X }.

  Definition eq_Algebra_Map {X Y: Algebra}(f g: Algebra_Map_base X Y) :=
    alg_map f ===  alg_map g.
  Hint Unfold eq_Algebra_Map.

  Program Definition Algebra_Map (X Y: Algebra): Setoid :=
    {| equal := @eq_Algebra_Map X Y |}.
  Next Obligation.
    split; rewrite /eq_Algebra_Map //=.
    move=> x //=; equiv_refl.
    move=> x y //=; equiv_symm.
    move=> x y z //=; equiv_trns.
  Qed.
  Canonical Structure Algebra_Map.

  Program Definition compose_Algebra_Map
          {X Y Z: Algebra}(f: Algebra_Map X Y)(g: Algebra_Map Y Z)
  : Algebra_Map X Z :=
    {| alg_map := g•f |}.
  Next Obligation.
    eapply transitivity;
      [ apply compose_subst_fst; apply symmetry, fmap_compose |].
    apply symmetry.
    eapply transitivity;
      [ eapply transitivity; [apply compose_assoc |];
        apply compose_subst_fst; apply symmetry, alg_map_commute |].
    eapply transitivity; [apply symmetry, compose_assoc |].
    apply symmetry;
      eapply transitivity; [apply symmetry, compose_assoc |].
    apply compose_subst_snd; apply alg_map_commute.
  Qed.
  Canonical Structure compose_Algebra_Map.

  Program Definition id_Algebra_Map (X: Algebra)
  : Algebra_Map X X :=
    {| alg_map := id |}.
  Next Obligation.
    eapply transitivity;
    [ apply compose_subst_fst; apply fmap_id |].
    eapply transitivity;
      [| apply symmetry, id_cod].
    apply id_dom.
  Qed.
  Canonical Structure id_Algebra_Map.


  Program Definition ALG: Category :=
    {| arr := Algebra_Map;
       compose := @compose_Algebra_Map ;
       id := id_Algebra_Map |}.
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply compose_assoc.
  Qed.            
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply compose_subst.
  Qed.            
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply id_dom.
  Qed.            
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply id_cod.
  Qed.            

  Canonical Structure ALG.

(*
  Lemma cata_fusion:
    forall (f g: Algebra)(h: Algebra_Map f g)(I: Initial ALG),
      h•initial_arr I f === initial_arr I g.
  Proof.
    move=> f g h I Heq.
    apply initial_fusion.
  Qed.
*)

  Definition catamorphism
             (I: Initial ALG)(X: Algebra)
  : alg_obj (initial_obj I) --> alg_obj X :=
    initial_arr I X.

  Lemma cata_refl:
    forall (I: Initial ALG),
      catamorphism I (initial_obj I) === id.
  Proof.
    move=> I; rewrite /catamorphism.
    apply (initiality (Initial_Spec:=I)).
  Qed.

  Lemma cata_fusion:
    forall (f g: Algebra)(h: alg_obj f --> alg_obj g)(I: Initial ALG),
      alg_arr g•fmap F h === h•alg_arr f  ->
      h•catamorphism I f === catamorphism I g.
  Proof.
    move=> f g h I Heq.
    move: (@initial_fusion ALG I f g {| alg_map_commute := Heq |}).
      by rewrite /= /eq_Algebra_Map /compose_Algebra_Map /=.
  Qed.
  
End Algebra.


Lemma Lambek_lemma:
  forall (C: Category)(F: Functor C C)(I: Initial (ALG F)),
    Iso (C:=C) (alg_obj (initial_obj I)) (F (alg_obj (initial_obj I))).
Proof.
  move=> C F I; rewrite /Iso /iso.
  exists
    (catamorphism I {| alg_arr := fmap F (alg_arr (initial_obj I)) |}).
  exists
    (alg_arr (initial_obj I)).
  split.
  - eapply transitivity; [| apply cata_refl ].
    apply 
      (cata_fusion {| alg_arr := fmap F (alg_arr (initial_obj I)) |}).
    equiv_refl.
  - eapply transitivity.
    apply symmetry.
    apply 
      (alg_map_commute (initial_arr I {| alg_arr := (fmap F) (alg_arr (initial_obj I)) |})).
    simpl.
    eapply transitivity; [apply fmap_compose |].
    eapply transitivity; [apply map_preserve_eq |].
    apply (cata_fusion {| alg_arr := fmap F (alg_arr (initial_obj I)) |}).
    equiv_refl.
    apply transitivity with (fmap F id);
      [apply map_preserve_eq | apply fmap_id].
    apply cata_refl.
Qed.    

  

Section ListFunctor.
  Variables (C: Category)
            (Hprod: hasProduct C)(Hcoprod: hasCoProduct C)
            (T: Terminal C).
  (* functoriality *)
  Definition listF_obj (A X: C): C :=
    coprod T (prod A X).

  Program Definition listF_arr (A X Y: C)
  : Map (X --> Y) (listF_obj A X --> listF_obj A Y) :=
    {| map_function f := coprod_arr (id_ T) (prod_arr id f) |}.
  Next Obligation.
    rename x into f; rename x' into f'.
    rewrite /coprod_arr /prod_arr.
    by apply coproduct_arr_subst_Y, compose_subst_fst, product_arr_subst_Y, compose_subst_snd.
  Qed.
  
  Program Definition listF (A: C): Functor C C :=
    {| fmap X Y := listF_arr A X Y |}.
  Next Obligation.
    rewrite /coprod_arr /prod_arr.
    eapply transitivity;
      [apply coproduct_arr_subst_Y, compose_subst_fst
      | apply coproduct_universality].
    apply product_arr_subst; apply id_cod.
    eapply transitivity;
      [ apply id_cod | apply symmetry, id_dom ].
    eapply transitivity;
      [ apply id_cod | apply symmetry ].
    eapply transitivity;
      [ apply compose_subst_fst, product_universality | apply id_dom];
      apply id_dom.
  Qed.
  Next Obligation.
    eapply transitivity;
    [ apply coprod_arr_compose |].
    apply coproduct_arr_subst.
    eapply transitivity; [ apply symmetry, compose_assoc | apply id_dom].
    apply compose_subst_fst.
    eapply transitivity; 
      [ apply prod_arr_compose |].
    apply product_arr_subst_X.
    rewrite /coprod_arr /prod_arr.
    apply compose_subst_snd, id_dom.
  Qed.

  Program Definition listF_alg_gen {A X: C}
             (fnil: T --> X)(fcons: prod A X --> X)
  : Algebra (listF A) :=
    {| alg_arr := coproduct_arr (coprod T (prod A X)) _ fnil fcons |}.
  
End ListFunctor.


(* for Initial Algebra of listF *)
Require Import Arith  Coq.Logic.ProofIrrelevance.

Definition eq_leq (n m: nat)(H H': n <= m) := True.
Program Definition leq (n m: nat): Setoid :=
  {| equal H H' := @eq_leq n m H H' |}.
Next Obligation.
  rewrite /eq_leq; split.
  - by move=> x.
  - by move=> x y.
  - by move=> x y z.
Qed.

Program Definition compose_leq
        {n m k: nat}(f: leq n m)(g: leq m k): leq n k.
by apply le_trans.
Defined.

Program Definition id_leq (n: nat): leq n n.
by apply le_n.
Defined.

Program Definition Omega: Category :=
  {| arr := leq;
     compose := @compose_leq;
     id := @id_leq |}.
Next Obligation.
  by rewrite /eq_leq //=.
Qed.
Next Obligation.
  by rewrite /eq_leq //=.
Qed.
Next Obligation.
  by rewrite /eq_leq //=.
Qed.


Definition Omega_Chain (C: Category) := Functor Omega C.
Definition Omega_CoLimit {C: Category}(F: Omega_Chain C) := CoLimit F.

Class Omega_CoComplete (C: Category) :=
  occ_spec (F: Omega_Chain C): hasCoLimit F.

Section InitialOmega.

  Variables (C: Category)
            (Hprod: hasProduct C)(Hcoprod: hasCoProduct C)
            (I: Initial C)(T: Terminal C)
            (F: Functor C C).
  
  Fixpoint n_f_prod (n: nat)(f: nat -> C): C :=
    match n with 
      | 0 => f 0
      | S p => prod (f n) (n_f_prod p f)
    end.

  Fixpoint n_app (n: nat)(X: C): C :=
    match n with
      | 0 => X
      | S p => F (n_app p X)
    end.

  Fixpoint n_omega_chain (n: nat) :=
    match n as m return (n_app m I --> n_app (S m) I) with
      | 0 => (initial_arr I (F I))
      | S p => fmap F (n_omega_chain p)
    end.

  Definition le_rect
  : forall (n : nat) (P : nat -> Type),
      P n ->
      (forall m : nat, n <= m -> P m -> P (S m)) ->
      forall n0 : nat, n <= n0 -> P n0.
  Proof.
    elim=> [| n IHn] P Hp IHle. 
    - elim=> [| m IHm] //= Hle.
      apply IHle; [apply le_0_n | apply IHm, le_0_n].
    - elim=> [| m IHm] //= Hle.
      + elim (le_Sn_0 n Hle).
        have: forall m: nat, n <= m -> P (S m) -> P (S (S m)).
          by move=> m' Hle' Hp'; apply IHle; [apply le_n_S |].
          move=> H; apply: (IHn (fun n => P (S n)) Hp H).
            by apply le_S_n.
  Defined.

  Program Definition ioc_fmap {n m: nat}
  : Map (leq n m) (n_app n I --> n_app m I) :=
    {| map_function H := _ |}.
  Next Obligation.
    induction H using le_rect.
    - by apply id.
    - by apply (n_omega_chain m•IHle).
  Defined.
  Next Obligation.
    rewrite (proof_irrelevance (n<=m) x x').
    equiv_refl.
  Defined.

  Program Definition initial_omega_chain: Omega_Chain C :=
    {| fobj n := n_app n I;
       fmap := @ioc_fmap |}.
  Next Obligation.
    rewrite /ioc_fmap_obligation_1 /id_leq //=.
    elim: X => [| n IHn] /=.
    - equiv_refl.
    - rewrite /ssr_have //=.
      eapply transitivity; [| apply fmap_id ].
      eapply transitivity; [| apply map_preserve_eq, IHn ].
      rewrite (proof_irrelevance (n <= n) (le_S_n n n (le_n (S n))) (le_n n)).
      (* oh... *)


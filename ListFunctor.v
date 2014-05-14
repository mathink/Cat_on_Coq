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
  Defined.
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
  Defined.
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
  Defined.
  Canonical Structure id_Algebra_Map.


  Program Definition ALG: Category :=
    {| arr := Algebra_Map;
       compose := @compose_Algebra_Map ;
       id := id_Algebra_Map |}.
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply compose_assoc.
  Defined.            
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply compose_subst.
  Defined.            
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply id_dom.
  Defined.            
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply id_cod.
  Defined.            

  Canonical Structure ALG.

(*
  Lemma cata_fusion:
    forall (f g: Algebra)(h: Algebra_Map f g)(I: Initial ALG),
      h•initial_arr I f === initial_arr I g.
  Proof.
    move=> f g h I Heq.
    apply initial_fusion.
  Defined.
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
  Defined.

  Lemma cata_fusion:
    forall (f g: Algebra)(h: alg_obj f --> alg_obj g)(I: Initial ALG),
      alg_arr g•fmap F h === h•alg_arr f  ->
      h•catamorphism I f === catamorphism I g.
  Proof.
    move=> f g h I Heq.
    move: (@initial_fusion ALG I f g {| alg_map_commute := Heq |}).
      by rewrite /= /eq_Algebra_Map /compose_Algebra_Map /=.
  Defined.
  
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
Defined.    

  

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
  Defined.
  
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
  Defined.
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
  Defined.

  Program Definition listF_alg_gen {A X: C}
             (fnil: T --> X)(fcons: prod A X --> X)
  : Algebra (listF A) :=
    {| alg_arr := coproduct_arr (coprod T (prod A X)) _ fnil fcons |}.
  
End ListFunctor.


(* for Initial Algebra of listF *)
Require Import Le Coq.Logic.ProofIrrelevance.

(*
Inductive leq (n: nat): nat -> Set :=
| leq_n : leq n n
| leq_S (m: nat): leq n m -> leq n (S m).

Definition eq_leq (n m: nat)(H H': leq n m) := True.

Program Definition LEQ (n m: nat): Setoid :=
  {| equal H H' := @eq_leq n m H H' |}.
Next Obligation.
  rewrite /eq_leq; split.
  - by move=> x.
  - by move=> x y.
  - by move=> x y z /=.
Defined.

Fixpoint leq_0_n (n: nat): leq 0 n :=
  match n as m return (leq 0 m) with
    | 0 => leq_n 0
    | S p => leq_S (leq_0_n p)
  end.

Fixpoint leq_n_S (n m: nat)(Hleq: leq n m): leq (S n) (S m) :=
  match Hleq with
    | leq_n => leq_n (S n)
    | leq_S p H => leq_S (leq_n_S H)
  end.
Check @eq_rec
.
Fixpoint leq_Sn_m (n m: nat)(Hleq: leq (S n) m): leq n m :=
  match Hleq in (leq _ m') return leq _ m' with
    | leq_n => leq_S (leq_n n)
    | leq_S p H => leq_S (leq_Sn_m H)
  end.

Fixpoint leq_trans (n m k: nat)(Hleq: leq n m)
: leq m k -> leq n k.
refine(
  match Hleq in (leq _ m') return (leq m' k -> leq n k) with
    | leq_n => fun (H: leq n k) =>
                 match H in (leq _ k') return leq n k' with
                   | leq_n => leq_n n
                   | leq_S p H => leq_S H
                 end
    | leq_S p Hp => fun (H: leq (S p) k) => 
                      match H in (leq _ k') return leq n k' with
                        | leq_n => leq_trans _ _ _ Hp (leq_S (leq_n p))
                        | leq_S q Hq => _
                      end
  end).
apply leq_S.


Lemma leq_trans_assoc:
  forall (n m k p: nat)(f: leq n m)(g: leq m k)(h: leq k p),
    leq_trans f (leq_trans g h) = leq_trans (leq_trans f g) h.
Proof.
  move=> n m k p Hleq; move: k p.
  elim: Hleq => [| m' Hm IHleq_m] //= k p g h.
  - move: g p h.
    elim=> [| k' Hk IHleq_k] //=.
    + move=> p [| p' Hp] //=.
    + move=> p h.
      inversion h.
      * subst.
        move: (IHleq_k k' (leq_n k')).
        apply leq_S_n in h.
 move=> p.
      elim=> [| p' Hp IHleq_p] //=.
      move: (IHleq_k _ (leq_S (leq_n k'))) => ->.
      by destruct Hk.
  rewrite -IHleq.
  induction g; move=> //=.
Qed.

Definition compose_leq
        {n m k: nat}(f: LEQ n m)(g: LEQ m k): LEQ n k :=
  leq_trans f g.

Definition id_leq (n: nat): LEQ n n := leq_n n.

  
*)
Definition eq_le (n m: nat)(H H': n <= m) := True.

Program Definition LEQ (n m: nat): Setoid :=
  {| equal H H' := @eq_le n m H H' |}.
Next Obligation.
  rewrite /eq_le; split.
  - by move=> x.
  - by move=> x y.
  - by move=> x y z /=.
Qed.
                     
Program Definition Omega: Category :=
  {| arr := LEQ;
     compose := @le_trans;
     id := @le_n |}.
Next Obligation.
  by rewrite /eq_le.
Qed.
Next Obligation.
  by rewrite /eq_le.
Qed.
Next Obligation.
  by rewrite /eq_le.
Qed.

Definition Omega_Chain (C: Category) := Functor Omega C.
Definition Omega_CoLimit {C: Category}(F: Omega_Chain C) := CoLimit F.

Class Omega_CoComplete (C: Category) :=
  occ_spec (F: Omega_Chain C): hasCoLimit F.

Section InitialOmega.

  Variables (C: Category)
            (Hprod: hasProduct C)(Hcoprod: hasCoProduct C).
  
  Fixpoint n_f_prod (n: nat)(f: nat -> C): C :=
    match n with 
      | 0 => f 0
      | S p => prod (f n) (n_f_prod p f)
    end.

  Fixpoint n_app (F: Functor C C)(n: nat)(X: C): C :=
    match n with
      | 0 => X
      | S p => F (n_app F p X)
    end.
  
  Fixpoint n_app_fmap (F: Functor C C)(n: nat){X Y: C}(f: X --> Y) :=
    match n as m return (n_app F m X --> n_app F m Y) with
      | 0 => f
      | S p => fmap F (n_app_fmap F p f)
    end.
  
  Lemma n_app_inc:
    forall (F: Functor C C)(n: nat)(X: C),
      F (n_app F n X) = n_app F n (F X).
  Proof.
    move=> F; elim=> [| n IHn] //= X.
    by rewrite IHn.
  Qed.

  Fixpoint n_omega_chain (F: Functor C C)(X: C)(f: X --> F X)(n: nat) :=
    match n as m return (n_app F m X --> n_app F (S m) X) with
      | 0 => f
      | S p => fmap F (n_omega_chain F X f p)
    end.

(*
  Definition leq_rect
  : forall (n : nat) (P : nat -> Type),
      P n ->
      (forall m : nat, leq n m -> P m -> P (S m)) ->
      forall m : nat, leq n m -> P m.
  Proof.
    elim=> [| n IHn] P IHp IHle.
    - elim=> [| m IHm] //= Hle.
      apply IHle; [| apply IHm]; apply leq_0_n.
    - elim=> [| m IHm] //= Hle; [elim (leq_Sn_0 Hle) |].
      apply (IHn (fun n => P (S n)) IHp).
      + by move=> m' Hle'; apply IHle, leq_n_S.
      + apply leq_S_n.

    move=> P Hnn Hle n; move: n P Hnn Hle.
    elim=> [| n IHn] P IHnn IHle.
    - elim=> [| m IHm].
      + move=> _; apply IHnn.
      + move=> H; apply IHle, IHm; apply leq_le, le_0_n.
    - move=> [| m] H.
      + apply leq_le in H; elim (le_Sn_0 n H).
      + have: forall n, P (S n) (S n).
        by move=> n'; apply IHnn.
        have: forall n m : nat, P (S n) (S m) -> P (S n) (S (S m)).
        by move=> n' m'; apply IHle.
        move=> Hle Hnn; apply : (IHn (fun n m => P (S n) (S m)) Hnn Hle).
        by apply leq_le in H; apply leq_le, le_S_n.
  Defined.
*)

  Fixpoint ioc_fmap_function (F: Functor C C)(X: C)(f: X --> F X){n m: nat}(Heq: leq n m): (n_app F n X --> n_app F m X) :=
    match Heq in (leq _ m') return (n_app F n X --> n_app F m' X) with
      | leq_n => n_app_fmap F n id
      | leq_S p H => n_omega_chain F X f p•ioc_fmap_function F X f H
    end.

  Program Definition ioc_fmap (F: Functor C C)(X: C)(f: X --> F X){n m: nat}
  : Map (LEQ n m) (n_app F n X --> n_app F m X) :=
    {| map_function H := ioc_fmap_function F X f H |}.
  Next Obligation.
    unfold eq_leq in Heq.
    induction x.
    rewrite (proof_irrelevance (leq n m) x x').
    equiv_refl.
  Defined.

  

  Program Definition initial_omega_chain (I: Initial C)(F: Functor C C)
  : Omega_Chain C :=
    {| fobj n := n_app F n I;
       fmap := @ioc_fmap F I (initial_arr I (F I))|}.
  Next Obligation.
    elim: X => [| n IHn] /=.
    - equiv_refl.
    - 
      (* oh... *)




Inductive Void: Set := .
Print Void_rec.
Print False_rec.
Definition leq_Sn_n (n: nat)(Hleq: leq (S n) n): Void.
  inversion Hleq.
  move: H; apply Void_rec.
Definition leq_Sn_0 (n: nat)(Hleq: leq (S n) 0): Void.
  inversion Hleq.
Defined.
Print leq_Sn_0.

Fixpoint leq_n_S (n m: nat)(Hleq: leq n m): leq (S n) (S m) :=
  match Hleq with
    | leq_n => leq_n (S n)
    | leq_S k H => leq_S (leq_n_S H)
  end.

Fixpoint leq_Sn_m (n m: nat)(Hleq: leq (S n) m): leq n m :=
  match Hleq in (leq (S n0) _) return leq n0 _ with
    | leq_n => 

Lemma leq_Sn_m:
  forall n m, leq (S n) m -> leq n m.
Proof.
    move=> n m; move: m n.
    induction m.
    intros.
    elim (leq_Sn_0 H).
    move=> [| n].
    intros.
    apply leq_0_n.

    intro.

    inversion H.
    apply leq_S, leq_n.
    subst.
    apply IHm in H1.
    by apply leq_S.
  Defined.



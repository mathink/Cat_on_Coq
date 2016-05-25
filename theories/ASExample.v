Set Implicit Arguments.
Unset Strict Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.
Require Import COC.AlgebraicStructures.

(** * 具体例：整数環
 **)
Require Import ZArith.
Open Scope Z_scope.

Canonical Structure positive_setoid := @Setoid.make _ (@eq positive) _.
Canonical Structure Z_setoid := @Setoid.make _ (@eq Z) _.
Instance Zneg_Proper : Proper ((==:>positive_setoid) ==> ((==:>Z_setoid))) Zneg.
Proof.
  now intros p q Heq; simpl in *; subst.
Qed.

Instance Zpos_Proper : Proper ((==:>positive_setoid) ==> ((==:>Z_setoid))) Zpos.
Proof.
  now intros p q Heq; simpl in *; subst.
Qed.

(* Group of '+' *)
Program Instance Zplus_is_binop: isBinop (X:=Z_setoid) Zplus.
Canonical Structure Zplus_binop := Binop.make Zplus_is_binop.

Program Instance Zplus_is_monoid: isMonoid Zplus_binop 0.
Next Obligation.
  intros x y z; simpl.
  apply Zplus_assoc.
Qed.
Next Obligation.
  repeat split.
  intros x; simpl.
  apply Zplus_0_r.
Qed.
Canonical Structure Zplus_monoid := Monoid.make Zplus_is_monoid.

Program Instance Zinv_is_map: isMap (X:=Z_setoid) Zopp.
Canonical Structure Zinv_map: Map Z_setoid Z_setoid := Map.make Zinv_is_map.

Program Instance Zplus_is_group: isGroup Zplus_binop 0 Zinv_map.
Next Obligation.
  repeat split.
  - intros x; simpl.
    apply Z.add_opp_diag_l.
  - intros x; simpl.
    apply Z.add_opp_diag_r.
Qed.
Canonical Structure Zgroup_monoid := Group.make Zplus_is_group.

Program Instance Zplus_commute: Commute Zplus_binop.
Next Obligation.
  apply Zplus_comm.
Qed.

(* Monoid of '*' *)
Instance Zmult_is_binop: isBinop (X:=Z_setoid) Zmult.
Proof.
  intros x y Heq z w Heq'; simpl in *; subst; auto.
Qed.
Canonical Structure Zmult_binop := Binop.make Zmult_is_binop.

Program Instance Zmult_is_monoid: isMonoid Zmult_binop 1.
Next Obligation.
  intros x y z; simpl.
  apply Zmult_assoc.
Qed.
Next Obligation.
  repeat split.
  - intros x; simpl.
    destruct x; auto.
  - intros x; simpl.
    apply Zmult_1_r.
Qed.
Canonical Structure Zmult_monoid := Monoid.make Zmult_is_monoid.

(* Ring of '+' & '*' *)
Program Instance Z_is_ring: isRing Zplus_binop 0 Zinv_map Zmult_binop 1.
Next Obligation.
  split; simpl; intros.
  - apply Z.mul_add_distr_l.
  - apply Z.mul_add_distr_r.
Qed.
Canonical Structure Z_ring := Ring.make Z_is_ring.

Compute (1 * 2 + 3).
     (* = 5 *)
     (* : Z *)

Open Scope ring_scope.
Compute (1 * 2 + 3).
     (* = 5 *)
     (* : Z_ring *)

(** * 具体例：整数から任意の環への準同型 **)
Section FromZ.
  Variable (R: Ring).
  Existing Instance Ring.prf.
  Open Scope ring_scope.

  Fixpoint rep_aux (p: positive): R :=
    match p with
    | xH => Ring.e R
    | xO p' => let x := rep_aux p' in x + x
    | xI p' => let x := rep_aux p' in 1 + x + x
    end.
  Arguments rep_aux _%positive.

  Lemma rep_aux_succ:
    forall p: positive,
      rep_aux (Pos.succ p) == 1 + rep_aux p.
  Proof.
    induction p; simpl in *.
    - rewrite IHp.
      rewrite associative.
      rewrite (commute (1 + rep_aux p)).
      now rewrite <- associative.
    - now rewrite associative.
    - reflexivity.
  Qed.

  Lemma rep_aux_add:
    forall p q,
      rep_aux (p + q) == rep_aux p + rep_aux q.
  Proof.
    induction p; simpl; destruct q; simpl.
    - simpl.
      rewrite Pos.add_carry_spec.
      rewrite (rep_aux_succ (p + q)).
      rewrite IHp.
      repeat rewrite <- associative.
      rewrite (Ring.add_commute_l (rep_aux q) 1 _).
      rewrite (Ring.add_commute_l (rep_aux q) (rep_aux p) _).
      now rewrite (Ring.add_commute_l 1 (rep_aux p) (rep_aux q + _)).
    - simpl.
      rewrite IHp.
      repeat rewrite <- associative.
      now rewrite (Ring.add_commute_l (rep_aux q)).
    - simpl.
      rewrite rep_aux_succ.
      repeat rewrite <- associative.
      now rewrite (Ring.add_commute (_ p) 1).
    - rewrite IHp.
      rewrite <- (associative 1 (rep_aux q) _).
      rewrite (Ring.add_commute_l (rep_aux p + rep_aux p) 1).
      repeat rewrite <- associative.
      now rewrite (Ring.add_commute_l (rep_aux q)).
    - rewrite IHp.
      repeat rewrite <- associative.
      now rewrite (Ring.add_commute_l (rep_aux q)).
    - now rewrite (Ring.add_commute _ 1), associative.
    - rewrite (rep_aux_succ q).
      rewrite <- associative.
      rewrite (Ring.add_commute_l (rep_aux q)).
      now rewrite <- associative.
    - now rewrite associative.
    - reflexivity.
  Qed.

  Lemma rep_aux_pred_double:
    forall p,
      rep_aux (Pos.pred_double p) == rep_aux p + rep_aux p + - 1%rng.
  Proof.
    induction p; simpl; intros.
    - repeat rewrite <- associative.
      rewrite (Ring.add_commute _ (- 1%rng)).
      rewrite (Ring.add_commute_l (rep_aux p) (- 1%rng)); simpl.
      now rewrite (associative _ (- 1%rng)), Ring.add_inv_r, Ring.add_id_l.
    - rewrite IHp.
      rewrite (Ring.add_commute _ (- 1%rng)) at 1.
      now rewrite (associative 1), Ring.add_inv_r, Ring.add_id_l, associative.
    - now rewrite <- associative, Ring.add_inv_r, Ring.add_id_r.
  Qed.
  
  Program Canonical Structure rep_aux_map: Map positive_setoid R := Map.build rep_aux.
  Next Obligation.
    now intros p q Heq; simpl in *; subst.
  Qed.
  
  Definition rep (z: Z): R :=
    match z with
    | Z0 => 0
    | Zpos p => rep_aux p
    | Zneg p => - (rep_aux p)
    end.
  Arguments rep _%Z.

  Program Canonical Structure rep_map: Map Z_ring R := Map.build rep.
  Next Obligation.
    now intros p q Heq; simpl in *; subst.
  Qed.

  Lemma rep_double:
    forall p,
      rep (Z.double p) == rep p + rep p.
  Proof.
    destruct p; simpl.
    - now rewrite Ring.add_id_l.
    - reflexivity.
    - now rewrite (Group.inv_op (G:=Ring.add_group R)); simpl.
  Qed.
  
  Lemma rep_succ_double:
    forall p,
      rep (Z.succ_double p) == 1 + rep p + rep p.
  Proof.
    destruct p; simpl.
    - now repeat rewrite Ring.add_id_r.
    - reflexivity.
    - rewrite rep_aux_pred_double.
      repeat rewrite (Group.inv_op (G:=Ring.add_group R)); simpl.
      now rewrite (Group.inv_inv (G:=Ring.add_group R)), associative.
  Qed.

  Lemma rep_pred_double:
    forall p,
      rep (Z.pred_double p) == - 1%rng + rep p + rep p.
  Proof.
    destruct p; simpl.
    - now repeat rewrite Ring.add_id_r.
    - now rewrite rep_aux_pred_double, commute, <- associative.
    - repeat rewrite (Group.inv_op (G:=Ring.add_group R)); simpl.
      now rewrite (commute), (commute _ (- 1%rng)).
  Qed.

  Lemma rep_pos_sub:
    forall p q,
      rep (Z.pos_sub p q) == rep_aux p - (rep_aux q).
  Proof.
    induction p, q; simpl.
    - rewrite rep_double, IHp.
      repeat rewrite (Group.inv_op (G:=Ring.add_group R)); simpl.
      repeat rewrite <- associative.
      rewrite (Ring.add_commute _ (- 1%rng)).
      rewrite (Ring.add_commute_l (- rep_aux q) (- 1%rng)); simpl.
      do 2 rewrite (Ring.add_commute_l (rep_aux p) (- 1%rng)); simpl.
      rewrite (associative 1 _).
      rewrite Ring.add_inv_r, Ring.add_id_l.
      now rewrite (Ring.add_commute_l _ (rep_aux p)).
    - rewrite rep_succ_double, IHp.
      rewrite (Group.inv_op (G:=Ring.add_group R)); simpl.
      repeat rewrite <- associative.
      now rewrite (Ring.add_commute_l (- rep_aux q) (rep_aux p)).
    - rewrite (Ring.add_commute _ (- 1%rng)), <- associative, (associative _ 1).
      now rewrite Ring.add_inv_l, Ring.add_id_l.
    - rewrite rep_pred_double, IHp, !(Group.inv_op (G:=Ring.add_group R)); simpl.
      repeat rewrite <- associative.
      repeat rewrite (Ring.add_commute_l _ (rep_aux p)).
      rewrite (Ring.add_commute_l _ (- rep_aux q)); simpl.
      now rewrite (Ring.add_commute (- 1%rng)).
    - rewrite rep_double, IHp.
      repeat rewrite (Group.inv_op (G:=Ring.add_group R)); simpl.
      repeat rewrite <- associative.
      now rewrite (Ring.add_commute_l _ (rep_aux p)).
    - apply rep_aux_pred_double.
    - repeat rewrite (Group.inv_op (G:=Ring.add_group R)); simpl.
      rewrite (commute _ (- 1%rng)).
      rewrite !(Ring.add_commute_l (R:=R) _ (- 1%rng)), associative; simpl.
      now rewrite Ring.add_inv_l, Ring.add_id_l.
    - now rewrite rep_aux_pred_double, (Group.inv_op (G:=Ring.add_group R)), (Group.inv_inv (G:=Ring.add_group R)); simpl.
    - now rewrite Ring.add_inv_r.
  Qed.
  
  Lemma rep_add:
    forall p q: Z,
      rep (p + q) == rep p + rep q.
  Proof.
    intros [|p|p] [|q|q]; simpl; try (now rewrite ?Ring.add_id_l, ?Ring.add_id_r).
    - now apply rep_aux_add.
    - now apply rep_pos_sub.
    - now rewrite rep_pos_sub, commute.
    - now rewrite rep_aux_add, (Group.inv_op (G:=Ring.add_group R)), commute; simpl.
  Qed.

  Lemma rep_aux_mul:
    forall p q,
      rep_aux (p * q) == rep_aux p * rep_aux q.
  Proof.
    induction p; simpl.
    - intros q.
      rewrite rep_aux_add; simpl.
      rewrite !distributive_r, Ring.mul_id_l.
      now repeat rewrite <- associative, <- IHp.
    - intros.
      now rewrite !distributive_r, <- IHp.
    - intros.
      now rewrite Ring.mul_id_l.
  Qed.
    
  Lemma rep_mul:
    forall p q,
      rep (p * q) == rep p * rep q.
  Proof.
    intros [|p|p] [|q|q]; simpl; try (now rewrite ?Ring.mul_0_l, ?Ring.mul_0_r).
    - now apply rep_aux_mul.
    - now rewrite rep_aux_mul, <- Ring.mul_inv_r.
    - now rewrite rep_aux_mul, <- Ring.mul_inv_l.
    - now rewrite rep_aux_mul, <- Ring.mul_inv_inv.
  Qed.

  Program Instance rep_is_ring_hom: isRingHom _ _ rep_map.
  Next Obligation.
    split; simpl; intros.
    - split; simpl; intros.
      + apply rep_add.
      + reflexivity.
    - destruct x as [|p|p]; simpl.
      + now rewrite (Group.inv_id (Ring.add_group R)).
      + reflexivity.
      + now rewrite (Group.inv_inv (G:=Ring.add_group R)).
  Qed.
  Next Obligation.
    split; simpl; intros.
    - apply rep_mul.
    - reflexivity.
  Qed.

  Definition rep_ring_hom: RingHom Z_ring R := RingHom.make rep_is_ring_hom.

  Eval simpl in (rep_ring_hom 0).
     (*   = 0 *)
     (* : R *)
  Eval simpl in (rep_ring_hom 1).
     (* = 1 *)
     (* : R *)
  Eval simpl in (rep_ring_hom 2).
     (* = 1 + 1 *)
     (* : R *)
  Eval simpl in (rep_ring_hom 4).
     (* = 1 + 1 + (1 + 1) *)
     (* : R *)
  Eval simpl in (rep_ring_hom 10).
     (* = 1 + (1 + 1) + (1 + 1) + (1 + (1 + 1) + (1 + 1)) *)
     (* : R *)
  Eval simpl in (rep_ring_hom 33).
     (*   = 1 + *)
     (*   (1 + 1 + (1 + 1) + (1 + 1 + (1 + 1)) + *)
     (*    (1 + 1 + (1 + 1) + (1 + 1 + (1 + 1)))) + *)
     (*   (1 + 1 + (1 + 1) + (1 + 1 + (1 + 1)) + *)
     (*    (1 + 1 + (1 + 1) + (1 + 1 + (1 + 1)))) *)
     (* : R *)
  Eval simpl in (rep_ring_hom 100).
     (* = 1 + (1 + 1 + 1 + (1 + 1 + 1) + (1 + 1 + 1 + (1 + 1 + 1))) + *)
     (*   (1 + 1 + 1 + (1 + 1 + 1) + (1 + 1 + 1 + (1 + 1 + 1))) + *)
     (*   (1 + (1 + 1 + 1 + (1 + 1 + 1) + (1 + 1 + 1 + (1 + 1 + 1))) + *)
     (*    (1 + 1 + 1 + (1 + 1 + 1) + (1 + 1 + 1 + (1 + 1 + 1)))) + *)
     (*   (1 + (1 + 1 + 1 + (1 + 1 + 1) + (1 + 1 + 1 + (1 + 1 + 1))) + *)
     (*    (1 + 1 + 1 + (1 + 1 + 1) + (1 + 1 + 1 + (1 + 1 + 1))) + *)
     (*    (1 + (1 + 1 + 1 + (1 + 1 + 1) + (1 + 1 + 1 + (1 + 1 + 1))) + *)
     (*     (1 + 1 + 1 + (1 + 1 + 1) + (1 + 1 + 1 + (1 + 1 + 1))))) *)
     (* : R *)
End FromZ.

(** * 具体例：有理数からなる体を構成する **)
Require Import QArith.
Open Scope Q_scope.

Canonical Structure Q_setoid := Setoid.make Q_Setoid.

(* Group of '+' *)
Program Instance Qplus_is_binop: isBinop (X:=Q_setoid) Qplus.
Canonical Structure Qplus_binop := Binop.make Qplus_is_binop.

Program Instance Qplus_is_monoid: isMonoid Qplus_binop 0.
Next Obligation.
  intros x y z; simpl.
  apply Qplus_assoc.
Qed.
Next Obligation.
  repeat split.
  - intros x; simpl.
    now apply Qplus_0_l.
  - intros x; simpl.
    now apply Qplus_0_r.
Qed.
Canonical Structure Qplus_monoid := Monoid.make Qplus_is_monoid.

Program Instance Qopp_is_map: isMap (X:=Q_setoid) Qopp.
Canonical Structure Qopp_map := Map.make Qopp_is_map.

Program Instance Qplus_is_group: isGroup Qplus_binop 0 Qopp_map.
Next Obligation.
  repeat split.
  - intros x; simpl.
    now rewrite Qplus_comm, Qplus_opp_r.
  - now intros x; simpl; rewrite Qplus_opp_r.
Qed.
Canonical Structure Qplus_group := Group.make Qplus_is_group.

Program Instance Qplus_commute: Commute Qplus_binop.
Next Obligation.
  apply Qplus_comm.
Qed.

(* Group of '*' *)
Program Instance Qmult_is_binop: isBinop (X:=Q_setoid) Qmult.
Canonical Structure Qmult_binop := Binop.make Qmult_is_binop.

Program Instance Qmult_is_monoid: isMonoid Qmult_binop 1.
Next Obligation.
  intros x y z; simpl.
  apply Qmult_assoc.
Qed.
Next Obligation.
  repeat split.
  - intros x; simpl.
    now apply Qmult_1_l.
  - intros x; simpl.
    now apply Qmult_1_r.
Qed.
Canonical Structure Qmult_monoid := Monoid.make Qmult_is_monoid.

Program Instance Qinv_is_map: isMap (X:=Q_setoid) Qinv.
Canonical Structure Qinv_map := Map.make Qinv_is_map.

(* Ring of '+' & '*' *)
Program Instance Q_is_ring: isRing Qplus_binop 0 Qopp_map Qmult_binop 1.
Next Obligation.
  split; simpl; intros.
  - apply Qmult_plus_distr_r.
  - apply Qmult_plus_distr_l.
Qed.
Canonical Structure Q_ring := Ring.make Q_is_ring.

(* Field of '+' & '*' *)
Program Instance Q_is_field: isField Qplus_binop 0 Qopp_map Qmult_binop 1 Qinv_map.
Next Obligation.
  now rewrite Qmult_comm, Qmult_inv_r.
Qed.
Next Obligation.
  now rewrite Qmult_inv_r.
Qed.
Canonical Structure Q_field := Field.make Q_is_field.

(* an example *)
Open Scope field_scope.
Eval compute in ((4#2) / (3#2) == 4#3).
     (* = 24%Z = 24%Z *)
     (* : Prop *)
Close Scope Q_scope.


(** * 具体例：整数環のイデアル **)
Open Scope Z_scope.

(* 任意の n について n の倍数からなる部分集合 Zn はイデアル *)
Instance Zn_is_ideal (n: Z): isIdeal Z_ring `(exists x, m = x * n).
Proof.
  split.
  - intros x y Heq P; simpl.
    now rewrite Heq; auto.
  - intros x y [p Hp] [q Hq]; subst.
    exists (p + q).
    now rewrite <- Z.mul_add_distr_r.
  - intros x [p Hp]; subst; simpl.
    exists (-p).
    now rewrite Zopp_mult_distr_l.
  - now (exists 0).
  - intros x y [p Hp] [q Hq]; subst.
    exists ((p * q) * n).
    rewrite <- Z.mul_shuffle1.
    now rewrite !Z.mul_assoc.
  - intros a x [p Hp]; subst.
    exists (a * p).
    rewrite Z.mul_assoc.
    rewrite Z.mul_shuffle0.
    now rewrite Z.mul_comm.
  - intros a x [p Hp]; subst.
    exists (p * a).
    now rewrite Z.mul_shuffle0.
Qed.
Definition Zn_ideal (n: Z) := Ideal.make (Zn_is_ideal n).

(* Z2 は 10 を含む *)
Goal Ideal.contain (Zn_ideal 2) 10.
Proof.
  simpl.
  now exists 5.
Qed.             

(* さらに、任意の偶数を含む *)
Goal forall n,
    Ideal.contain (Zn_ideal 2) (n * 2).
Proof.
  simpl; intros.
  now exists n.
Qed.             

(* 奇数は含まない *)
Goal forall n,
    ~ Ideal.contain (Zn_ideal 2) (n * 2 + 1).
Proof.
  intros n H; simpl in H.
  assert (H': exists x, n * 2 + 1 = 2 * x).
  {
    destruct H as [m Hm]; exists m.
    now rewrite (Z.mul_comm 2 m).
  }
  rewrite <- Zeven_ex_iff in H'.
  revert H'.
  apply Zodd_not_Zeven.
  rewrite Zodd_ex_iff.
  now exists n; rewrite Z.mul_comm.
Qed. 

(** Z/2Z は 0 と 1 (の同値類)からなる剰余環 **)
Definition Z_2Z := IdealQuotient (Zn_ideal 2).
Lemma Z_2Z_has_only_two_elements:
  forall x: Z_2Z,
    x == 0 \/ x == 1.
Proof.
  simpl; intros [ | p | p]; simpl.
  - now left; exists 0.
  - destruct p; simpl.
    + right.
      exists (Zpos p).
      rewrite Zmult_comm.
      now apply Pos2Z.inj_xO.
    + left.
      exists (Zpos p).
      rewrite Zmult_comm.
      now apply Pos2Z.inj_xO.
    + now right; exists 0.
  - induction p; simpl.
    + right.
      exists (Zneg (Pos.succ p)).
      rewrite Zmult_comm.
      now apply Pos2Z.neg_xO.
    + left.
      exists (Zneg p).
      rewrite Zmult_comm.
      now apply Pos2Z.neg_xO.
    + now right; exists (-1).
Qed.


(* Z_2Z を環として解釈することができるようになった *)
(* あまり意味はないけど *)
Lemma Z_2Z_add_0:
  forall x: Z_2Z, (x + x == 0)%rng.
Proof.
  simpl.
  intros x; exists x.
  now rewrite Zplus_0_r, Zplus_diag_eq_mult_2.
Qed.

(** *** Z は始対象 **)
Require Import Category.
Program Instance Z_is_initial_of_Rng: isInitial rep_ring_hom.
Next Obligation.
  destruct x as [|p|p].
  - simpl.
    rewrite (MonoidHom.ident (spec:=f)).
    reflexivity.
  - simpl.
    induction p.
    + simpl.
      rewrite Pos2Z.inj_xI, Zmult_comm, <- Zplus_diag_eq_mult_2.
      rewrite !(MonoidHom.op (spec:=f)); simpl.
      rewrite IHp.
      rewrite (MonoidHom.ident (spec:=RingHom.mul_monoid_hom f)); simpl.
      now rewrite commute, associative.
    + simpl.
      rewrite Pos2Z.inj_xO, Zmult_comm, <- Zplus_diag_eq_mult_2.
      rewrite !(MonoidHom.op (spec:=f)); simpl.
      now rewrite IHp.
    + simpl.
      now rewrite (MonoidHom.ident (spec:=(RingHom.mul_monoid_hom f))); simpl.
  - simpl.
    induction p.
    + simpl.
      rewrite Pos2Z.neg_xI, Zmult_comm, <- Zplus_diag_eq_mult_2.
      assert (H: Z.neg p + Z.neg p - 1 = (Z.neg p + Z.neg p) + (- 1)).
      {
        now simpl.
      }
      rewrite H.
      rewrite (RingHom.minus (R:=Z_ring) _ 1).
      rewrite !(MonoidHom.op (spec:=f)); simpl.
      rewrite IHp.
      rewrite (MonoidHom.ident (spec:=(RingHom.mul_monoid_hom f))); simpl.
      rewrite !(Group.inv_op (G:=Ring.add_group c)); simpl.
      now rewrite associative.
    + simpl.
      rewrite Pos2Z.neg_xO, Zmult_comm, <- Zplus_diag_eq_mult_2.
      rewrite !(MonoidHom.op (spec:=f)); simpl.
      rewrite IHp.
      now rewrite !(Group.inv_op (G:=Ring.add_group c)); simpl.
    + simpl.
      rewrite (GroupHom.inv (f:=RingHom.add_group_hom f) 1); simpl.
      now rewrite (MonoidHom.ident (f:=(RingHom.mul_monoid_hom f))); simpl.
Qed.      


(** * 例：アーベル群は Z-(左)加群 **)
Section AbelianIsZMod.
  Require Import ZArith.
  Context (M: Abelian).
  Open Scope ring_scope.

  Open Scope group_scope.

  (** M から Z への射 **)
  Fixpoint az_lsm_aux (p: positive)(x: M): M :=
    match p with
    | xI p => az_lsm_aux p x * az_lsm_aux p x * x
    | xO p => az_lsm_aux p x * az_lsm_aux p x
    | xH => x
    end.

  Definition az_lsm (p: Z)(x: M): M :=
    match p with
    | Z0 => 1%group
    | Zpos p => az_lsm_aux p x
    | Zneg p => (az_lsm_aux p x)^-1
    end.

  (** 補題たち **)
  Lemma az_lsm_aux_pos_succ:
    forall p x,
      az_lsm_aux (Pos.succ p) x == az_lsm_aux p x * x.
  Proof.
    intros p x.
    induction p; simpl.
    - rewrite IHp.
      rewrite (Monoid.commute_l (M:=Group.monoid M)); simpl.
      now rewrite !associative.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma az_lsm_aux_pos_add:
    forall p q x,
      az_lsm_aux (p + q) x == (az_lsm_aux p x * az_lsm_aux q x)%group.
  Proof.
    induction p; intros; destruct q; simpl.
    + rewrite Pos.add_carry_spec.
      rewrite az_lsm_aux_pos_succ.
      rewrite <- !associative in *.
      rewrite IHp.
      rewrite <- !(Monoid.commute_l (M:=Group.monoid M) _ x); simpl.
      rewrite (Monoid.commute_l (M:=Group.monoid M) (az_lsm_aux p x) (az_lsm_aux q x)); simpl.
      now rewrite !associative.
    + rewrite IHp.
      rewrite <- !associative in *.
      rewrite (Monoid.commute_l (M:=Group.monoid M) x); simpl.
      rewrite (commute x).
      now rewrite !(Monoid.commute_l (M:=Group.monoid M) (az_lsm_aux p x) (az_lsm_aux q x)); simpl.
    + rewrite az_lsm_aux_pos_succ.
      rewrite <- !associative.
      now rewrite (Monoid.commute_l (M:=Group.monoid M) x); simpl.
    + rewrite IHp.
      rewrite <- !associative.
      now rewrite (Monoid.commute_l (M:=Group.monoid M) _ (az_lsm_aux p x)); simpl.
    + rewrite IHp.
      rewrite <- !associative.
      now rewrite (Monoid.commute_l (M:=Group.monoid M) _ (az_lsm_aux p x)); simpl.
    + reflexivity.
    + rewrite az_lsm_aux_pos_succ.
      rewrite <- !associative.
      now rewrite !(Monoid.commute_l (M:=Group.monoid M) x); simpl.
    + now rewrite (commute x).
    + reflexivity.
  Qed.

  Lemma az_lsm_z_double:
    forall p x,
      az_lsm (Z.double p) x == az_lsm p x * az_lsm p x.
  Proof.
    destruct p; simpl; intros.
    - now rewrite left_identical.
    - reflexivity.
    - now rewrite Group.inv_op.
  Qed.

  Lemma az_lsm_aux_pos_pred_double:
    forall p x,
      az_lsm_aux (Pos.pred_double p) x == az_lsm_aux p x * az_lsm_aux p x * x ^-1.
  Proof.
    induction p; simpl; intros.
    - rewrite (commute _ x).
      rewrite !associative.
      rewrite <- !associative.
      rewrite right_invertible, right_identical.
      now rewrite !(Monoid.commute_l (M:=Group.monoid M) _ x); simpl.
    - rewrite IHp.
      rewrite (commute _ x).
      rewrite <- !associative.
      rewrite !(Monoid.commute_l (M:=Group.monoid M) _ (x^-1)); simpl.
      rewrite !associative.
      now rewrite left_invertible, left_identical.
    - now rewrite <- associative, right_invertible, right_identical.
  Qed.
  
  Lemma az_lsm_z_succ_double:
    forall p x,
      az_lsm (Z.succ_double p) x == az_lsm p x * az_lsm p x * x.
  Proof.
    destruct p; simpl; intros.
    - now rewrite !left_identical.
    - reflexivity.
    - rewrite az_lsm_aux_pos_pred_double.
      rewrite !Group.inv_op, Group.inv_inv.
      now rewrite (commute x).
  Qed.

  Lemma az_lsm_z_pred_double:
    forall p x,
      az_lsm (Z.pred_double p) x == az_lsm p x * az_lsm p x * (x^-1).
  Proof.
    destruct p; simpl; intros.
    - now rewrite !left_identical.
    - now rewrite az_lsm_aux_pos_pred_double.
    - now rewrite !Group.inv_op, commute.
  Qed.

  Lemma az_lsm_z_pos_sub:
    forall p q x,
      az_lsm (Z.pos_sub p q) x == az_lsm_aux p x * az_lsm_aux q x ^-1.
  Proof.
    induction p; intros; simpl; destruct q; simpl.
    - rewrite az_lsm_z_double, IHp.
      rewrite !Group.inv_op.
      rewrite <- !associative.
      rewrite !(Monoid.commute_l (M:=Group.monoid M) _ x); simpl.
      rewrite !(Monoid.commute_l (M:=Group.monoid M) _ (x^-1)); simpl.
      rewrite !associative.
      rewrite left_invertible, left_identical.
      rewrite <- !associative.
      now rewrite !(Monoid.commute_l (M:=Group.monoid M) _ (az_lsm_aux q x^-1)); simpl.
    - rewrite az_lsm_z_succ_double, IHp.
      rewrite !Group.inv_op.
      rewrite <- !associative.
      rewrite !(Monoid.commute_l (M:=Group.monoid M) _ (az_lsm_aux p x)); simpl.
      rewrite (commute x).
      now rewrite !associative.
    - now rewrite <- !associative, right_invertible, right_identical.
    - rewrite az_lsm_z_pred_double, IHp.
      rewrite !Group.inv_op.
      rewrite (commute (x^-1)).
      rewrite <- !associative.
      now rewrite !(Monoid.commute_l (M:=Group.monoid M) _ (az_lsm_aux p x)); simpl.
    - rewrite az_lsm_z_double, IHp.
      rewrite !Group.inv_op.
      rewrite !(Monoid.commute_l (M:=Group.monoid M) _ (az_lsm_aux p x)); simpl.
      now rewrite <- !associative.
    - apply az_lsm_aux_pos_pred_double.
    - rewrite !Group.inv_op.
      rewrite !associative.
      now rewrite right_invertible, left_identical.
    - rewrite az_lsm_aux_pos_pred_double.
      rewrite !Group.inv_op, Group.inv_inv.
      now rewrite (commute x).
    - now rewrite right_invertible.
  Qed.

  Lemma az_lsm_aux_pos_mul:
    forall p q x,
      az_lsm_aux (p * q) x == az_lsm_aux p (az_lsm_aux q x).
  Proof.
    induction p; simpl; intros.
    - rewrite az_lsm_aux_pos_add; simpl.
      now rewrite IHp, commute.
    - now rewrite IHp.
    - reflexivity.
  Qed.

  Lemma az_lsm_aux_inv:
    forall p x,
      (az_lsm_aux p x) ^-1 == (az_lsm_aux p (x^-1)).
  Proof.
    induction p; simpl; intros.
    - now rewrite !Group.inv_op, IHp, commute.
    - now rewrite !Group.inv_op, IHp.
    - reflexivity.
  Qed.

  Lemma az_lsm_aux_mul:
    forall p x y,
      az_lsm_aux p (x * y) == az_lsm_aux p x * az_lsm_aux p y.
  Proof.
    induction p; simpl; intros.
    - rewrite IHp.
      rewrite (Monoid.commute_l (M:=Group.monoid M) _ (az_lsm_aux p x)).
      rewrite <- !associative.
      now rewrite !(Monoid.commute_l (M:=Group.monoid M) _ x).
    - rewrite IHp.
      rewrite (Monoid.commute_l (M:=Group.monoid M) _ (az_lsm_aux p x)).
      now rewrite <- !associative.
    - reflexivity.
  Qed.
      
  (** 本命 **)
  Program Instance Abelian_is_LMod: isLMod az_lsm.
  Next Obligation.
    intros p q HeqZ x y HeqM.
    rewrite <- HeqZ; clear q HeqZ.
    destruct p; simpl; try reflexivity.
    - induction p; simpl.
      + now rewrite IHp, HeqM.
      + now rewrite IHp.
      + now idtac.
    - assert (H: az_lsm_aux p x == az_lsm_aux p y).
      {
        induction p; simpl.
        - now rewrite IHp, HeqM.
        - now rewrite IHp.
        - now idtac.
      }
      now rewrite H.
  Qed.
  Next Obligation.
    destruct a; simpl.
    - now rewrite left_identical.
    - now apply az_lsm_aux_mul.
    - rewrite az_lsm_aux_mul.
      now rewrite Group.inv_op, commute.
  Qed.
  Next Obligation.
    destruct a, b; simpl;
    rewrite ?left_identical, ?right_identical;
    (try reflexivity); rename p0 into q.
    - now rewrite az_lsm_aux_pos_add.
    - now apply az_lsm_z_pos_sub.
    - rewrite commute.
      now apply az_lsm_z_pos_sub.
    - rewrite az_lsm_aux_pos_add.
      now rewrite !Group.inv_op, commute.
  Qed.
  Next Obligation.
    destruct a, b; simpl; (try rename p0 into q); try reflexivity.
    - induction p; simpl.
      + rewrite <- IHp.
        now rewrite !left_identical.
      + rewrite <- IHp.
        now rewrite !left_identical.
      + reflexivity.
    - now apply az_lsm_aux_pos_mul.
    - rewrite az_lsm_aux_pos_mul.
      now rewrite az_lsm_aux_inv.
    - induction p; simpl.
      + rewrite !Group.inv_op, <- IHp.
        now rewrite left_identical, left_invertible.
      + rewrite !Group.inv_op, <- IHp.
        now rewrite !left_identical.
      + now rewrite !Group.inv_id.
    - now rewrite az_lsm_aux_pos_mul.
    - rewrite az_lsm_aux_pos_mul.
      rewrite <- !az_lsm_aux_inv.
      now rewrite Group.inv_inv.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.
End AbelianIsZMod.
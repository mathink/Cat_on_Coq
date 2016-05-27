Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.
From COC.AlgebraicStructures Require Import Binop Monoid Group Ring.

(** * 環のイデアル
部分集合を述語で表現
  **)
Module Ideal.
  Open Scope ring_scope.

  Class spec (R: Ring)(P: R -> Prop) :=
    proof {
        contain_subst: Proper ((==) ==> flip impl) P;
        add_close:
          forall x y,
            P x -> P y -> P (x + y);

        inv_close:
          forall x,
            P x -> P (- x);

        z_close:
          P 0;

        mul_close:
          forall x y,
            P x -> P y -> P (x * y);

        left_mul:
          forall a x,
            P x -> P (a * x);

        right_mul:
          forall a x,
            P x -> P (x * a)
      }.

  Structure type (R: Ring) :=
    make {
        contain: R -> Prop;

        prf: spec contain
      }.

  Module Ex.
    Existing Instance prf.
    Existing Instance contain_subst.

    Notation isIdeal := spec.
    Notation Ideal := type.
    
    Coercion prf: Ideal >-> isIdeal.
    Arguments isIdeal (R P): clear implicits.
  End Ex.
End Ideal.
Export Ideal.Ex.


(** ** 環準同型の核はイデアル **)
Section RingKernel.
  Open Scope ring_scope.
  (* Variable (R S: Ring)(f: RingHom R S). *)
(* Toplevel input, characters 21-58: *)
(* > Variable (R S: Ring)(f: RingHom R S). *)
(* > ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
(* Anomaly: Universe Top.7334 undefined. Please report. *)

  Definition RKernel_spec (R S: Ring)(f: RingHom R S)(x: R) := f x == 0.
  Arguments RKernel_spec R S f x /.
  Definition RKernel (R S: Ring)(f: RingHom R S) := { x | RKernel_spec f x }.

  Program Instance RKernel_is_ideal (R S: Ring)(f: RingHom R S)
    : isIdeal R (RKernel_spec f).
  Next Obligation.
    intros x y Heq P; simpl in *.
    now rewrite Heq.
  Qed.
  Next Obligation.
    now rewrite RingHom.add_op, H, H0, Ring.add_id_l.
  Qed.
  Next Obligation.
    now rewrite RingHom.add_inv, H, (Ring.add_inv_id S).
  Qed.
  Next Obligation.
    now rewrite RingHom.add_ident.
  Qed.
  Next Obligation.
    now rewrite RingHom.mul_op, H, H0, Ring.mul_0_r.
  Qed.
  Next Obligation.
    now rewrite RingHom.mul_op, H, Ring.mul_0_r.
  Qed.
  Next Obligation.
    now rewrite RingHom.mul_op, H, Ring.mul_0_l.
  Qed.

  Definition RKernel_ideal (R S: Ring)(f: RingHom R S) := Ideal.make (RKernel_is_ideal R S f).

End RingKernel.

(** ** イデアルはある環準同型の核 
ただし、 Coq の函数である以上、イデアルに含まれるか否かは決定可能という前提が必要
**)
Definition ideal_RKernel
           `(I: Ideal R)
           (H: forall x, {Ideal.contain I x} + {~Ideal.contain I x})
           (x: R): R :=
  match H x with
  | left _ => 0%rng
  | right _ => x
  end.

Lemma ideal_RKernel_valid:
  forall `(I: Ideal R)(H: forall x, {Ideal.contain I x} + {~Ideal.contain I x})(x: R),
    Ideal.contain I x <-> ideal_RKernel H x == 0%rng.
Proof.
  intros; split; intros H'; unfold ideal_RKernel in *; destruct (H x); try now auto.
  rewrite H'.
  apply Ideal.z_close.
Qed.

(** ** イデアルの商
環 R とそのイデアル I について 'x~y :<=> x-y in I' は同値関係
 **)
Section IdealQuotient.
  Open Scope ring_scope.

  Definition Ideal_equal (R: Ring)(I: Ideal R): R -> R -> Prop :=
    fun x y => Ideal.contain I (x - y).
  Arguments Ideal_equal R I x y /.

  Program Instance Ideal_equiv `(I: Ideal R): Equivalence (Ideal_equal I).
  Next Obligation.
    intros x; simpl; simpl.
    rewrite Ring.add_inv_r.
    apply Ideal.z_close.
  Qed.
  Next Obligation.
    intros x y Heq; simpl in *.
    rewrite <- (Ring.add_inv_inv (y - x)); simpl.
    apply Ideal.inv_close.
    now rewrite (Ring.add_inv_op y), (Ring.add_inv_inv x); simpl.
  Qed.
  Next Obligation.
    intros x y z Hxy Hyz.
    simpl in *.
    rewrite <- (Ring.add_id_l (- z)).
    rewrite <- (Ring.add_inv_l y).
    rewrite !associative.
    rewrite <- (associative (x - y)).
    now apply Ideal.add_close; auto.
  Qed.

  Definition IdealQuotient `(I: Ideal R) := Setoid.make (Ideal_equiv I).
End IdealQuotient.
Arguments Ideal_equal R I x y /.


(** 剰余環を構成する **)
Section QuotientRing.
  Open Scope ring_scope.
  Context `(I: Ideal R).

  (* 演算とかの定義 *)
  Definition IQ_add (x y: IdealQuotient I): IdealQuotient I := x + y.
  Definition IQ_O : IdealQuotient I := 0.
  Definition IQ_minus (x: IdealQuotient I): IdealQuotient I := - x.
  Definition IQ_mul (x y: IdealQuotient I): IdealQuotient I := x * y.
  Definition IQ_I : IdealQuotient I := 1.
    
  Program Instance IQ_add_is_binop: isBinop IQ_add.
  Next Obligation.
    intros x x' Heqx y y' Heqy; simpl in *.
    unfold IQ_add.
    rewrite (Group.inv_op (G:=Ring.g R)); simpl.
    rewrite (commute (- y')), !associative.
    rewrite <- (associative x), (commute y), !associative, <- !associative.
    rewrite associative.
    now apply Ideal.add_close.
  Qed.
  Canonical Structure IQ_add_binop := Binop.make IQ_add_is_binop.

  Program Instance IQ_add_is_monoid: isMonoid IQ_add_binop IQ_O.
  Next Obligation.
    intros x y z; simpl.
    unfold IQ_add.
    rewrite associative, right_invertible.
    now apply Ideal.z_close.
  Qed.
  Next Obligation.
    repeat split.
    - intros x; simpl.
      unfold IQ_add, IQ_O; simpl.
      rewrite left_identical, right_invertible.
      now apply Ideal.z_close.
    - intros x; simpl.
      unfold IQ_add, IQ_O; simpl.
      rewrite right_identical, right_invertible.
      now apply Ideal.z_close.
  Qed.
  Canonical Structure IQ_add_monoid := Monoid.make IQ_add_is_monoid.

  Program Instance IQ_minus_is_map: isMap (X:=IdealQuotient I) IQ_minus.
  Next Obligation.
    intros x y Heq; simpl in *.
    unfold IQ_minus.
    rewrite <- (Group.inv_op (G:=Ring.g R)); simpl.
    apply Ideal.inv_close.
    now rewrite commute.
  Qed.    
  Canonical Structure IQ_minus_map := Map.make IQ_minus_is_map.

  Program Instance IQ_add_is_group: isGroup IQ_add_binop IQ_O IQ_minus_map.
  Next Obligation.
    repeat split.
    - intros x; simpl.
      unfold IQ_add, IQ_minus, IQ_O.
      rewrite left_invertible, right_invertible.
      now apply Ideal.z_close.
    - intros x; simpl.
      unfold IQ_add, IQ_minus, IQ_O.
      rewrite right_invertible, right_invertible.
      now apply Ideal.z_close.
  Qed.
  Canonical Structure IQ_add_group := Group.make IQ_add_is_group.

  Program Instance IQ_add_commute: Commute IQ_add_binop.
  Next Obligation.
    unfold IQ_add.
    rewrite (commute b), right_invertible.
    now apply Ideal.z_close.
  Qed.

  (* Monoid of '*' *)
  Program Instance IQ_mul_is_binop: isBinop IQ_mul.
  Next Obligation.
    intros x x' Heqx y y' Heqy.
    unfold IQ_mul; simpl in *.
    assert (H: x*y - x'*y' == (x - x')*(y - y') + (x - x')*y' + x'*(y - y')).
    {
      rewrite !distributive_l, !distributive_r.
      rewrite Ring.mul_inv_inv, !Ring.mul_inv_r, !Ring.mul_inv_l.
      rewrite <- !associative.
      rewrite 5!(Ring.add_commute_l _ (x'*y)); simpl.
      rewrite (associative (x'*y)).
      rewrite right_invertible, left_identical.
      rewrite 2!(Ring.add_commute_l _ (x*y')); simpl.
      rewrite (associative (x*y')).
      rewrite right_invertible, left_identical.
      rewrite (associative (x'*y')).
      rewrite right_invertible, left_identical.
      reflexivity.
    }
    rewrite H; clear H.
    repeat apply Ideal.add_close; auto.
    - now apply Ideal.mul_close.
    - now apply Ideal.right_mul.
    - now apply Ideal.left_mul.
  Qed.
  Canonical Structure IQ_mul_binop := Binop.make IQ_mul_is_binop.

  Program Instance IQ_mul_is_monoid: isMonoid IQ_mul_binop IQ_I.
  Next Obligation.
    intros x y z; simpl.
    unfold IQ_mul.
    rewrite associative, right_invertible.
    now apply Ideal.z_close.
  Qed.
  Next Obligation.
    repeat split.
    - intros x; simpl.
      unfold IQ_mul, IQ_I; simpl.
      rewrite left_identical, right_invertible.
      now apply Ideal.z_close.
    - intros x; simpl.
      unfold IQ_mul, IQ_I; simpl.
      rewrite right_identical, right_invertible.
      now apply Ideal.z_close.
  Qed.
  Canonical Structure IQ_mul_monoid := Monoid.make IQ_mul_is_monoid.

  (* Ring of '+' & '*' *)
  Program Instance IQ_is_ring: isRing IQ_add_binop IQ_O IQ_minus_map IQ_mul_binop IQ_I.
  Next Obligation.
    split; simpl; intros.
    - unfold IQ_add, IQ_mul.
      rewrite distributive_l.
      rewrite right_invertible.
      now apply Ideal.z_close.
    - unfold IQ_add, IQ_mul.
      rewrite distributive_r.
      rewrite right_invertible.
      now apply Ideal.z_close.
  Qed.
  (* 剰余環の完成 *)
  Canonical Structure IQ_ring := Ring.make IQ_is_ring.
End QuotientRing.
Arguments IQ_add R I x y /.
Arguments IQ_O R I /.
Arguments IQ_minus R I x /.
Arguments IQ_mul R I x y /.
Arguments IQ_I R I /.

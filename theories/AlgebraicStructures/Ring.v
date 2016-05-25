Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.
From COC.AlgebraicStructures Require Import Binop Monoid Group.

(** * 環(Ring)
加法と乗法、二つの演算からなる構造。
加法は群を、乗法はモノイドをなす。
 **)
Module Ring.
  Class spec (R: Setoid)(add: Binop R)(z: R)(inv: Map R R)(mul: Binop R)(e: R) :=
    proof {
        is_add_group:> isGroup add z inv;
        add_commute:> Commute add;
        is_mul_monoid:> isMonoid mul e;

        distributive:> Distributive add mul
      }.

  Structure type :=
    make {
        carrier: Setoid;

        add: Binop carrier;
        z: carrier;
        inv: Map carrier carrier;

        mul: Binop carrier;
        e: carrier;

        prf: spec add z inv mul e
      }.

  Module Ex.
    Existing Instance is_add_group.
    Existing Instance add_commute.
    Existing Instance is_mul_monoid.
    Existing Instance distributive.
    Existing Instance prf.

    Notation isRing := spec.
    Notation Ring := type.

    Coercion is_add_group: isRing >-> isGroup.
    Coercion add_commute: isRing >-> Commute.
    Coercion is_mul_monoid: isRing >-> isMonoid.
    Coercion distributive: isRing >-> Distributive.
    Coercion carrier: Ring >-> Setoid.
    Coercion prf: Ring >-> isRing.

    Delimit Scope ring_scope with rng.

    Notation "x + y" := (add _ x y): ring_scope.
    Notation "x * y" := (mul _ x y): ring_scope.
    Notation "'0'" := (z _): ring_scope.
    Notation "- x" := (inv _ x): ring_scope.
    Notation "x - y" := (add _ x (- y)%rng): ring_scope.
    Notation "'1'" := (e _): ring_scope.
  End Ex.
  Import Ex.

  Definition add_group (R: Ring): Group := Group.make R.
  Definition mul_monoid (R: Ring): Monoid := Monoid.make (is_mul_monoid (spec:=R)).
  
  Definition add_id_l {R: Ring}(x: R) := (@left_identical R (add R) (z R) (is_add_group (spec:=R)) x).
  Definition add_id_r {R: Ring}(x: R) := (@right_identical R (add R) (z R) (is_add_group (spec:=R)) x).
  Definition add_inv_l {R: Ring}(x: R) := (@left_invertible R (add R) (z R) (is_add_group (spec:=R)) (inv R) (is_add_group (spec:=R)) x).
  Definition add_inv_r {R: Ring}(x: R) := (@right_invertible R (add R) (z R) (is_add_group (spec:=R)) (inv R) (is_add_group (spec:=R)) x).
  Definition add_inv_op {R: Ring}(x y: R) :=
    (Group.inv_op (G:=(Ring.add_group R)) x y).
  Definition add_inv_id (R: Ring): (- 0 == 0)%rng
    := (Group.inv_id (add_group R)).
  Definition add_inv_inv {R: Ring}(x: R)
    := (Group.inv_inv (G:=add_group R) x).
  Definition add_commute_l {R: Ring}(x y z: R) := (Monoid.commute_l (M:=Group.monoid (add_group R)) x y z).
  Definition mul_id_l {R: Ring}(x: R) := (@left_identical R (mul R) (e R) (is_mul_monoid (spec:=R)) x).
  Definition mul_id_r {R: Ring}(x: R) := (@right_identical R (mul R) (e R) (is_mul_monoid (spec:=R)) x).

  Section RingProps.
    Variable (R: Ring).
    Open Scope ring_scope.


    Lemma mul_0_l:
      forall (x: R),
        (0 * x == 0)%rng.
    Proof.
      intros.
      assert (H: 0 * x == 0 * x + 0 * x :> R).
      {
        rewrite <- (Ring.add_inv_l 0) at 1.
        rewrite (Ring.add_inv_id R); simpl.
        now rewrite (distributive_r).
      }
      apply symmetry.
      generalize (Monoid.left_op (M:=Group.monoid (Ring.add_group R)) (-(0*x)) H); simpl.
      now rewrite Ring.add_inv_l, associative, Ring.add_inv_l, Ring.add_id_l.
    Qed.
    
    Lemma mul_0_r:
      forall (x: R),
        (x * 0 == 0)%rng.
    Proof.
      intros.
      assert (H: x * 0 == x * 0 + x * 0 :> R).
      {
        rewrite <- (Ring.add_inv_l 0) at 1.
        rewrite (Ring.add_inv_id R); simpl.
        now rewrite (distributive_l).
      }
      apply symmetry.
      generalize (Monoid.left_op (M:=Group.monoid (Ring.add_group R)) (-(x*0)) H); simpl.
      now rewrite Ring.add_inv_l, associative, Ring.add_inv_l, Ring.add_id_l.
    Qed.

    Lemma minus_mul_l:
      forall x: R, (- 1%rng) * x == - x.
    Proof.
      intros x.
      rewrite <- (Ring.add_id_l).
      rewrite <- (Ring.add_inv_l x), <- associative.
      rewrite <- (Ring.mul_id_l x) at 2.
      now rewrite <- distributive_r, Ring.add_inv_r, mul_0_l, Ring.add_id_r.
    Qed.

    Lemma minus_mul_r:
      forall x: R, x * - 1%rng == - x.
    Proof.
      intros x.
      rewrite <- (Ring.add_id_r).
      rewrite <- (Ring.add_inv_r x), associative.
      rewrite <- (Ring.mul_id_r x) at 2.
      now rewrite <- distributive_l, Ring.add_inv_l, mul_0_r, Ring.add_id_l.
    Qed.

    Lemma mul_inv_l:
      forall x y: R,
        (- x) * y == - (x * y).
    Proof.
      intros.
      rewrite <- (Ring.add_id_l).
      rewrite <- (Ring.add_inv_l (x*y)), <- associative.
      now rewrite <- distributive_r, Ring.add_inv_r, mul_0_l, Ring.add_id_r.
    Qed.

    Lemma mul_inv_r:
      forall x y: R,
        x * (- y) == - (x * y).
    Proof.
      intros.
      rewrite <- (Ring.add_id_l).
      rewrite <- (Ring.add_inv_l (x*y)), <- associative.
      now rewrite <- distributive_l, Ring.add_inv_r, mul_0_r, Ring.add_id_r.
    Qed.

    Lemma mul_inv_inv:
      forall x y: R,
        (- x) * (- y) == x * y.
    Proof.
      intros.
      now rewrite mul_inv_l, mul_inv_r, (Ring.add_inv_inv (x*y)).
    Qed.
  End RingProps.
End Ring.
Export Ring.Ex.


(** * 環準同型
加法と乗法それぞれについて準同型
 **)
Module RingHom.
  Open Scope ring_scope.

  Class spec (R S: Ring)(f: Map R S) :=
    proof {
        is_add_group_hom:> isGroupHom (Ring.add_group R) (Ring.add_group S) f;
        is_mul_monoid_hom:> isMonoidHom (Ring.mul_monoid R) (Ring.mul_monoid S) f
      }.

  Class type (R S: Ring) :=
    make {
        map: Map R S;
        prf: spec R S map
      }.

  Module Ex.
    Existing Instance is_add_group_hom.
    Existing Instance is_mul_monoid_hom.
    Existing Instance prf.

    Notation isRingHom := spec.
    Notation RingHom := type.

    Coercion map: RingHom >-> Map.
    Coercion prf: RingHom >-> isRingHom.
    Coercion is_add_group_hom: isRingHom >-> isGroupHom.
    Coercion is_mul_monoid_hom: isRingHom >-> isMonoidHom.
  End Ex.
  Import Ex.
  
  Definition add_group_hom `(f: RingHom R R') := GroupHom.make f.
  Definition mul_monoid_hom `(f: RingHom R R') :=
    MonoidHom.make (is_mul_monoid_hom (spec:=f)).

  Program Canonical Structure compose
          (R S T: Ring)(f: RingHom R S)(g: RingHom S T) :=
    {|
      map := GroupHom.compose (add_group_hom f) (add_group_hom g);
      prf := proof _ _
    |}.
  Next Obligation.
    now apply (MonoidHom.compose (mul_monoid_hom f) (mul_monoid_hom g)).
  Qed.

  Program Canonical Structure id (R: Ring): RingHom R R :=
    {|
      map := GroupHom.id (Ring.add_group R);
      prf := proof _ _
    |}.
  Next Obligation.
    now apply (MonoidHom.id).
  Qed.

  Definition equal {R S: Ring}: relation (RingHom R S) :=
    fun f g => forall x: R, f x == g x.
  Arguments equal {R S} f g /.

  Program Canonical Structure setoid (R S: Ring): Setoid :=
    Setoid.build (@equal R S).
  Next Obligation.
    intros f x;  reflexivity.
  Qed.
  Next Obligation.
    intros f g Heq x.
    generalize (Heq x).
    now symmetry.
  Qed.
  Next Obligation.
    intros f g h Hfg Hgh x.
    rewrite (Hfg x); apply Hgh.
  Qed.

  Open Scope ring_scope.
  Definition add_op `(f: RingHom R R')(x y: R): f (x + y) == f x + f y
    := (MonoidHom.op (f:=GroupHom.monoid_hom (add_group_hom f)) x y).
  Definition add_ident `(f: RingHom R R'): f 0 == 0
    := (MonoidHom.ident (f:=GroupHom.monoid_hom (add_group_hom f))).
  Definition add_inv `(f: RingHom R R')(x: R): f (- x) == - f x
    := (GroupHom.inv (f:=add_group_hom f) x).
  Definition mul_op `(f: RingHom R R')(x y: R): f (x * y) == f x * f y
    := (MonoidHom.op (f:=mul_monoid_hom f) x y).
  Definition mul_ident `(f: RingHom R R'): f 1 == 1
    := (MonoidHom.ident (f:=mul_monoid_hom f)).

  Section RingHomProps.
    Lemma minus:
      forall (R S: Ring)(x y: R)(f: RingHom R S),
        f (x - y) == f x - f y.
    Proof.
      intros; rewrite (MonoidHom.op (f:=GroupHom.monoid_hom (add_group_hom f))); simpl.
      rewrite (GroupHom.inv (f:=add_group_hom f)); simpl.
      reflexivity.
    Qed.
  End RingHomProps.
End RingHom.
Export RingHom.Ex.


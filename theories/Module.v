Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.
Require Import COC.Algebra.

(** * 加群の定義
左、右、双。
 **)
Module Abelian.
  Class spec (G: Group) :=
    proof {
        commute:> Commute (Group.op G)
      }.

  Structure type :=
    make {
        group: Group;
        prf: spec group
      }.

  Module Ex.
    Notation isAbelian := spec.
    Notation Abelian := type.

    Coercion group: Abelian >-> Group.
    Coercion prf: Abelian >-> isAbelian.

    Existing Instance prf.
  End Ex.
End Abelian.
Export Abelian.Ex.
  
(** ** 左加群 **)
Module LMod.
  Open Scope ring_scope.

  Class spec (A: Ring)(M: Abelian)(sm: A -> M -> M) :=
    proof {
        sm_proper:> Proper ((==) ==> (==) ==> (==)) sm;

        distributive_mul_l:
          forall (a: A)(x y: M),
            sm a (x * y)%group == (sm a x * sm a y)%group;

        distributive_add_r:
          forall (a b: A)(x: M),
            sm (a + b) x == (sm a x * sm b x)%group;

        composition:
          forall (a b: A)(x: M),
            sm (a * b) x == sm a (sm b x);

        ident:
          forall (x: M),
            sm 1 x == x
      }.

  Structure type (A: Ring) :=
    make {
        abelian: Abelian;
        sm: A -> abelian -> abelian;

        prf: spec sm
      }.

  Module Ex.
    Notation isLMod := spec.
    Notation LMod := type.

    Coercion abelian: LMod >-> Abelian.
    Coercion prf: LMod >-> isLMod.

    Existing Instance sm_proper.
    Existing Instance prf.
  End Ex.
End LMod.
Export LMod.Ex.

(** ** 右加群 **)
Module RMod.
  Open Scope ring_scope.

  Class spec (A: Ring)(M: Abelian)(sm: M -> A -> M) :=
    proof {
        sm_proper:> Proper ((==) ==> (==) ==> (==)) sm;

        distributive_mul_r:
          forall (x y: M)(a: A),
            sm (x * y)%group a == (sm x a * sm y a)%group;

        distributive_add_l:
          forall (x: M)(a b: A),
            sm x (a + b) == (sm x a * sm x b)%group;

        composition:
          forall (x: M)(a b: A),
            sm x (a * b) == sm (sm x a) b;

        ident:
          forall (x: M),
            sm x 1 == x
      }.

  Structure type (A: Ring) :=
    make {
        abelian: Abelian;
        sm: abelian -> A -> abelian;

        prf: spec sm
      }.

  Module Ex.
    Notation isRMod := spec.
    Notation RMod := type.

    Coercion abelian: RMod >-> Abelian.
    Coercion prf: RMod >-> isRMod.

    Existing Instance sm_proper.
    Existing Instance prf.
  End Ex.
End RMod.
Export RMod.Ex.

(** ** 双加群 **)
Module BiMod.
  Class spec (A B: Ring)(M: Abelian)
        (lsm: A -> M -> M)(rsm: M -> B -> M) :=
    proof {
        lmod:> isLMod lsm;
        rmod:> isRMod rsm;

        assoc:
          forall (a: A)(b: B)(x: M),
            rsm (lsm a x) b == lsm a (rsm x b)
      }.

  Structure type (A B: Ring) :=
    make {
        abelian: Abelian;
        lsm: A -> abelian -> abelian;
        rsm: abelian -> B -> abelian;

        prf: spec lsm rsm
      }.

  Module Ex.
    Notation isBiMod := spec.
    Notation BiMod := type.

    Coercion abelian: BiMod >-> Abelian.
    Coercion lmod: isBiMod >-> isLMod.
    Coercion rmod: isBiMod >-> isRMod.
    Coercion prf: BiMod >-> isBiMod.

    Existing Instance lmod.
    Existing Instance rmod.
    Existing Instance prf.
  End Ex.

End BiMod.
Export BiMod.Ex.


(** * 例：環準同型から双加群を構成する **)
Section BiModFromRingHom.
  Open Scope ring_scope.

  (** 環からアーベル群 **)
  Instance Ring_is_abelian (R: Ring): isAbelian (Ring.add_group R).
  Proof.
    split; simpl.
    apply R.
  Qed.
  Canonical Structure Ring_abelian (R: Ring) := Abelian.make (Ring_is_abelian R).

  (** 環 A, B と環準同型 f を準備する **)
  Context {A B: Ring}(f: RingHom A B).

  Definition RH_lsm (a: A)(b: B) := f a * b.
  Arguments RH_lsm a b /.
  Definition RH_rsm (b: B)(a: A) := b * f a.
  Arguments RH_rsm b a /.

  Program Instance RH_is_lmod: isLMod (M:=Ring_abelian B) RH_lsm.
  Next Obligation.
    intros x x' Heqx y y' Heqy; simpl.
    now rewrite Heqx, Heqy.
  Qed.
  Next Obligation.
    now rewrite distributive_l.
  Qed.
  Next Obligation.
    rewrite (MonoidHom.op (spec:=f)); simpl.
    now rewrite distributive_r.
  Qed.
  Next Obligation.
    rewrite (MonoidHom.op (spec:=(RingHom.mul_monoid_hom f))); simpl.
    now rewrite associative.
  Qed.
  Next Obligation.
    rewrite (MonoidHom.ident (spec:=RingHom.mul_monoid_hom f)); simpl.
    now rewrite left_identical.
  Qed.
    
    
  Program Instance RH_is_rmod: isRMod (M:=Ring_abelian B) RH_rsm.
  Next Obligation.
    intros x x' Heqx y y' Heqy; simpl.
    now rewrite Heqx, Heqy.
  Qed.
  Next Obligation.
    now rewrite distributive_r.
  Qed.
  Next Obligation.
    rewrite (MonoidHom.op (spec:=f)); simpl.
    now rewrite distributive_l.
  Qed.
  Next Obligation.
    rewrite (MonoidHom.op (spec:=(RingHom.mul_monoid_hom f))); simpl.
    now rewrite associative.
  Qed.
  Next Obligation.
    rewrite (MonoidHom.ident (spec:=RingHom.mul_monoid_hom f)); simpl.
    now rewrite right_identical.
  Qed.


  Program Instance RH_is_bimod: isBiMod (M:=Ring_abelian B) RH_lsm RH_rsm.
  Next Obligation.
    now rewrite associative.
  Qed.
  Definition RH_bimod := BiMod.make RH_is_bimod.

End BiModFromRingHom.


(** * 例：可換環では左加群=右加群 **)
(** 可換環の定義 **)
Module CRing.
  Class spec (R: Ring) :=
    proof {
        commute:> Commute (Ring.mul R)
      }.

  Structure type :=
    make {
        rng: Ring;
        prf: spec rng
      }.

  Module Ex.
    Notation isCRing := spec.
    Notation CRing := type.

    Coercion rng: CRing >-> Ring.
    Coercion prf: CRing >-> isCRing.

    Existing Instance prf.
  End Ex.
End CRing.
Export CRing.Ex.


Section LModRModOnCRing.
  Context (A: CRing).
  
  (** ** 左加群は右加群 **)
  Definition rsm_from_lmod (M: LMod A)(x: M)(a: A) := LMod.sm a x.
  Arguments rsm_from_lmod M x a /.
  
  Program Instance LMod_is_rmod (M: LMod A)
    : isRMod (@rsm_from_lmod M).
  Next Obligation.
    intros x x' Heqx y y' Heqy; simpl.
    now rewrite Heqx, Heqy.
  Qed.
  Next Obligation.
    now rewrite LMod.distributive_mul_l.
  Qed.
  Next Obligation.
    now rewrite LMod.distributive_add_r.
  Qed.
  Next Obligation.
    now rewrite commute, LMod.composition.
  Qed.
  Next Obligation.
    now rewrite LMod.ident.
  Qed.

  (** ** 右加群は左加群 **)
  Definition lsm_from_rmod (M: RMod A)(a: A)(x: M) := RMod.sm x a.
  Arguments lsm_from_rmod M a x /.
  
  Program Instance RMod_is_lmod (M: RMod A)
    : isLMod (@lsm_from_rmod M).
  Next Obligation.
    intros x x' Heqx y y' Heqy; simpl.
    now rewrite Heqx, Heqy.
  Qed.
  Next Obligation.
    now rewrite RMod.distributive_mul_r.
  Qed.
  Next Obligation.
    now rewrite RMod.distributive_add_l.
  Qed.
  Next Obligation.
    now rewrite commute, RMod.composition.
  Qed.
  Next Obligation.
    now rewrite RMod.ident.
  Qed.
End LModRModOnCRing.


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
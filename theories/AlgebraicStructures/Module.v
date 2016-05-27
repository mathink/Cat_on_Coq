Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.
From COC.AlgebraicStructures Require Import Binop Monoid Group Ring.

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
  Instance Ring_is_abelian (R: Ring): isAbelian (Ring.g R).
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
    rewrite (MonoidHom.op (spec:=(RingHom.mh f))); simpl.
    now rewrite associative.
  Qed.
  Next Obligation.
    rewrite (MonoidHom.ident (spec:=RingHom.mh f)); simpl.
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
    rewrite (MonoidHom.op (spec:=(RingHom.mh f))); simpl.
    now rewrite associative.
  Qed.
  Next Obligation.
    rewrite (MonoidHom.ident (spec:=RingHom.mh f)); simpl.
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



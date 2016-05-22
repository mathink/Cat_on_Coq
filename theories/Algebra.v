Set Implicit Arguments.
Unset Strict Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.
Notation Setoid_of eq := (@Setoid.make _ eq _).

(** 
このファイルのみを読まれることを想定し、COC における「もの」の定義の方針を以下に記す
- 定義したい構造毎にモジュールを用意し、その中で必要なものを構成する
- 構造の性質は、構成要素についての命題クラス(Class) [spec] として記述する
- 構造は、構成要素と命題クラスの証明をフィールドとして持つ [Structure] [type]
- モジュール内モジュール [Ex] を使ってグローバル用の名前や記法を設定する

以上のルールをどのように運用しているかは実際のコードを見てもらえれば大体わかると思われる
 **)

(** * 二項演算 *)
Module Binop.
  Class spec {X: Setoid}(op: X -> X -> X) :=
    substitute:> Proper ((==) ==> (==) ==> (==)) op.

  Structure type (X: Setoid) :=
    make {
        op: X -> X -> X;
        prf: spec op
      }.

  Notation build op := (@make _ op _).

  Module Ex.
    Notation isBinop := spec.
    Notation Binop := type.

    Coercion op: Binop >-> Funclass.
    Coercion prf: Binop >-> isBinop.

    Existing Instance prf.
  End Ex.

  Import Ex.

  Definition equal {X: Setoid}(f g: Binop X) :=
    forall x y, f x y == g x y.
  Arguments equal X f g /.

  Instance equiv (X: Setoid): Equivalence (@equal X).
  Proof.
    split.
    - now intros f x y.
    - now intros f g Heq x y.
    - now intros f g h Hfg Hgh x y; rewrite (Hfg x y).
  Qed.

  Canonical Structure setoid (X: Setoid):= Setoid.make (equiv X).
End Binop.
Export Binop.Ex.

(** * 二項演算の性質たち  **)
(** ** 結合性 **)
Class Associative `(op: Binop X): Prop :=
  associative:>
    forall (x y z: X), op x (op y z) == op (op x y) z.

(** ** 単位元の存在(左右) **)
Class LIdentical `(op: Binop X)(e: X): Prop :=
  left_identical:> forall x: X, op e x == x.

Class RIdentical `(op: Binop X)(e: X): Prop :=
  right_identical:> forall x: X, op x e == x.

Class Identical `(op: Binop X)(e: X): Prop :=
  {
    identical_l:> LIdentical op e;
    identical_r:> RIdentical op e
  }.
Existing Instance identical_l.
Existing Instance identical_r.
Coercion identical_l: Identical >-> LIdentical.
Coercion identical_r: Identical >-> RIdentical.

(** ** 逆元の存在(左右) **)
Class LInvertible `{Identical X op e}(inv: Map X X): Prop :=
  left_invertible:>
    forall (x: X), op (inv x) x == e.

Class RInvertible `{Identical X op e}(inv: Map X X): Prop :=
  right_invertible:>
    forall (x: X), op x (inv x) == e.

Class Invertible `{Identical X op e}(inv: Map X X): Prop :=
  {
    invertible_l:> LInvertible inv;
    invertible_r:> RInvertible inv
  }.
Coercion invertible_l: Invertible >-> LInvertible.
Coercion invertible_r: Invertible >-> RInvertible.

(** ** 可換性 **)
Class Commute `(op: Binop X): Prop :=
  commute:>
    forall a b, op a b == op b a.

(** ** 分配律 **)
Class Distributive (X: Setoid)(add mul: Binop X) :=
  {
    distributive_l:>
      forall a b c, mul a (add b c) == add (mul a b) (mul a c);

    distributive_r:>
      forall a b c, mul (add a b) c == add (mul a c) (mul b c)
  }.

(** ** 可除性 **)
Class Divisible `(op: Binop X)(divL divR: Binop X): Prop :=
  {
    divisible_l:>
      forall (a b: X), op (divL a b) a == b;
    divisible_r:>
      forall (a b: X), op a (divR a b) == b
  }.

(** 代数構造については以下の方針に従う
- 可能な限り、性質の寄せ集めとして定義する
- 既存の代数構造との関係は別途記述する
 **)

(** * マグマ(Magma)
二項演算を伴うもっともシンプルな代数構造。
これをそのまま使うことはないと思う。
 **)
Module Magma.
  Structure type :=
    make {
        carrier: Setoid;
        op: Binop carrier
      }.

  Module Ex.
    Notation Magma := type.
    Coercion carrier: Magma >-> Setoid.
    Delimit Scope magma_scope with magma.
    Notation "x * y" := (op _ x y) (at level 40, left associativity): magma_scope.
  End Ex.
End Magma.
Export Magma.Ex.

(** * モノイド(Monoid)
比較的シンプル。
結合的で単位元を持つ二項演算を伴うあれ。
 **)
Module Monoid.
  Class spec (M: Setoid)(op: Binop M)(e: M) :=
    proof {
        associative:> Associative op;
        identical:> Identical op e
      }.

  Structure type :=
    make {
        carrier: Setoid;
        op: Binop carrier;
        e: carrier;

        prf: spec op e
      }.

  Definition magma (M: type) := Magma.make (op M).

  Module Ex.
    Existing Instance associative.
    Existing Instance identical.
    Existing Instance prf.

    Notation isMonoid := spec.
    Notation Monoid := type.

    Coercion associative: isMonoid >-> Associative.
    Coercion identical: isMonoid >-> Identical.
    Coercion carrier: Monoid >-> Setoid.
    Coercion prf: Monoid >-> isMonoid.
    Coercion magma: Monoid >-> Magma.

    Delimit Scope monoid_scope with monoid.
    Notation "x * y" := (op _ x y) (at level 40, left associativity): monoid_scope.
    Notation "'1'" := (e _): monoid_scope.
  End Ex.

  Import Ex.
  
  Section MonoidProps.
    Variable (M: Monoid).
    Open Scope monoid_scope.

    Lemma left_op:
      forall x y z: M,
        y == z -> x * y == x * z.
    Proof.
      intros.
      now rewrite H.
    Qed.

    Lemma right_op:
      forall x y z: M,
        x == y -> x * z == y * z.
    Proof.
      intros.
      now rewrite H.
    Qed.

    Lemma commute_l:
      forall `{Commute M (Monoid.op M)}(x y z: M), x * (y * z) == y * (x * z).
    Proof.
      intros; repeat rewrite associative.
      now rewrite (commute x y).
    Qed.
  End MonoidProps.

End Monoid.
Export Monoid.Ex.


(** * 群(Group)
逆元付きのモノイド、として定義。
結合的で単位的な逆元付きのマグマとしてもよい(面倒なのでそうはしない)。
 **)
Module Group.
  Class spec (G: Setoid)(op: Binop G)(e: G)(inv: Map G G) :=
    proof {
        is_monoid:> isMonoid op e;
        invertible:> Invertible inv
      }.

  Structure type :=
    make {
        carrier: Setoid;
        op: Binop carrier;
        e: carrier;
        inv: Map carrier carrier;
        
        prf: spec op e inv
      }.


  Module Ex.
    Existing Instance is_monoid.
    Existing Instance invertible.
    Existing Instance prf.

    Notation isGroup := spec.
    Notation Group := type.

    Coercion is_monoid: isGroup >-> isMonoid.
    Coercion invertible: isGroup >-> Invertible.
    Coercion carrier: Group >-> Setoid.
    Coercion prf: Group >-> isGroup.

    Delimit Scope group_scope with group.

    Notation "x * y" := (op _ x y) (at level 40, left associativity): group_scope.
    Notation "'1'" := (e _): group_scope.
    Notation "x ^-1" := (inv _ x) (at level 20, left associativity): group_scope.
  End Ex.

  Import Ex.
  
  Canonical Structure monoid (G: Group) := Monoid.make G.

  Section GroupProps.

    Variable (G: Group).
    Open Scope group_scope.
    
    Lemma inv_op:
      forall (x y: G),
        (x * y)^-1 == y^-1 * x^-1.
    Proof.
      intros.
      rewrite <- (left_identical ((y^-1 * x^-1))).
      rewrite <- (left_invertible (x * y)).
      repeat rewrite <- associative.
      rewrite (associative y).
      now rewrite right_invertible, left_identical, right_invertible, right_identical.
    Qed.

    Lemma inv_id:
      (1^-1 == 1 :> G)%group.
    Proof.
      intros.
      now rewrite <- (left_identical (1^-1)), right_invertible.
    Qed.  

    Lemma inv_inv:
      forall (x: G), x ^-1 ^-1 == x.
    Proof.
      intros.
      now rewrite <- (left_identical (x^-1^-1)), <- (right_invertible x), <- associative, right_invertible, right_identical.
    Qed.
  End GroupProps.
End Group.
Export Group.Ex.

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

  Canonical Structure add_group (R: Ring): Group := Group.make R.
  Canonical Structure mul_monoid (R: Ring): Monoid := Monoid.make (is_mul_monoid (spec:=R)).
  
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

(** ** 具体例
整数環
 **)
Require Import ZArith.
Open Scope Z_scope.

Canonical Structure positive_setoid := Setoid_of (@eq positive).
Canonical Structure Z_setoid := Setoid_of (@eq Z).
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

(** * 体(Field)
乗法が零元(加法の単位元)以外で群をなす環。
また、加法と乗法の単位元が異なる。
 **)
Module Field.
  Class spec (K: Setoid)(add: Binop K)(z: K)(minus: Map K K)
        (mul: Binop K)(e: K)(inv: Map K K) :=
    proof {
        field_ring:> isRing add z minus mul e; (* [ring] って名前、色々面倒なので [field_ring] にしてある *)

        mul_inv_l: forall x: K, ~ x == z -> mul (inv x) x == e;
        mul_inv_r: forall x: K, ~ x == z -> mul x (inv x) == e;

        zero_neq_one: ~(z == e)
      }.

  Structure type :=
    make {
        carrier: Setoid;
        add: Binop carrier;
        mul: Binop carrier;
        z: carrier;
        e: carrier;
        minus: Map carrier carrier;
        inv: Map carrier carrier;

        prf: spec add z minus mul e inv
      }.

  Module Ex.
    Notation isField := spec.
    Notation Field := type.

    Coercion field_ring: isField >-> isRing.
    Coercion carrier: Field >-> Setoid.
    Coercion prf: Field >-> isField.

    Existing Instance field_ring.
    Existing Instance prf.

    Definition ring_of_field (K: Field): Ring := Ring.make (field_ring (spec:=K)).
    Coercion ring_of_field: Field >-> Ring.
    
    Delimit Scope field_scope with fld.

    Notation "x + y" := (add _ x y): field_scope.
    Notation "x * y" := (mul _ x y): field_scope.
    Notation "'0'" := (z _): field_scope.
    Notation "'1'" := (e _): field_scope.
    Notation "- x" := (minus _ x): field_scope.
    Notation "x ^-1" := (inv _ x) (at level 20, left associativity): field_scope.
    Notation "x - y" := (add _ x (- y)%fld): field_scope.
    Notation "x / y" := (mul _ x (y^-1)%fld): field_scope.
  End Ex.

  Import Ex.

  Definition rng (K: Field) := Ring.make (field_ring (spec:=K)).
End Field.
Export Field.Ex.

(** ** 具体化
有理数からなる体を作る。
 **)
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

(** ** 具体化 
整数環のイデアル
 **)
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

(** これ以降にやること。
各代数構造について準同型を定義する。
 **)

(** * マグマ準同型
二項演算の保存
 **)
Module MagmaHom.
  Open Scope magma_scope.
  
  Class spec (X Y: Magma)(f: Map X Y) :=
    proof {
        sp: forall x y: X, f (x * y) == f x * f y
      }.

  Structure type (X Y: Magma) :=
    make {
        map: Map X Y;
        prf: spec X Y map
      }.

  Module Ex.
    Notation isMagmaHom := spec.
    Notation MagmaHom := type.

    Coercion map: MagmaHom >-> Map.
    Coercion prf: MagmaHom >-> isMagmaHom.

    Existing Instance prf.
  End Ex.
End MagmaHom.
Export MagmaHom.Ex.

(** * モノイド準同型
単位元の保存
 **)
Module MonoidHom.
  Open Scope monoid_scope.
  
  Class spec (M N: Monoid)(f: Map M N) :=
    proof {
        op: forall x y, f (x * y) == f x * f y;
        ident: f 1 == 1
      }.
  
  Class type (M N: Monoid) :=
    make {
        map: Map M N;
        prf: spec M N map
      }.

  Module Ex.
    Notation isMonoidHom := spec.
    Notation MonoidHom := type.

    Coercion map: MonoidHom >-> Map.
    Coercion prf: MonoidHom >-> isMonoidHom.

    Existing Instance prf.
  End Ex.

  Import Ex.

  Program Canonical Structure compose
          (M N L: Monoid)(f: MonoidHom M N)(g: MonoidHom N L) :=
    {|
      map := Map.compose f g;
      prf := proof _ _
    |}.
  Next Obligation.
    now rewrite !op.
  Qed.
  Next Obligation.
    now rewrite !ident.
  Qed.

  Program Canonical Structure id (M: Monoid): MonoidHom M M :=
    {|
      map := Map.id;
      prf := proof _ _
    |}.
  Next Obligation.
    reflexivity.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.

  Definition equal {M N: Monoid}: relation (MonoidHom M N) :=
    fun f g => forall x: M, f x == g x.
  Arguments equal {M N} f g /.

  Program Canonical Structure setoid (M N: Monoid): Setoid :=
    Setoid.build (@equal M N).
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
End MonoidHom.
Export MonoidHom.Ex.


(** * 群準同型
逆元の保存
 **)
Module GroupHom.
  Open Scope group_scope.

  Class spec (G H: Group)(f: Map G H) :=
    proof {
        is_monoid_hom:> isMonoidHom (Group.monoid G) (Group.monoid H) f;
        inv: forall x, f(x^-1) == (f x)^-1
      }.

  Class type (G H: Group) :=
    make {
        map: Map G H;
        prf: spec G H map
      }.

  Module Ex.
    Existing Instance is_monoid_hom.
    Existing Instance prf.

    Notation isGroupHom := spec.
    Notation GroupHom := type.

    Coercion is_monoid_hom: isGroupHom >-> isMonoidHom.
    Coercion map: GroupHom >-> Map.
    Coercion prf: GroupHom >-> isGroupHom.
  End Ex.

  Import Ex.

  Canonical Structure monoid_hom `(f: GroupHom G H) := MonoidHom.make f.

  Program Canonical Structure compose
          (G H K: Group)(f: GroupHom G H)(g: GroupHom H K) :=
    {|
      map := MonoidHom.compose (monoid_hom f) (monoid_hom g);
      prf := proof _ _
    |}.
  Next Obligation.
    now rewrite !inv.
  Qed.

  Program Canonical Structure id (M: Group): GroupHom M M :=
    {|
      map := MonoidHom.id (Group.monoid M);
      prf := proof _ _
    |}.
  Next Obligation.
    reflexivity.
  Qed.

  Definition equal {G H: Group}: relation (GroupHom G H) :=
    fun f g => forall x: G, f x == g x.
  Arguments equal {G H} f g /.

  Program Canonical Structure setoid (G H: Group): Setoid :=
    Setoid.build (@equal G H).
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
End GroupHom.
Export GroupHom.Ex.

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
  
  Canonical Structure add_group_hom `(f: RingHom R R') := GroupHom.make f.
  Canonical Structure mul_monoid_hom `(f: RingHom R R') :=
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

(** ** 具体例：整数から任意の環への準同型 **)
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
(その先の話はまた今度)
 **)
Section IdealQuotient.
  Close Scope Z_scope.
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

(** 
Z/2Z は 0 と 1 (の同値類)からなる剰余環
 **)
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
    rewrite (Group.inv_op (G:=Ring.add_group R)); simpl.
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
    rewrite <- (Group.inv_op (G:=Ring.add_group R)); simpl.
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

(* Z_2Z を環として解釈することができるようになった *)
(* あまり意味はないけど *)
Lemma Z_2Z_add_0:
  forall x: Z_2Z, (x + x == 0)%rng.
Proof.
  simpl.
  intros x; exists x.
  now rewrite Zplus_0_r, Zplus_diag_eq_mult_2.
Qed.

Module FieldHom.
  Open Scope field_scope.

  Class spec (K L: Field)(f: Map K L) :=
    proof {
        is_ring_hom:> isRingHom (Field.rng K) (Field.rng L) f
      }.


  Class type (R S: Field) :=
    make {
        map: Map R S;
        prf: spec R S map
      }.

  Module Ex.
    Existing Instance is_ring_hom.
    Existing Instance prf.

    Notation isFieldHom := spec.
    Notation FieldHom := type.

    Coercion map: FieldHom >-> Map.
    Coercion prf: FieldHom >-> isFieldHom.
    Coercion is_ring_hom: isFieldHom >-> isRingHom.
  End Ex.
  Import Ex.
  
  Definition ring_hom `(f: FieldHom K L) := RingHom.make f.

  Program Canonical Structure compose
          (K L M: Field)(f: FieldHom K L)(g: FieldHom L M) :=
    {|
      map := RingHom.compose (ring_hom f) (ring_hom g);
      prf := proof _
    |}.

  Program Canonical Structure id (K: Field): FieldHom K K :=
    {|
      map := RingHom.id (Field.rng K);
      prf := proof _
    |}.

  Definition equal {K L: Field}: relation (FieldHom K L) :=
    fun f g => forall x: K, f x == g x.
  Arguments equal {K L} f g /.

  Program Canonical Structure setoid (K L: Field): Setoid :=
    Setoid.build (@equal K L).
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
End FieldHom.
Export FieldHom.Ex.

(** * 圏を作る **)
Require Import COC.Category.

(** ** モノイドの圏 Mon **)
Program Canonical Structure Mon: Category :=
  Category.build (@MonoidHom.setoid)
                 (@MonoidHom.compose)
                 (@MonoidHom.id).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl in *.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.

(** ** 群の圏 Grp **)
Program Canonical Structure Grp: Category :=
  Category.build (@GroupHom.setoid)
                 (@GroupHom.compose)
                 (@GroupHom.id).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl in *.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.

(** ** 環の圏 Rng **)
Program Canonical Structure Rng: Category :=
  Category.build (@RingHom.setoid)
                 (@RingHom.compose)
                 (@RingHom.id).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl in *.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.

(** *** かくにん **)
Check rep_ring_hom Q_ring \o{Rng} rep_ring_hom Z_ring.
Eval simpl in (rep_ring_hom Q_ring \o{Rng} rep_ring_hom Z_ring) 3%Z.
Goal
  (rep_ring_hom Q_ring \o{Rng} rep_ring_hom Z_ring) 3%Z == (6#2)%Q.
Proof.
  simpl.
  compute.
  reflexivity.
Qed.

(** *** Z は始対象 **)
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

(** ** 体の圏 Fld **)
Program Canonical Structure Fld: Category :=
  Category.build (@FieldHom.setoid)
                 (@FieldHom.compose)
                 (@FieldHom.id).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl in *.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.
Next Obligation.
  now idtac.
Qed.

  
(** * おまけ(ハイティング代数)
途中。
 **)
Module SemiLattice.
  Class spec (L: Setoid)(op: Binop L) :=
    {
      comm:> Commute op;
      assoc:> Associative op
    }.

  Structure type :=
    {
      carrier: Setoid;
      op: Binop carrier;

      prf: spec op
    }.

  Module Ex.
    Notation isSemiLattice := spec.
    Notation SemiLattice := type.

    Coercion carrier: SemiLattice >-> Setoid.
    Coercion prf: SemiLattice >-> isSemiLattice.

    Existing Instance prf.

    Notation "x + y" := (SemiLattice.op _ x y): semilat_scope.
    Delimit Scope semilat_scope with semilat.
  End Ex.
End SemiLattice.
Export SemiLattice.Ex.

Module Lattice.
  Class spec (L: Setoid)(and: Binop L)(or: Binop L) :=
    {
      and_sl:> isSemiLattice and;
      or_sl:> isSemiLattice or;

      or_absorp:
        forall a b,
          or a (and a b) == a;

      and_absorp:
        forall a b,
          and a (or a b) == a
    }.

  Structure type :=
    {
      carrier: Setoid;
      and: Binop carrier;
      or: Binop carrier;

      prf: spec and or
    }.

  Module Ex.
    Notation isLattice := spec.
    Notation Lattice := type.

    Coercion carrier: Lattice >-> Setoid.
    Coercion prf: Lattice >-> isLattice.

    Existing Instance prf.

    Notation "x /\ y" := (Lattice.and _ x y): cat_scope.
    Notation "x \/ y" := (Lattice.or _ x y): cat_scope.

    Delimit Scope cat_scope with cat.
  End Ex.

  Import Ex.

  Instance or_comm (L: Lattice): Commute (or L)
    := SemiLattice.comm (spec:=or_sl (spec:=L)).
  Instance and_comm (L: Lattice): Commute (and L)
    := SemiLattice.comm (spec:=and_sl (spec:=L)).

  Instance or_assoc (L: Lattice): Associative (or L)
    := SemiLattice.assoc (spec:=or_sl (spec:=L)).
  Instance and_assoc (L: Lattice): Associative (and L)
    := SemiLattice.assoc (spec:=and_sl (spec:=L)).

  Existing Instance or_comm.
  Existing Instance and_comm.
  Open Scope cat_scope.

  Lemma or_idempotent (L: Lattice)(a: L): (a \/ a) == a.
  Proof.
    rewrite <- (and_absorp a a) at 2.
    now rewrite or_absorp.
  Qed.

  Lemma and_idempotent (L: Lattice)(a: L): (a /\ a) == a.
  Proof.
    rewrite <- (or_absorp a a) at 2.
    now rewrite and_absorp.
  Qed.

  Definition le (L: Lattice)(a b: L) := (a /\ b) == a.

  Module ExAppend.
    Notation "a <= b" := (le a b): cat_scope.
  End ExAppend.
End Lattice.
Export Lattice.Ex.
Export Lattice.ExAppend.

Module Hyting.
  Open Scope cat_scope.

  Class spec (L: Lattice)(rpc: forall a b: L, L) :=
    {
      rpc_proper:> Proper ((==) ==> (==) ==> (==)) rpc;
      ump: forall a b: L, Lattice.le (a /\ rpc a b) b;
      max: forall a b x: L,
          (a /\ x) <= b -> x <= (rpc a b)
    }.

  Structure type :=
    {
      L: Lattice;
      rpc: L -> L -> L;

      prf: spec rpc
    }.

  Module Ex.
    Notation isHyting := spec.
    Notation Hyting := type.

    Coercion L: Hyting >-> Lattice.
    Coercion prf: Hyting >-> isHyting.

    Existing Instance prf.
  End Ex.

  Import Ex.

  Goal forall (Hyt: Hyting)(x y: Hyt),
      y <= (rpc x y).
  Proof.
    intros; apply max.
    unfold Lattice.le; intros.
    rewrite <- Lattice.and_assoc.
    now rewrite Lattice.and_idempotent.
  Qed.
End Hyting.
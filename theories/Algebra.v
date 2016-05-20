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

  Definition setoid (X: Setoid):= Setoid.make (equiv X).
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

    Delimit Scope monoid_scope with monoid.
    Notation "x * y" := (op _ x y) (at level 40, left associativity): monoid_scope.
    Notation "'1'" := (e _): monoid_scope.
  End Ex.

End Monoid.
Export Monoid.Ex.

(** * 群(Group)
逆元付きのモノイド、として定義。
結合的で単位的な逆元付きのマグマとしてもよい(面倒なのでそうはしない)。
 **)
Module Group.
  Class spec (G: Setoid)(op: Binop G)(e: G)(inv: Map G G) :=
    proof {
        monoid:> isMonoid op e;
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
    Existing Instance monoid.
    Existing Instance invertible.
    Existing Instance prf.

    Notation isGroup := spec.
    Notation Group := type.

    Coercion monoid: isGroup >-> isMonoid.
    Coercion invertible: isGroup >-> Invertible.
    Coercion carrier: Group >-> Setoid.
    Coercion prf: Group >-> isGroup.

    Delimit Scope group_scope with group.

    Notation "x * y" := (op _ x y) (at level 40, left associativity): group_scope.
    Notation "'1'" := (e _): group_scope.
    Notation "x ^-1" := (inv _ x) (at level 20, left associativity): group_scope.
  End Ex.
End Group.
Export Group.Ex.


(** * 環(Ring)
加法と乗法、二つの演算からなる構造。
加法は群を、乗法はモノイドをなす。
 **)
Module Ring.
  Class spec (R: Setoid)(add: Binop R)(z: R)(inv: Map R R)(mul: Binop R)(e: R) :=
    proof {
        add_group:> isGroup add z inv;
        add_commute:> Commute add;
        mul_monoid:> isMonoid mul e;

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
    Existing Instance add_group.
    Existing Instance add_commute.
    Existing Instance mul_monoid.
    Existing Instance distributive.
    Existing Instance prf.

    Notation isRing := spec.
    Notation Ring := type.

    Coercion add_group: isRing >-> isGroup.
    Coercion add_commute: isRing >-> Commute.
    Coercion mul_monoid: isRing >-> isMonoid.
    Coercion distributive: isRing >-> Distributive.
    Coercion carrier: Ring >-> Setoid.
    Coercion prf: Ring >-> isRing.

    Delimit Scope ring_scope with rng.

    Notation "x + y" := (add _ x y): ring_scope.
    Notation "x * y" := (mul _ x y): ring_scope.
    Notation "'0'" := (z _): ring_scope.
    Notation "x ^-1" := (inv _ x) (at level 20, left associativity): ring_scope.
    Notation "'1'" := (e _): ring_scope.
  End Ex.
  Import Ex.

  Definition add_id_l {R: Ring}(x: R) := (@left_identical R (add R) (z R) (add_group (spec:=R)) x).
  Definition add_id_r {R: Ring}(x: R) := (@right_identical R (add R) (z R) (add_group (spec:=R)) x).
  Definition add_inv_l {R: Ring}(x: R) := (@left_invertible R (add R) (z R) (add_group (spec:=R)) (inv R) (add_group (spec:=R)) x).
  Definition add_inv_r {R: Ring}(x: R) := (@right_invertible R (add R) (z R) (add_group (spec:=R)) (inv R) (add_group (spec:=R)) x).
  Definition mul_id_l {R: Ring}(x: R) := (@left_identical R (mul R) (e R) (mul_monoid (spec:=R)) x).
  Definition mul_id_r {R: Ring}(x: R) := (@right_identical R (mul R) (e R) (mul_monoid (spec:=R)) x).
  
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
    Notation  "- x" := (minus _ x): field_scope.
    Notation  "x ^-1" := (inv _ x) (at level 20, left associativity): field_scope.
    Notation "x - y" := (add _ x (- y)%fld): field_scope.
    Notation "x / y" := (mul _ x y^-1): field_scope.
  End Ex.

  Import Ex.

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
            P x -> P (x^-1);

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
Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.

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

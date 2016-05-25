Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.
From COC.AlgebraicStructures Require Import Binop Monoid.

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
  
  Definition monoid (G: Group) := Monoid.make G.

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

  Definition monoid_hom `(f: GroupHom G H) := MonoidHom.make f.

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

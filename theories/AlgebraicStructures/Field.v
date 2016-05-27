Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.
From COC.AlgebraicStructures Require Import Binop Monoid Group Ring.

(** * 体(Field)
可換環でかつ乗法が零元以外逆元を持ち可換
 **)
Module Field.
  Class spec (K: Setoid)(add: Binop K)(z: K)(minus: Map K K)
        (mul: Binop K)(e: K)(inv: Map K K) :=
    proof {
        field_ring:> isRing add z minus mul e; (* [ring] って名前、色々面倒なので [field_ring] にしてある *)
        add_commute:> Commute add;
        mul_commute:> Commute mul;
        
        mul_inv_e_l: forall x: K, ~ x == z -> mul (inv x) x == e;
        mul_inv_e_r: forall x: K, ~ x == z -> mul x (inv x) == e;

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

  Definition r (K: type) := Ring.make (field_ring (spec:=prf K)).

  Module Ex.
    Notation isField := spec.
    Notation Field := type.

    Coercion field_ring: isField >-> isRing.
    Coercion carrier: Field >-> Setoid.
    Coercion prf: Field >-> isField.
    Coercion r: Field >-> Ring.
    
    Existing Instance field_ring.
    Existing Instance prf.

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

  Section FieldProps.
    Context (K: Field).
    Open Scope field_scope.
    Definition mul_0_l: forall (x: K),(0 * x == 0)
      := Ring.mul_0_l (R:=K).
    Definition mul_0_r: forall (x: K), (x * 0 == 0)
      := Ring.mul_0_r (R:=K).
    Definition minus_mul_l: forall x: K, (- 1%fld) * x == - x
      := Ring.minus_mul_l (R:=K).
    Definition minus_mul_r: forall x: K, x * (- 1%fld) == - x
      := Ring.minus_mul_r (R:=K).
    Definition mul_inv_l: forall x y: K, (- x) * y == - (x * y)
      := Ring.mul_inv_l (R:=K).
    Definition mul_inv_r: forall x y: K, x * (- y) == - (x * y)
      := Ring.mul_inv_r (R:=K).
    Definition mul_inv_inv: forall x y: K, (- x) * (- y) == x * y
      := Ring.mul_inv_inv (R:=K).
  End FieldProps.
End Field.
Export Field.Ex.

(** * 体準同型 **)
Module FieldHom.
  Open Scope field_scope.

  Class spec (K L: Field)(f: Map K L) :=
    proof {
        is_ring_hom:> isRingHom K L f
      }.


  Class type (R S: Field) :=
    make {
        map: Map R S;
        prf: spec R S map
      }.

  Definition rh `(f: type K L) :=
    RingHom.make (is_ring_hom (spec:=prf)).

  Module Ex.
    Notation isFieldHom := spec.
    Notation FieldHom := type.

    Coercion is_ring_hom: isFieldHom >-> isRingHom.
    Coercion map: FieldHom >-> Map.
    Coercion prf: FieldHom >-> isFieldHom.
    Coercion rh : FieldHom >-> RingHom.

    Existing Instance is_ring_hom.
    Existing Instance prf.
  End Ex.
  Import Ex.
  
  Definition ring_hom `(f: FieldHom K L) := RingHom.make f.

  Program Canonical Structure compose
          (K L M: Field)(f: FieldHom K L)(g: FieldHom L M) :=
    {|
      map := RingHom.compose f g;
      prf := proof _
    |}.

  Program Canonical Structure id (K: Field): FieldHom K K :=
    {|
      map := RingHom.id K;
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

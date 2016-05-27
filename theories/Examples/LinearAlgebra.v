Set Implicit Arguments.
Unset Strict Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

From COC Require Import
     Setoid
     AlgebraicStructures.

Module VSpace.

  Open Scope field_scope.

  Class spec (F: Field)(V: Setoid)(add: Binop V)(inv: Map V V)(scalar: F -> V -> V)(zero: V) :=
    proof {
        scalar_proper:> Proper ((==) ==> (==) ==> (==)) scalar;

        add_assoc:> Associative add;
        add_comm:> Commute add;
        add_ident:> Identical add zero;
        add_inv:> Invertible inv;

        distributive_l:
          forall a u v,
            scalar a (add u v) == add (scalar a u) (scalar a v);

        distributive_r:
          forall a b v,
            scalar (a + b) v == add (scalar a v) (scalar b v);

        scalar_assoc:
          forall a b v,
            scalar a (scalar b v) == scalar (a * b) v;

        scalar_unit_l:
          forall v,
            scalar 1 v == v
      }.

  Structure type (F: Field) :=
    make {
        space: Setoid;

        add: Binop space;
        inv: Map space space;
        scalar: F -> space -> space;
        zero: space;
        
        prf: spec add inv scalar zero
      }.

  Check @proof.
  Notation build X add inv scalar zero :=
    (@make _ X add inv scalar zero (@proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ )).

  Module Ex.
    Notation isVSpace := spec.
    Notation VSpace := type.

    Coercion space: VSpace >-> Setoid.
    Coercion prf: VSpace >-> isVSpace.

    Existing Instance add_assoc.
    Existing Instance add_comm.
    Existing Instance add_ident.
    Existing Instance add_inv.
    Existing Instance prf.

    Delimit Scope vspace_scope with vspace.

    Notation "x + y" := (add _ x y): vspace_scope.
    Notation "- x" := (inv _ x): vspace_scope.
    Notation "x - y" := (x + (- y))%vspace: vspace_scope.
    Infix "*" := (scalar): vspace_scope.
    Notation "0" := (zero _): vspace_scope.
  End Ex.

  Import Ex.


  Section VSpaceProps.
    Context (F: Field)(V: VSpace F).

    Open Scope vspace_scope.

    Lemma add_trans_minus_l:
      forall u v w: V,
        u + v == w -> u == w - v.
    Proof.
      intros.
      assert (Heq: u + v == w - v + v).
      {
        now rewrite H, <- associative, left_invertible, right_identical.
      }
      rewrite <- (right_identical u); simpl.
      rewrite <- (right_invertible v), associative.
      rewrite Heq, <- !associative.
      now rewrite right_invertible, right_identical.
    Qed.
    
    Lemma add_trans_minus_r:
      forall u v w: V,
        u + v == w -> v == w - u.
    Proof.
      intros.
      apply add_trans_minus_l.
      now rewrite commute, H.
    Qed.
    
    Lemma add_with_0_l:
      forall u v: V,
        u + v == u -> v == 0.
    Proof.
      intros u v Heq.
      rewrite commute in Heq.
      apply add_trans_minus_l in Heq.
      now rewrite Heq, right_invertible.
    Qed.    

    Lemma add_with_0_r:
      forall u v: V,
        u + v == v -> u == 0.
    Proof.
      intros u v Heq.
      now rewrite commute in Heq; apply add_with_0_l with v.
    Qed.
    
    Lemma scalar_0_l:
      forall (v: V), scalar 0%fld v == 0 :> V.
    Proof.
      intros v.
      apply add_with_0_l with (0%fld * v).
      rewrite <- (left_identical 0%fld) at 3; simpl.
      now rewrite distributive_r; simpl.
    Qed.
  
    Lemma scalar_0_r:
      forall (x: F), scalar x 0 == 0 :> V.
    Proof.
      intros v.
      apply add_with_0_l with (v * 0).
      rewrite <- (left_identical 0) at 3; simpl.
      now rewrite distributive_l; simpl.
    Qed.
  
    Lemma scalar_inv_l:
      forall (x: F)(v: V), scalar (- x)%fld v == - (scalar x v).
    Proof.
      intros x v.
      rewrite <- (left_identical (- (x * v))).
      apply add_trans_minus_l.
      now rewrite <- distributive_r, left_invertible, scalar_0_l.
    Qed.

    Lemma scalar_inv_r:
      forall (x: F)(v: V), scalar x (- v) == - (scalar x v).
    Proof.
      intros x v.
      rewrite <- (left_identical (- (x * v))).
      apply add_trans_minus_l.
      now rewrite <- distributive_l, left_invertible, scalar_0_r.
    Qed.

    Lemma inv_add_inv:
      forall (u v: V), - (u + v) == - u - v.
    Proof.
      intros u v.
      (* u *)
      rewrite <- (left_identical (- u - v)).
      rewrite <- (left_invertible (u + v)).
      rewrite (commute u v), <- !associative.
      rewrite (associative u), right_invertible, left_identical.
      now rewrite right_invertible, right_identical.
    Qed.
  End VSpaceProps.
End VSpace.
Export VSpace.Ex.

Section FieldAsVSpace.
  Context (F: Field).
  Open Scope field_scope.

  Program Definition FieldVSpace: VSpace F :=
    VSpace.build
      F
      (Field.add F)
      (Field.minus F)
      (Field.mul F)
      0.
  Next Obligation.
    now rewrite distributive_l.
  Qed.  
  Next Obligation.
    now rewrite distributive_r.
  Qed.  
  Next Obligation.
    now rewrite associative.
  Qed.
  Next Obligation.
    now rewrite left_identical.
  Qed.
End FieldAsVSpace.

Section FunctionSpace.
  Context (F: Field)(X: Setoid).
  Open Scope field_scope.

  Program Definition function_add: Binop (Map.setoid X F) :=
    Binop.build (fun f g => [ v :-> (f v + g v)]).
  Next Obligation.
    now intros u v Heq; rewrite Heq.
  Qed.
  Next Obligation.
    intros f f' Heqf g g' Heqg; simpl in *; intros v.
    now rewrite Heqf, Heqg.
  Qed.

  Program Definition function_minus: Map (Map.setoid X F) (Map.setoid X F) :=
    [ f v :-> - f v ].
  Next Obligation.
    now intros u v Heq; rewrite Heq.
  Qed.
  Next Obligation.
    intros f f' Heqf; simpl in *; intros v.
    now rewrite Heqf.
  Qed.

  Program Definition FunctionSpace: VSpace F :=
    VSpace.build
      (Map.setoid X F)
      function_add
      function_minus
      (fun x f => [ v :-> x * f v])
      ([ v :-> 0]).
  Next Obligation.
    now intros u v Heq; rewrite Heq.
  Qed.
  Next Obligation.
    now intros u v Heq.
  Qed.
  Next Obligation.
    intros x x' Heqx f f' Heqf; simpl in *; intros v.
    now rewrite Heqx, Heqf.
  Qed.
  Next Obligation.
    intros f g h x; simpl.
    now rewrite associative.
  Qed.
  Next Obligation.
    intros f g x; simpl.
    now rewrite commute.
  Qed.
  Next Obligation.
    split; intros f x; simpl.
    - now rewrite left_identical.
    - now rewrite right_identical.
  Qed.
  Next Obligation.
    split; intros f x; simpl.
    - now rewrite left_invertible.
    - now rewrite right_invertible.
  Qed.
  Next Obligation.
    now rewrite distributive_l.
  Qed.
  Next Obligation.
    now rewrite distributive_r.
  Qed.
  Next Obligation.
    now rewrite associative.
  Qed.
  Next Obligation.
    now rewrite left_identical.
  Qed.

End FunctionSpace.

Module LinearMap.
  Open Scope vspace_scope.

  Class spec (F: Field)(U V: VSpace F)(f: Map U V) :=
    proof {
        preserve_add:
          forall u v: U, f (u + v) == f u + f v;
        preserve_scalar:
          forall x v, f (x * v) == x * f v
      }.

  Structure type (F: Field)(U V: VSpace F) :=
    make {
        map: Map U V;

        prf: spec U V map
      }.

  Notation build map := (@make _ _ _ map (@proof _ _ _ _ _ _)).

  Module Ex.
    Notation isLinearMap := spec.
    Notation LinearMap := type.

    Coercion map: LinearMap >-> Map.
    Coercion prf: LinearMap >-> isLinearMap.

    Existing Instance prf.
  End Ex.

  Import Ex.

  Definition equal (F: Field)(U V: VSpace F): relation (LinearMap U V) :=
    fun f g => forall x, f x == g x.
  Arguments equal {F U V} f g /.

  Program Canonical Structure setoid F U V: Setoid :=
    Setoid.build (@equal F U V).
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

  Program Definition compose F (U V W: VSpace F)(f: LinearMap U V)(g: LinearMap V W)
    : LinearMap U W :=
    LinearMap.build (Map.compose f g).
  Next Obligation.
    now rewrite !preserve_add.
  Qed.
  Next Obligation.
    now rewrite !preserve_scalar.
  Qed.

  Program Definition id F (U: VSpace F): LinearMap U U :=
    LinearMap.build (Map.id ).
  Next Obligation.
    reflexivity.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.
  
End LinearMap.
Export LinearMap.Ex.

Section HomSpace.
  Context (F: Field)(U V: VSpace F).
  Open Scope vspace_scope.
  
  Program Definition linear_map_add (f g: LinearMap U V): LinearMap U V :=
    LinearMap.build ([ v :-> f v + g v]).
  Next Obligation.
    now intros v v' Heqv; rewrite Heqv.
  Qed.
  Next Obligation.
    rewrite !LinearMap.preserve_add.
    rewrite <- associative.
    now rewrite (associative (f v)), (commute (f v)), !associative.
  Qed.
  Next Obligation.
    rewrite !LinearMap.preserve_scalar.
    now rewrite VSpace.distributive_l.
  Qed.

  Program Definition linear_map_add_binop: Binop (LinearMap.setoid U V) :=
    Binop.build linear_map_add.
  Next Obligation.
    now intros f f' Heqf g g' Heqg x; simpl in *; rewrite Heqf, Heqg.
  Qed.
  
  Program Definition linear_map_inv (f: LinearMap U V): LinearMap U V :=
    LinearMap.build ([ v :-> - f v ]).
  Next Obligation.
    now intros v v' Heqv; rewrite Heqv.
  Qed.
  Next Obligation.
    now rewrite LinearMap.preserve_add, VSpace.inv_add_inv.
  Qed.
  Next Obligation.
    rewrite LinearMap.preserve_scalar.
    now rewrite <- VSpace.scalar_inv_r.
  Qed.

  Program Definition linear_map_inv_map: Map (LinearMap.setoid U V) (LinearMap.setoid U V)
    := Map.build linear_map_inv.
  Next Obligation.
    now intros f f' Heqf; simpl in *; intros x; rewrite Heqf.
  Qed.
  
  Program Definition HomSpace: VSpace F :=
    VSpace.build
      (LinearMap.setoid U V)
      linear_map_add_binop
      linear_map_inv_map
      (fun x f => LinearMap.build ([ v :-> x * f v ]))
      (LinearMap.build ([ v :-> 0])).
  Next Obligation.
    now intros v v' Heq; rewrite Heq.
  Qed.
  Next Obligation.
    now rewrite LinearMap.preserve_add, VSpace.distributive_l.
  Qed.
  Next Obligation.
    now rewrite LinearMap.preserve_scalar, !VSpace.scalar_assoc, commute.
  Qed.
  Next Obligation.
    now intros _ _ _.
  Qed.
  Next Obligation.
    now rewrite left_identical.
  Qed.
  Next Obligation.
    now rewrite VSpace.scalar_0_r.
  Qed.
  Next Obligation.
    intros x x' Heqx f f' Heqf v; simpl in *.
    now rewrite Heqx, Heqf.
  Qed.
  Next Obligation.
    intros f g h x; simpl.
    now rewrite associative.
  Qed.
  Next Obligation.
    intros f g x; simpl.
    now rewrite commute.
  Qed.
  Next Obligation.
    split; intros f x; simpl.
    - now rewrite left_identical.
    - now rewrite right_identical.
  Qed.
  Next Obligation.
    split; intros f x; simpl.
    - now rewrite left_invertible.
    - now rewrite right_invertible.
  Qed.
  Next Obligation.
    now rewrite VSpace.distributive_l.
  Qed.
  Next Obligation.
    now rewrite VSpace.distributive_r.
  Qed.
  Next Obligation.
    now rewrite VSpace.scalar_assoc.
  Qed.
  Next Obligation.
    now rewrite VSpace.scalar_unit_l.
  Qed.
End HomSpace.

Section DualSpace.
  Context (F: Field).

  Definition DualSpace (V: VSpace F) := HomSpace V (FieldVSpace F).
  
  Program Definition DualDual_canonical (V: VSpace F)
    : Map V (DualSpace (DualSpace V)) :=
    [ v :-> LinearMap.build ([f :-> f v])].
  Next Obligation.
    now intros f f' Heqf.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.
  Next Obligation.
    reflexivity.
  Qed.
  Next Obligation.
    intros v v' Heqv f; simpl.
    now rewrite Heqv.
  Qed.
End DualSpace.

Require Import COC.Category.

Program Definition VSpaces (F: Field): Category :=
  Category.build (@LinearMap.setoid F)
                 (@LinearMap.compose F)
                 (@LinearMap.id F).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl in *.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  reflexivity.
Qed.


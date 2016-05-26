Set Implicit Arguments.
Unset Strict Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid.

(** * 部分 Setoid
部分構造的なものは全部これをベースにするので、いっそ [Sub] という名前にする。
 **)
Module Sub.
  Class spec (X: Setoid)(P: X -> Prop) :=
    proof {
        contain_subst:> Proper ((==) ==> flip impl) P
      }.

  Structure type (X: Setoid) :=
    make {
        contain: X -> Prop;

        prf: spec X contain
      }.

  Notation build P := (@make _ P (@proof _ _ _)).
  Module Ex.
    Notation isSub := spec.
    Notation Sub := type.

    Coercion contain: Sub >-> Funclass.
    Coercion prf: Sub >-> isSub.

    Existing Instance prf.

    Notation "{ x | P }" := (build (fun x => P)).
  End Ex.

  Import Ex.
  
  Definition include (X: Setoid)(P Q: Sub X) :=
    forall x, P x -> Q x.
  Arguments include X P Q /.

  Program Definition union (X: Setoid)(P Q: Sub X) :=
    { x | P x \/ Q x }.
  Next Obligation.
    now intros x y Heq [Hp | Hq]; [left | right]; rewrite Heq.
  Qed.

  Program Definition intersection (X: Setoid)(P Q: Sub X) :=
    { x | P x /\ Q x }.
  Next Obligation.
    now intros x y Heq [Hp Hq]; split; rewrite Heq.
  Qed.

  Definition equal (X: Setoid): relation (Sub X) :=
    fun P Q => include P Q /\ include Q P.
  Arguments equal X P Q /.

  Program Canonical Structure setoid (X: Setoid) :=
    Setoid.build (@equal X).
  Next Obligation.
    now intros P; simpl; split; auto.
  Qed.
  Next Obligation.
    now intros P Q Heq; split; intros x; apply Heq.
  Qed.
  Next Obligation.
    intros P Q R HeqPQ HeqQR; simpl; split; intros x.
    - now intros Hp; apply HeqQR, HeqPQ.
    - now intros Hr; apply HeqPQ, HeqQR.
  Qed.
End Sub.
Export Sub.Ex.


Require Import COC.AlgebraicStructures.
Module SubMonoid.
  Open Scope monoid_scope.

  Class spec (M: Monoid)(N: Sub M) :=
    proof {
        close_op: forall x y: M, N x -> N y -> N (x * y);
        close_e: N 1
      }.

  Structure type (M: Monoid) :=
    make {
        sub: Sub M;

        prf: spec M sub
      }.

  Module Ex.
    Notation isSubMonoid := spec.
    Notation SubMonoid := type.

    Coercion sub: SubMonoid >-> Sub.
    Coercion prf: SubMonoid >-> isSubMonoid.

    Existing Instance prf.
  End Ex.

End SubMonoid.
Export SubMonoid.Ex.


Module SubGroup.
  Open Scope group_scope.

  Class spec (G: Group)(H: Sub G) :=
    proof {
        close_op: forall x y: G, H x -> H y -> H (x * y);
        close_e: H 1;
        close_inv: forall x, H x -> H (x^-1)
      }.

  Structure type (G: Group) :=
    make {
        sub: Sub G;

        prf: spec G sub
      }.

  Module Ex.
    Notation isSubGroup := spec.
    Notation SubGroup := type.

    Coercion sub: SubGroup >-> Sub.
    Coercion prf: SubGroup >-> isSubGroup.

    Existing Instance prf.
  End Ex.

End SubGroup.
Export SubGroup.Ex.

Program Definition LeftCoset (G: Group)(g: G)(H: SubGroup G): Sub G :=
  { x | H (g^-1 * x)%group }.
Next Obligation.
  now intros x y Heq Hc; rewrite Heq.
Qed.

Program Definition RightCoset (G: Group)(g: G)(H: SubGroup G): Sub G :=
  { x | H (x * g^-1)%group }.
Next Obligation.
  now intros x y Heq Hc; rewrite Heq.
Qed.
  
Module NormalSubGroup.
  Open Scope group_scope.
  
  Class spec (G: Group)(N: SubGroup G) :=
    proof {
        normal: forall g n: G, N n -> N (g * n * g^-1)
      }.

  Structure type (G: Group) :=
    make {
        sub_group: SubGroup G;

        prf: spec sub_group
      }.

  Module Ex.
    Notation isNormalSubGroup := spec.
    Notation NormalSubGroup := type.

    Coercion sub_group: NormalSubGroup >-> SubGroup.
    Coercion prf: NormalSubGroup >-> isNormalSubGroup.

    Existing Instance prf.
  End Ex.

  Import Ex.

  Program Instance from_LRCoset (G: Group)(H: SubGroup G)
          (Heq: forall g, LeftCoset g H == RightCoset g H :> Sub.setoid G)
    : isNormalSubGroup H.
  Next Obligation.
    apply Heq.
    now rewrite associative, left_invertible, left_identical.
  Qed.

  Lemma eq_LRCoset:
    forall (G: Group)(N: NormalSubGroup G)(g: G),
      LeftCoset g N == RightCoset g N :> Sub.setoid G.
  Proof.
    simpl; intros G N g; split; intros x Hc.
    - rewrite <- (left_identical _), <- (right_invertible g).
      rewrite <- associative, (associative _ x), (associative).
      now apply NormalSubGroup.normal.
    - generalize (NormalSubGroup.normal (N:=N) (x ^-1) Hc).
      rewrite associative, left_invertible, left_identical.
      now rewrite Group.inv_inv.
  Qed.
End NormalSubGroup.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Setoid
        COC.Category.

(** 
 ** 色々な積
 **)
Module Prod.
  Record type (X Y: Type): Type := make { fst: X; snd: Y }.

  Module Ex.
    Notation Prod := type.
    Notation "X * Y" := (Prod X Y) (at level 40, left associativity): cat_scope.
    Notation "( x , y )" := (@make _ _ x y): cat_scope.
    Notation "p '.1'" := (@fst _ _ p) (at level 40, left associativity, format "p .1"): cat_scope.
    Notation "p '.2'" := (@snd _ _ p) (at level 40, left associativity, format "p .2"): cat_scope.
  End Ex.
  Import Ex.

  Definition equal {X Y: Setoid}: relation (Prod X Y) :=
    (fun (p q: Prod X Y) =>
       (fst p == fst q)/\(snd p == snd q)).
  Arguments equal {X Y} p q /.
  
  Program Definition setoid (X Y: Setoid) :=
    Setoid.build (@equal X Y).
  Next Obligation.
    intros [x y]; simpl; split; reflexivity.
  Qed.
  Next Obligation.
    intros [x1 y1] [x2 y2] [Heqx Heqy]; split;
    symmetry; assumption.
  Qed.
  Next Obligation.
    intros [x1 y1] [x2 y2] [x3 y3]; simpl.
    intros [Heqx12 Heqy12] [Heqx23 Heqy23]; split.
    - transitivity x2; assumption.
    - transitivity y2; assumption.
  Qed.

  Local Infix "[*]" := setoid (at level 40, left associativity).

  Module fst.
    Lemma substitute:
      forall (X Y: Setoid)(p q: X [*] Y),
        p == q -> fst p == fst q.
    Proof.
      intros X Y [x1 y1] [x2 y2] [Heq _]; auto.
    Qed.
  End fst.
    
  Module snd.
    Lemma substitute:
      forall (X Y: Setoid)(p q: X [*] Y),
        p == q -> snd p == snd q.
    Proof.
      intros X Y [x1 y1] [x2 y2] [_ Heq]; auto.
    Qed.
  End snd.

  Lemma substitute:
    forall (X Y: Setoid)(x1 x2: X)(y1 y2: Y),
      x1 == x2 -> y1 == y2 -> (x1, y1) == (x2, y2) :> X [*] Y.
  Proof.
    intros; simpl.
    split; auto.
  Qed.

  Program Definition map {X Y Z W: Setoid}(f: Map X Z)(g: Map Y W):
    Map (X [*] Y) (Z [*] W) :=
    [ p :-> make (f (fst p)) (g (snd p))].
  Next Obligation.
    intros; intros [x1 y1] [x2 y2]; simpl.
    intros [Heqx Heqy]; split; apply Map.substitute; assumption.
  Qed.

  Definition arr {C D: Category}: Prod C D -> Prod C D -> Type :=
    fun (P Q: Prod C D) =>
      (C (fst P) (fst Q)) [*] (D (snd P) (snd Q)).

  Definition compose
          {C D: Category}(P Q R: Prod C D)
          (f: arr P Q)(g: arr Q R): arr P R :=
    make (fst g \o fst f) (snd g \o snd f).

  Definition id {C D: Category}(P: Prod C D): arr P P :=
    make (Id (fst P)) (Id (snd P)).

  
  
  Program Definition category (C D: Category) :=
    Category.build _
                   (@compose C D)
                   (@id C D).
  Next Obligation.
    revert X Y Z.
    intros [X1 Y1] [X2 Y2] [X3 Y3]; simpl.
    intros [fx fy] [fx' fy'] [Heqfx Heqfy]; simpl in *.
    intros [gx gy] [gx' gy'] [Heqgx Heqgy]; simpl in *; split;
    apply Category.comp_subst; assumption.
  Qed.
  Next Obligation.
    revert X Y Z W f g h.
    intros [X1 Y1] [X2 Y2] [X3 Y3] [X4 Y4]; simpl.
    intros [fx fy] [gx gy] [hx hy]; simpl; split;
    now rewrite Category.comp_assoc.
  Qed.
  Next Obligation.
    revert X Y f.
    now intros [X1 Y1] [X2 Y2] [f g]; simpl in *; split;
    rewrite catC1f.
  Qed.
  Next Obligation.
    revert X Y f.
    now intros [X1 Y1] [X2 Y2] [f g]; simpl in *; split;
    rewrite catCf1.
  Qed.

  Instance isFunctor (C C' D D': Category)(F: Functor C D)(G: Functor C' D')
    : @isFunctor (category C C') (category D D')
                 (fun XY => let (X,Y) := XY in (F X, G Y))
                 (fun XY XY' fg => let (f,g) := fg in (fmap F f, fmap G g)).
  Proof.
    split; simpl.
    - intros [X Y] [X' Y'] [f g] [f' g'] [Heqf Heqg]; simpl in *.
      now rewrite Heqf, Heqg.
    - intros [X1 Y1] [X2 Y2] [X3 Y3] [f1 g1] [f2 g2]; simpl in *.
      now rewrite !fnC.
    - now intros [X Y]; simpl; split; rewrite fn1.
  Qed.

  Program Definition functor (C C' D D': Category)(F: Functor C D)(G: Functor C' D')
    : Functor (category C C') (category D D') :=
    Functor.make (@isFunctor _ _ _ _ F G).

  Module Ex2.
    Infix "[*]" := setoid (at level 40, left associativity): cat_scope.
    Infix "[x]" := category (at level 40, left associativity): cat_scope.
    Notation Bifunctor B C D := (Functor (B [x] C) D).
  End Ex2.
End Prod.
Export Prod.Ex.
Export Prod.Ex2.


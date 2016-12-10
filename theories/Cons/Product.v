(** * Product **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

Class IsProduct (C: Category)(X Y: C)
      (P: C)(pi1: C P X)(pi2: C P Y)
      (univ: forall (Z: C), C Z X -> C Z Y -> C Z P) :=
  {
    product_universality_1:
      forall (Z: C)(p1: C Z X)(p2: C Z Y),
        (p1 == pi1 \o univ Z p1 p2);

    product_universality_2:
      forall (Z: C)(p1: C Z X)(p2: C Z Y),
        (p2 == pi2 \o univ Z p1 p2);
    
    product_uniqueness:
      forall (Z: C)(p1: C Z X)(p2: C Z Y)(u: C Z P),
        (p1 == pi1 \o u) ->
        (p2 == pi2 \o u) ->
        u == univ Z p1 p2
  }.

Structure Product (C: Category)(X Y: C) :=
  {
    product_obj:> C;
    product_proj1: C product_obj X;
    product_proj2: C product_obj Y;

    product_univ: forall (Z: C), C Z X -> C Z Y -> C Z product_obj;

    product_prf:> IsProduct product_proj1 product_proj2 (@product_univ)
  }.
Existing Instance product_prf.

Notation "[ 'Product' P 'by' univ 'with' pi1 , pi2 ]" :=
  (@Build_Product _ _ _ P pi1 pi2 univ _).
Notation "[ 'Product' 'by' univ 'with' pi1 , pi2 ]" :=
  [Product _ by univ with pi1, pi2].

Notation "[ f , g 'to' P ]" := (product_univ P f g).
Notation "pi1_{ P }" := (product_proj1 P) (at level 0, no associativity, format "pi1_{ P }").
Notation "pi2_{ P }" := (product_proj2 P) (at level 0, no associativity, format "pi2_{ P }").

Program Instance product_univ_proper (C: Category)(X Y: C)
        (prod: Product C X Y)
        (Z: C)
  : Proper ((== in C Z X) ==> (== in C Z Y) ==> (==))
           (@product_univ _ _ _ prod Z).
Next Obligation.
  intros f f' Heqf g g' Heqg.
  apply (product_uniqueness (IsProduct:=prod)(p1:=f')(p2:=g')(u:=[f , g to prod])).
  - rewrite <- Heqf.
    now apply (product_universality_1 (IsProduct:=prod) f g).
  - rewrite <- Heqg.
    now apply (product_universality_2 (IsProduct:=prod) f g).
Qed.  

Definition product_map (C: Category)(prod: forall (X Y: C), Product C X Y)
           (X X' Y Y': C)(f: C X Y)(g: C X' Y')
  : C (prod X X') (prod Y Y') :=
  [f \o pi1_{prod X X'} , g \o pi2_{prod X X'} to (prod Y Y')].
Notation "[ f \* g 'with' prod ]" := (product_map prod f g).

Program Instance product_map_proper
        (C: Category)(prod: forall (X Y: C), Product C X Y)
        (X X' Y Y': C)
  : Proper ((==) ==> (==) ==> (==)) (@product_map _ prod X X' Y Y').
Next Obligation.
  intros f f' Heqf g g' Heqg.
  unfold product_map.
  now rewrite Heqf, Heqg.
Qed.

Lemma product_map_compose:
  forall (C: Category)(prod: forall (X Y: C), Product C X Y)
         (X X' Y Y' Z Z': C)
         (f: C X Y)(g: C Y Z)
         (f': C X' Y')(g': C Y' Z'),
    [(g \o f) \* (g' \o f') with prod] ==
    [g \* g' with prod] \o [ f \* f' with prod].
Proof.
  intros.
  unfold product_map.
  symmetry.
  apply (product_uniqueness (IsProduct:=prod Z Z')).
  - rewrite <- cat_comp_assoc.
    rewrite <- (product_universality_1 (IsProduct:=prod Z Z') _ _).
    rewrite !cat_comp_assoc.
    now rewrite <- (product_universality_1 (IsProduct:=prod Y Y') _ _).
  - rewrite <- cat_comp_assoc.
    rewrite <- (product_universality_2 (IsProduct:=prod Z Z') _ _).
    rewrite !cat_comp_assoc.
    now rewrite <- (product_universality_2 (IsProduct:=prod Y Y') _ _).
Qed.

Lemma product_map_id:
  forall (C: Category)(prod: forall (X Y: C), Product C X Y)
         (X X': C),
    [Id X \* Id X' with prod] == Id (prod X X').
Proof.
  intros.
  unfold product_map.
  rewrite !cat_comp_id_cod.
  symmetry.
  now apply (product_uniqueness (IsProduct:=prod X X'));
    rewrite !cat_comp_id_dom.
Qed.

(** Isomorphic **)
Lemma product_isomorphic:
  forall (C: Category)(X Y: C)(P Q: Product C X Y),
    P === Q in C.
Proof.
  intros; simpl; unfold isomorphic.
  exists [pi1_{P}, pi2_{P} to Q], [pi1_{Q}, pi2_{Q} to P]; split.
  - rewrite (product_uniqueness (p1:=pi1_{P})(p2:=pi2_{P})(u:=Id P));
      try now rewrite cat_comp_id_dom.
    apply product_uniqueness.
    + rewrite <- cat_comp_assoc.
      rewrite <- (product_universality_1 (IsProduct:=P)).
      now rewrite <- (product_universality_1 (IsProduct:=Q)).
    + rewrite <- cat_comp_assoc.
      rewrite <- (product_universality_2 (IsProduct:=P)).
      now rewrite <- (product_universality_2 (IsProduct:=Q)).
  - rewrite (product_uniqueness (p1:=pi1_{Q})(p2:=pi2_{Q})(u:=Id Q));
      try now rewrite cat_comp_id_dom.
    apply product_uniqueness.
    + rewrite <- cat_comp_assoc.
      rewrite <- (product_universality_1 (IsProduct:=Q)).
      now rewrite <- (product_universality_1 (IsProduct:=P)).
    + rewrite <- cat_comp_assoc.
      rewrite <- (product_universality_2 (IsProduct:=Q)).
      now rewrite <- (product_universality_2 (IsProduct:=P)).
Qed.


(** Examples **)
Inductive product (A B: Type): Type :=
| pair_of (fst: A)(snd: B).

Definition fst (A B: Type)(p: product A B): A :=
  match p with
  | pair_of a _ => a
  end.

Definition snd (A B: Type)(p: product A B): B :=
  match p with
  | pair_of _ b => b
  end.

Notation "( x , y )" := (pair_of x y) (format "( x ,  y )").

Notation "p .1" := (fst p) (at level 5, left associativity, format "p .1").
Notation "p .2" := (snd p) (at level 5, left associativity, format "p .2").

Program Definition product_of_types (X Y: Type)
  : Product Types X Y :=
  [Product (product X Y) by (fun P f g x => (f x, g x))
   with @fst X Y, @snd X Y].
Next Obligation.
  generalize (H x), (H0 x).
  now destruct (u x); simpl; intros; subst.
Qed.

Program Definition product_setoid (X Y: Setoid): Setoid :=
  [Setoid by `((p.1 == q.1) /\ (p.2 == q.2)) on product X Y].
Next Obligation.
  repeat split; program_simpl; try now auto.
  - now rewrite H.
  - now rewrite H2.
Qed.

Program Instance fst_proper (X Y: Setoid)
  : Proper ((== in product_setoid X Y) ==> (== in X)) (@fst X Y).

Program Instance snd_proper (X Y: Setoid)
  : Proper ((== in product_setoid X Y) ==> (== in Y)) (@snd X Y).

Program Instance pair_of_proper (X Y: Setoid)
  : Proper ((== in X) ==> (== in Y) ==> (== in product_setoid X Y)) (@pair_of X Y).

Program Definition product_of_Setoids (X Y: Setoid)
  : Product Setoids X Y :=
  [Product (product_setoid X Y)
    by (fun P f g => [x :-> (f x, g x)])
   with [Map by @fst X Y],
        [Map by @snd X Y]].
Next Obligation.
  now intros p q Heq; simpl; rewrite Heq.
Qed.

Program Definition product_category (C D: Category): Category :=
  [Category by (fun X Y => product_setoid (C X.1 Y.1) (D X.2 Y.2))
   with (fun X Y Z f g => (g.1 \o f.1, g.2 \o f.2)),
        (fun X => (Id X.1, Id X.2))].
Next Obligation.
  - repeat split; program_simpl; try now auto.
    + now rewrite H, H0.
    + now rewrite H1, H2.
  - now rewrite !cat_comp_assoc.
  - now rewrite !cat_comp_id_dom.
  - now rewrite !cat_comp_id_cod.
Qed.

Program Definition functor_for_product_of_Cat (C D: Category)
        (B: Category)(F: B --> C)(G: B --> D)
  : B --> (product_category C D) :=
  [Functor by f :-> (fmap F f, fmap G f)
   with b :-> (F b, G b)].
Next Obligation.
  - now intros f g Heq; simpl; rewrite Heq.
  - now rewrite !fmap_comp.
  - now rewrite !fmap_id.
Qed.

Program Definition product_of_Cat (C D: Category)
  : Product Cat C D :=
  [Product (product_category C D)
    by (@functor_for_product_of_Cat C D)
   with [Functor by fg :-> fg.1 with XY :-> XY.1],
        [Functor by fg :-> fg.2 with XY :-> XY.2]].
Next Obligation.
  generalize (H _ _ f), (H0 _ _ f); clear H H0; intros H1 H2.
  destruct (fmap u f); simpl in *.
  destruct (u X), (u Y); simpl in *.
  destruct H1, H2.
  now apply hom_eq_def; rewrite H, H0.
Qed.

(** Product as Functor **)
Program Definition Product_1_functor (C: Category)
        (prod: forall X Y: C, Product C X Y)
        (X: C)
  : C --> C :=
  [Functor by (fun (Y Z: C)(g: C Y Z) => [Id _ \* g with prod ])
   with `(prod X Y) ].
Next Obligation.
  - rename X0 into Y, Y into Z.
    intros g g' Heq.
    now rewrite Heq.
  - rename X0 into Y, Y into Z, Z into W.
    now rewrite <- product_map_compose, cat_comp_id_cod.
  - now apply product_map_id.
Qed.

Program Definition Product_2_functor (C: Category)
        (prod: forall X Y: C, Product C X Y)
        (Y: C)
  : C --> C :=
  [Functor by (fun (W X: C)(f: C W X) => [f \* Id _ with prod ])
   with `(prod X Y) ].
Next Obligation.
  - rename X into W, Y0 into X.
    intros f f' Heq.
    now rewrite Heq.
  - rename X into V, Y0 into W, Z into X.
    now rewrite <- product_map_compose, cat_comp_id_dom.
  - now apply product_map_id.
Qed.


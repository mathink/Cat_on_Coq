(** * Exponential **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main COC.Cons.Product.

Class IsExponential
      (C: Category)
      (prod: forall (X Y: C), Product C X Y)
      (Y Z: C)
      (exp: C)(ev: C (prod exp Y) Z)
      (univ: forall (X: C)(g: C (prod X Y) Z), C X exp) :=
  {
    exp_universality:
      forall (X: C)(g: C (prod X Y) Z),
        g == ev \o [univ X g \* Id Y with prod];
    exp_uniqueness:
      forall (X: C)(g: C (prod X Y) Z)(u: C X exp),
        g == ev \o [u \* Id Y with prod] ->
        u == univ X g
  }.

Structure Exponential
          (C: Category)(prod: forall (X Y: C), Product C X Y)
          (Y Z: C) :=
  {
    exp_obj:> C;
    exp_eval: C (prod exp_obj Y) Z;
    exp_univ: forall (X: C), C (prod X Y) Z -> C X exp_obj;

    exp_prf:> IsExponential exp_eval exp_univ
  }.
Existing Instance exp_prf.

Notation "[ 'Exp' exp 'by' univ 'with' eval ]" :=
  (@Build_Exponential _ _ _ _ exp eval univ _).
Notation "[ 'Exp' 'by' univ 'with' eval ]" :=
  [Exp _ by univ with eval].
Notation "[ 'curry' f 'to' exp ]" := (exp_univ exp f) (f at next level).

Program Instance exponential_univ_proper
        (C: Category)
        (prod: forall (X Y: C), Product C X Y)
        (Y Z: C)
        (exp: Exponential prod Y Z)
        (X: C)
  : Proper ((==) ==> (==)) (@exp_univ _ prod _ _ exp X).
Next Obligation.
  intros f g Heq.
  apply (exp_uniqueness (IsExponential:=exp)).
  rewrite <- Heq.
  now apply (exp_universality (IsExponential:=exp)).
Qed.

(** Isomorphic **)
Lemma exponential_isomorphic:
  forall (C: Category)
         (prod: forall (X Y: C), Product C X Y)
         (Y Z: C)(exp exp': Exponential prod Y Z),
    exp === exp' in C.
Proof.
  intros; simpl; unfold isomorphic.
  exists [curry (exp_eval exp) to exp'], [curry (exp_eval exp') to exp]; split.
  - rewrite (exp_uniqueness (g:=exp_eval exp)(u:=Id exp)).
    + apply exp_uniqueness.
      rewrite <- (cat_comp_id_dom (Id Y)), product_map_compose.
      now rewrite <- cat_comp_assoc, <- !exp_universality.
    + now rewrite product_map_id, cat_comp_id_dom.
  - rewrite (exp_uniqueness (g:=exp_eval exp')(u:=Id exp')).
    + apply exp_uniqueness.
      rewrite <- (cat_comp_id_dom (Id Y)), product_map_compose.
      now rewrite <- cat_comp_assoc, <- !exp_universality.
    + now rewrite product_map_id, cat_comp_id_dom.
Qed.

(** Examples **)
Program Definition exponential_of_Setoids (Y Z: Setoids)
  : Exponential (C:=Setoids) product_of_Setoids Y Z :=
  [Exp (Setoids Y Z)
    by (fun (X: Setoid) f => [x :-> [y :-> f (x, y)]])
   with [gy :-> gy.1 gy.2]].
Next Obligation.
  intros [g y] [g' y'] [Heqg Heqy]; simpl in *.
  now rewrite Heqy, Heqg.
Qed.
Next Obligation.
  now intros y y' Heq; rewrite Heq.
Qed.
Next Obligation.
  now intros x x' Heq y; simpl; rewrite Heq.
Qed.
Next Obligation.
  rename g into f, u into g, x0 into y.
  now rewrite (H (x, y)).
Qed.

(** Exp as Functor **)
Program Definition Exponential_functor
        (C: Category)(prod: forall (X Y: C), Product C X Y)
        (exp: forall (Y Z: C), Exponential prod Y Z)
        (X: C)
  : C --> C :=
  [Functor by (fun (Y Z: C)(g: C Y Z) => [curry (g \o exp_eval (exp X Y)) to (exp X Z)]) with `(exp X Y)].
Next Obligation.
  - rename X0 into Y, Y into Z.
    now intros g g' Heq; rewrite Heq.
  - rename X0 into Y, Y into Z, Z into W.
    symmetry.
    apply exp_uniqueness.
    rewrite <- (cat_comp_id_dom (Id X)).
    rewrite product_map_compose.
    rewrite <- cat_comp_assoc.
    rewrite <- (exp_universality (IsExponential:=exp X W)).
    rewrite !cat_comp_assoc.
    now rewrite <- (exp_universality (IsExponential:=exp X Z)).
  - rename X0 into Y.
    symmetry.
    apply exp_uniqueness.
    now rewrite product_map_id, cat_comp_id_cod, cat_comp_id_dom.
Qed.

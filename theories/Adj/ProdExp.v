(** * (- * Y) -| (-)^Y **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Base.Main
        COC.Cons.Product
        COC.Cons.Exponential
        COC.Adj.Adjunction.

Program Definition prod_exp_adjunction
        (C: Category)
        (prod: forall (X Y: C), Product C X Y)
        (exp: forall (Y Z: C), Exponential prod Y Z)
        (Y: C)
  : Product_2_functor prod Y -| Exponential_functor exp Y :=
  [Adj by (fun X Z => [f in C (prod X Y) Z :-> [curry f to exp Y Z]]),
          (fun X Z => [f in C X (exp Y Z) :-> exp_eval (exp Y Z) \o [f \* Id Y with prod]])].
Next Obligation.
  now intros f f' Heq; rewrite Heq.
Qed.
Next Obligation.
  now intros f f' Heq; rewrite Heq.
Qed.
Next Obligation.
  - rename c into X, d into Z.
    now rewrite <- (exp_universality (IsExponential:=exp Y Z)).
  - rename c into X, d into Z.
    symmetry.
    now apply exp_uniqueness.
  - rename c' into W, c into X, d into Z, d' into Z'.
    symmetry.
    apply exp_uniqueness.
    rewrite <- (cat_comp_id_dom (Id Y)) at 2.
    rewrite product_map_compose.
    rewrite <- (cat_comp_assoc _ _ (exp_eval _)), <- exp_universality.
    rewrite !cat_comp_assoc.
    rewrite <- (cat_comp_id_dom (Id Y)) at 2.
    rewrite product_map_compose.
    now rewrite <- (cat_comp_assoc _ _ (exp_eval _)), <- exp_universality.
  - rename c' into W, c into X, d into Z, d' into Z'.
    rewrite !cat_comp_assoc.
    rewrite <- product_map_compose, cat_comp_id_dom.
    rewrite <- (cat_comp_id_dom (Id Y)) at 1.
    rewrite product_map_compose.
    now rewrite <- cat_comp_assoc, <- exp_universality, cat_comp_assoc.
Qed.

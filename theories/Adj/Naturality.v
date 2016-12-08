(** * Adjunction **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main COC.Cons.Product COC.Adj.Adjunction.

(** naturality of adj_lr, adj_rl **)
Program Definition prod_functor (C D C' D': Category)(F: C --> D)(F': C' --> D'): (product_category C C') --> (product_category D D') :=
  [ F \* F' with product_of_Cat].
Notation "[ F 'xF' G ]" := (prod_functor F G).

Program Definition hom_functor (C: Category): (product_category C^op C) --> Setoids :=
  [Functor by fh :-> [ g :-> fh.2 \o{C} g \o{C} fh.1]
   with XY :-> C XY.1 XY.2].
Next Obligation.
  now intros g g' Heq; rewrite Heq.
Qed.
Next Obligation.
  intros f f' [Heqf1 Heqf2] g; simpl.
  - now rewrite Heqf1, Heqf2.
  - now rewrite !cat_comp_assoc.
  - now rewrite cat_comp_id_dom, cat_comp_id_cod.
Qed.
Notation "'HomF' C" := (hom_functor C) (at level 40, no associativity).

Program Definition op_functor (C D: Category)(F: C --> D)
  : C^op --> D^op :=
  [Functor by f :-> fmap F f ].
Next Obligation.
  - now apply fmap_proper.
  - now apply fmap_comp.
  - now apply fmap_id.
Qed.
Notation "F ^opF" := (op_functor F) (at level 0, format "F ^opF").

(** 
#$Hom_D(-,-)\circ F\times Id_D$#
 **)
Definition adj_lrF (C D: Category)(F: C --> D): (product_category C^op D) --> Setoids :=
  hom_functor D \o [F^opF xF (Id D)].

(** 
#$Hom_C(-,-)\circ Id_{C^op}\times G$#
 **)
Definition adj_rlF (C D: Category)(G: D --> C): (product_category C^op D) --> Setoids :=
  hom_functor C \o [(Id C^op) xF G].


Program Definition adj_lr_Natrans
        (C D: Category)(F: C --> D)(G: D --> C)(adj: F -| G)
  : (adj_lrF F) ==> (adj_rlF G):=
  [ cd :=> let (c,d) := cd in adj_lr adj (c:=c)(d:=d)].
Next Obligation.
  now rewrite adj_lr_naturality.
Qed.

Program Definition adj_rl_Natrans
        (C D: Category)(F: C --> D)(G: D --> C)(adj: F -| G)
  : (adj_rlF G) ==> (adj_lrF F):=
  [ cd :=> let (c,d) := cd in adj_rl adj (c:=c)(d:=d)].
Next Obligation.
  now rewrite adj_rl_naturality.
Qed.

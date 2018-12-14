Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Universe Polymorphism.

Require Import COC.Base.Main
        COC.Adj.Main
        COC.Monad.Monad.

Definition adj_mult (C D: Category)(F: C --> D)(G: D --> C)(adj: F -| G)
  : ((G \o F) \o (G \o F)) ==> (G \o F) :=
  (G <o ([ 1 \o * ==> *] \o (adj_counit adj o> F) \o Nassoc)) \o Nassoc_inv.

Program Definition Monad_from_adj
        (C D: Category)(F: C --> D)(G: D --> C)(adj: F -| G) :=
  [Monad by (G \o F), adj_unit adj, adj_mult adj].
Next Obligation.
  - rewrite !fmap_comp, !fmap_id, !cat_comp_id_dom, !cat_comp_id_cod.
    rewrite <- (fmap_comp (fmap F _)).
    rewrite <- (cat_comp_id_cod (_ \o fmap F _)), <- adj_rl_naturality.
    rewrite fmap_id, !cat_comp_id_cod.
    rewrite <- (cat_comp_id_dom (fmap G (adj_rl _ (Id (G (F X)))))) at 2.
    rewrite <- (cat_comp_id_dom (Id (G (F (G (F X)))))).
    rewrite adj_rl_naturality.
    now rewrite fmap_id, !cat_comp_id_dom, fmap_comp.
  - rewrite !fmap_comp, !fmap_id, !cat_comp_id_dom, !cat_comp_id_cod.
    rewrite <- (cat_comp_id_dom (fmap G _ \o _)), cat_comp_assoc.
    rewrite <- adj_lr_naturality, fmap_id, !cat_comp_id_dom.
    now rewrite adj_iso_rl_lr.
  - rewrite !fmap_comp, !fmap_id, !cat_comp_id_dom, !cat_comp_id_cod.
    rewrite <- fmap_comp.
    rewrite <- (cat_comp_id_cod (adj_rl _ _ \o _)).
    rewrite <- adj_rl_naturality, fmap_id, !cat_comp_id_cod.
    now rewrite adj_iso_lr_rl, fmap_id.
Qed.

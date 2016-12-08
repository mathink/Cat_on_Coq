(** * Lan and Colimit **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main COC.Cons.Terminal COC.Limit.Colimit COC.KanExt.Lan.

Program Definition colimit_from_lan
        (C D: Category)
        (F: C --> D)
        (lan: Lan F (ToOne C))
  : Colimit F :=
  [Colimit [Cocone by (lanN lan) to (lanF lan tt)]
    by `(lanU lan (S:=constant_functor One D (c: Cocone F)) [i :=> c i] tt) ].
Next Obligation.
  rewrite (natrans_naturality (IsNatrans:=lanN lan)); simpl.
  now rewrite (fmap_id (F:=lanF lan) tt), cat_comp_id_cod.
Qed.
Next Obligation.
  now rewrite cocone_commute, cat_comp_id_cod.
Qed.
Next Obligation.
  generalize (lan_universality (IsLan:=lan)(S:=[* in One |-> c in D])); simpl.
  intros H; apply H.

  generalize (lan_uniqueness (IsLan:=lan)(S:=[* in One |-> c in D])); simpl.
  intros Huniq; eapply (Huniq _ [x :=> match x with
                                       | tt => u
                                       end
                                   from (lanF lan) to [* in One |-> c in D]]); simpl.
  now apply H.
  Grab Existential Variables.
  split.
  intros [] [] []; simpl.
  now rewrite (fmap_id (F:=lanF lan)), cat_comp_id_dom, cat_comp_id_cod.
Qed.

Program Definition lan_from_colimit
        (C D: Category)
        (F: C --> D)
        (colim: Colimit F)
  : Lan F (ToOne C) :=
  [Lan by (fun S (e: F ==> (S \o ToOne C)) =>
           [ x :=> match x with
                   | tt => colimit_univ colim [Cocone by e to S tt]
                   end])
   with [Functor by f :-> Id colim], [ c in C :=> colim c]].
Next Obligation.
  now rewrite cat_comp_id_dom.
Qed.
Next Obligation.
  now rewrite cocone_commute, cat_comp_id_cod.
Qed.
Next Obligation.
  rewrite (natrans_naturality (IsNatrans:=e)); simpl.
  now rewrite (fmap_id (F:=S) tt), cat_comp_id_cod.
Qed.
Next Obligation.
  destruct X, Y, f.
  now rewrite cat_comp_id_dom, (fmap_id (F:=S) tt), cat_comp_id_cod.
Qed.
Next Obligation.
  generalize (colimit_universality (IsColimit:=colim)); simpl.
  intros H; apply (H [Cocone by e to S tt] X).
  destruct X.
  generalize (colimit_uniqueness (IsColimit:=colim)); intros Huniq.
  now apply (Huniq [Cocone by e to S tt]), H.
Qed.

(** * Lan and Colimit **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main COC.Cons.Terminal COC.Limit.Colimit COC.KanExt.Lan.

Program Definition colimit_from_lan_cone
        (C D: Category)
        (F: C --> D)
        (lan: Lan F (ToOne C))
  : Cocone _ :=
  [Cocone by (lanN lan) to (lanF lan tt)].
Next Obligation.
  rewrite (natrans_naturality (IsNatrans:=lanN lan)); simpl.
  now rewrite (fmap_id (F:=lanF lan) tt), cat_comp_id_cod.
Qed.

Program Definition colimit_from_lan_univ
        (C D: Category)
        (F: C --> D)
        (lan: Lan F (ToOne C))
        (c: Cocone F) :=
  lanU lan (S:=constant_functor One D (c: Cocone F)) [i :=> c i] tt.
Next Obligation.
  now rewrite cocone_commute, cat_comp_id_cod.
Qed.

Program Definition colimit_from_lan
        (C D: Category)
        (F: C --> D)
        (lan: Lan F (ToOne C))
  : Colimit F :=
  [Colimit (colimit_from_lan_cone lan) by colimit_from_lan_univ lan].
Next Obligation.
  generalize (lan_universality (IsLan:=lan)(S:=[* in One |-> c in D])); simpl.
  intros H; apply H.

  generalize (lan_uniqueness (IsLan:=lan)(S:=[* in One |-> c in D])); simpl.
  unfold colimit_from_lan_univ; simpl.
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

Program Definition lan_from_colimit_lanF
        (C D: Category)
        (F: C --> D)
        (colim: Colimit F)
  : One --> D :=
  [Functor by f :-> Id colim].
Next Obligation.
  now rewrite cat_comp_id_dom.
Qed.

Program Definition lan_from_colimit_lanN
        (C D: Category)
        (F: C --> D)
        (colim: Colimit F)
  : F ==> (lan_from_colimit_lanF colim \o ToOne C) :=
  [ c in C :=> colim c].
Next Obligation.
  now rewrite cocone_commute, cat_comp_id_cod.
Qed.

Program Definition lan_from_colimit_univ_cocone
        (C D: Category)
        (F: C --> D)
        (colim: Colimit F)
        (S: One --> D)(e: F ==> (S \o ToOne C)) :=
  [Cocone by e to S tt].
Next Obligation.
  rewrite (natrans_naturality (IsNatrans:=e)); simpl.
  now rewrite (fmap_id (F:=S) tt), cat_comp_id_cod.
Qed.

Program Definition lan_from_colimit_univ
        (C D: Category)
        (F: C --> D)
        (colim: Colimit F)
        (S: One --> D)(e: F ==> (S \o ToOne C))
  : lan_from_colimit_lanF colim ==> S :=
  [ x :=> match x with
          | tt => colimit_univ
                   colim
                   (lan_from_colimit_univ_cocone colim e)
          end].
Next Obligation.
  destruct X, Y, f.
  now rewrite cat_comp_id_dom, (fmap_id (F:=S) tt), cat_comp_id_cod.
Qed.

Program Definition lan_from_colimit
        (C D: Category)
        (F: C --> D)
        (colim: Colimit F)
  : Lan F (ToOne C) :=
  [Lan by lan_from_colimit_univ colim
   with lan_from_colimit_lanF colim,
        lan_from_colimit_lanN colim].
Next Obligation.
  - generalize (colimit_universality (IsColimit:=colim)); simpl.
    now intros H; apply (H [Cocone by e to S tt] X).
  - destruct X.
    generalize (colimit_uniqueness (IsColimit:=colim)); intros Huniq.
    now apply (Huniq [Cocone by e to S tt]), H.
Qed.

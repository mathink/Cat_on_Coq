(** * Ran and Limit **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main COC.Cons.Terminal COC.Limit.Limit COC.KanExt.Ran.

Program Definition limit_from_ran_cone
        (C D: Category)
        (F: C --> D)
        (ran: Ran F (ToOne C))
  : Cone F :=
  [Cone by (ranN ran) from (ranF ran tt)].
Next Obligation.
  rewrite <- (natrans_naturality (IsNatrans:=ranN ran)); simpl.
  now rewrite (fmap_id (F:=ranF ran) tt), cat_comp_id_dom.
Qed.

Program Definition limit_from_ran_univ
        (C D: Category)
        (F: C --> D)
        (ran: Ran F (ToOne C))
        (c: Cone F)
  :=
    ranU ran (S:=[* in One |-> (c: Cone F) in D]) [i :=> c i] tt.
Next Obligation.
  now rewrite cone_commute, cat_comp_id_dom.
Qed.

Program Definition limit_from_ran
        (C D: Category)
        (F: C --> D)
        (ran: Ran F (ToOne C))
  : Limit F :=
  [Limit (limit_from_ran_cone ran)
    by (limit_from_ran_univ ran) ].
Next Obligation.
  generalize (ran_universality (IsRan:=ran)(S:=[* in One |-> c in D ])); simpl.
  intros H; apply H.

  generalize (ran_uniqueness (IsRan:=ran)(S:=[* in One |-> c in D ])); simpl.
  intros Huniq; eapply (Huniq _ [x :=> match x with
                                       | tt => u
                                       end
                                   from [* in One |-> c in D] to (ranF ran)]); simpl.
  now apply H.
  Grab Existential Variables.
  split.
  intros [] [] []; simpl.
  now rewrite (fmap_id (F:=ranF ran)), cat_comp_id_dom, cat_comp_id_cod.
Qed.

Program Definition ran_from_limit_ranF
        (C D: Category)
        (F: C --> D)
        (lim: Limit F)
  : One --> D :=
  [Functor by f :-> Id lim].
Next Obligation.
  now rewrite cat_comp_id_dom.
Qed.

Program Definition ran_from_limit_ranN
        (C D: Category)
        (F: C --> D)
        (lim: Limit F)
  : (ran_from_limit_ranF lim \o ToOne C) ==> F :=
  [ c in C :=> lim c].
Next Obligation.
  now rewrite cone_commute, cat_comp_id_dom.
Qed.

Program Definition ran_from_limit_univ_cone
        (C D: Category)
        (F: C --> D)
        (lim: Limit F)
        (S: One --> D)(e: (S \o ToOne C) ==> F)
  : Cone F :=
  [Cone by e from S tt].
Next Obligation.
  rewrite <- (natrans_naturality (IsNatrans:=e)); simpl.
  now rewrite (fmap_id (F:=S) tt), cat_comp_id_dom.
Qed.

Program Definition ran_from_limit_univ
        (C D: Category)
        (F: C --> D)
        (lim: Limit F)
        (S: One --> D)(e: (S \o ToOne C) ==> F)
  : S ==> ran_from_limit_ranF lim :=
  [ x :=> match x with
          | tt => limit_univ lim (ran_from_limit_univ_cone lim e)
          end].
Next Obligation.
  destruct X, Y, f.
  now rewrite cat_comp_id_cod, (fmap_id (F:=S) tt), cat_comp_id_dom.
Qed.

Program Definition ran_from_limit
        (C D: Category)
        (F: C --> D)
        (lim: Limit F)
  : Ran F (ToOne C) :=
  [Ran by ran_from_limit_univ lim
   with ran_from_limit_ranF lim, ran_from_limit_ranN lim].
Next Obligation.
  - generalize (limit_universality (IsLimit:=lim)); simpl.
    now intros H; apply (H [Cone by e from S tt] X).
  - destruct X.
    generalize (limit_uniqueness (IsLimit:=lim)); intros Huniq.
    now apply (Huniq [Cone by e from S tt]), H.
Qed.

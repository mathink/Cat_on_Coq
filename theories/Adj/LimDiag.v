(** * Colim -| Diag -| Lim **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Base.Main
        COC.Limit.Main
        COC.Adj.Adjunction.

Program Definition Diagonal_functor (J C: Category)
  : C --> (C^J) :=
  [Functor by f :-> [X in J :=> f]
   with X :-> [ * in J |-> X in C ]].
Next Obligation.
  now rewrite cat_comp_id_dom, cat_comp_id_cod.
Qed.

Program Definition Colimit_functor_fmap_cocone (J C: Category)(colim: forall (D: J --> C), Colimit D)(D D': C^J)(S: (C^J) D D') :=
  [Cocone by i :-> (colim D') i \o S i].
Next Obligation.
  rewrite cat_comp_assoc, natrans_naturality.
  rewrite <- cat_comp_assoc.
  now rewrite (cocone_commute (IsCocone:=colim D')).
Qed.

Program Definition Colimit_functor (J C: Category)(colim: forall (D: J --> C), Colimit D)
  : (C^J) --> C :=
  [Functor by (fun D D' S => colimit_univ (colim D) (Colimit_functor_fmap_cocone colim S) )
   with `(colim D)].
Next Obligation.
  - rename X into D, Y into D'.
    intros S T Heq; simpl.
    apply (colimit_uniqueness (IsColimit:=colim D)(c:=[ Cocone by i :-> (colim D') i \o T i])(u:=colimit_univ (colim D) [ Cocone by i :-> (colim D') i \o S i])); simpl.
    intros j; simpl.
    rewrite <- (Heq j).
    now rewrite (colimit_universality (IsColimit:=colim D)[Cocone by i :-> colim D' i \o S i]).

  - rename X into D, Y into D', Z into D''.
    rename f into S, g into T.
    symmetry.
    apply (colimit_uniqueness (IsColimit:=colim D)(c:=[ Cocone by i :-> (colim D'') i \o T i \o S i])).
    simpl; intros i.
    rewrite cat_comp_assoc.
    rewrite (colimit_universality (IsColimit:=colim D)[ Cocone by i :-> (colim D') i \o S i]); simpl.
    rewrite <- cat_comp_assoc.
    rewrite (colimit_universality (IsColimit:=colim D')[ Cocone by i :-> (colim D'') i \o T i]); simpl.
    now rewrite cat_comp_assoc.
  - symmetry.
    rename X into D.
    apply (colimit_uniqueness (IsColimit:=colim D)(c:=[ Cocone by i :-> (colim D) i \o Id (D i)])); simpl.
    intros i.
    now rewrite cat_comp_id_dom, cat_comp_id_cod.
Qed.

Program Definition colimit_diag_adj_lr
        (J C: Category)
        (colim: forall (D: J --> C), Colimit D)(D: J --> C)(c: C)
  : Map (C (Colimit_functor colim D) c)
        ((C^J) D (Diagonal_functor J C c)) :=
  [f :-> [i in J :=> f \o colim D i]].
Next Obligation.
  rename X into i, Y into j, f0 into u.
  rewrite cat_comp_assoc, (cocone_commute (IsCocone:=colim D)).
  now rewrite cat_comp_id_cod.
Qed.
Next Obligation.
  intros f g Heq i; simpl.
  now rewrite Heq.
Qed.

Program Definition colimit_diag_adj_rl_cocone
        (J C: Category)
        (colim: forall (D: J --> C), Colimit D)(D: J --> C)(c: C)
        (g: D ==> Diagonal_functor J C c) :=
  [Cocone by g to c].
Next Obligation.
  rewrite (natrans_naturality (IsNatrans:=g)); simpl.
  now rewrite cat_comp_id_cod.
Qed.

Program Definition colimit_diag_adj_rl
        (J C: Category)
        (colim: forall (D: J --> C), Colimit D)(D: J --> C)(c: C)
  : Map ((C^J) D (Diagonal_functor J C c))
        (C (Colimit_functor colim D) c) :=
  [g :-> colimit_univ (colim D)
     (colimit_diag_adj_rl_cocone colim g)].
Next Obligation.
  intros S T Heq; simpl.
  apply (colimit_uniqueness (IsColimit:=colim D)(c:=[Cocone by T to c])(u:=colimit_univ (colim D) [Cocone by S to c])); simpl.
  intros i.
  rewrite <- (Heq i).
  now rewrite (colimit_universality (IsColimit:=colim D) [Cocone by S to c]).
Qed.

Program Definition colimit_diag_adjunction
        (J C: Category)
        (colim: forall (D: J --> C), Colimit D)
  : Colimit_functor colim -| Diagonal_functor J C :=
  [Adj by colimit_diag_adj_lr colim,
          colimit_diag_adj_rl colim].
Next Obligation.
  - symmetry.
    now apply (colimit_uniqueness (IsColimit:=colim c)(c:=[Cocone by i :-> f \o (colim c) i])); simpl.
  - now rewrite (colimit_universality (IsColimit:=colim c) [Cocone by g to d]).
  - rewrite !cat_comp_assoc.
    now rewrite (colimit_universality (IsColimit:=colim c')[Cocone by i :-> (colim c) i \o f i]).
Qed.

Program Definition Limit_functor_fmap_cone (J C: Category)(lim: forall (D: J --> C), Limit D)(D D': C^J)(S: D ==> D') :=
  [Cone by i :-> S i \o (lim D) i].
Next Obligation.
  rewrite <- cat_comp_assoc, <- natrans_naturality.
  rewrite cat_comp_assoc.
  now rewrite (cone_commute (IsCone:=lim D)).
Qed.

Program Definition Limit_functor (J C: Category)(lim: forall (D: J --> C), Limit D)
  : (C^J) --> C :=
  [Functor by (fun D D' S => limit_univ (lim D') (Limit_functor_fmap_cone lim S)) with `(lim D)].
Next Obligation.
  - rename X into D, Y into D'.
    intros S T Heq; simpl.
    apply (limit_uniqueness (IsLimit:=lim D')(c:=[ Cone by i :-> T i \o (lim D) i])(u:=limit_univ (lim D') [ Cone by i :-> S i \o (lim D) i])); simpl.
    intros j; simpl.
    rewrite <- (Heq j).
    now rewrite (limit_universality (IsLimit:=lim D')[Cone by i :-> S i \o lim D i]).
  - rename X into D, Y into D', Z into D''.
    rename f into S, g into T.
    symmetry.
    apply (limit_uniqueness (IsLimit:=lim D'')(c:=[ Cone by i :-> (T i \o S i) \o (lim D i)])).
    simpl; intros i.
    rewrite <- cat_comp_assoc.
    rewrite (limit_universality (IsLimit:=lim D'')[ Cone by i :-> T i \o (lim D') i]); simpl.
    rewrite cat_comp_assoc.
    rewrite (limit_universality (IsLimit:=lim D')[ Cone by i :-> S i \o (lim D) i]); simpl.
    now rewrite cat_comp_assoc.
  - symmetry.
    rename X into D.
    apply (limit_uniqueness (IsLimit:=lim D)(c:=[ Cone by i :-> Id (D i) \o (lim D) i])); simpl.
    intros i.
    now rewrite cat_comp_id_dom, cat_comp_id_cod.
Qed.

Program Definition diag_limit_adjunction_lr_cone
        (J C: Category)
        (lim: forall (D: J --> C), Limit D)
        (c: C)(D: J --> C)(g: Diagonal_functor J C c ==> D) :=
  [Cone by g from c].
Next Obligation.
  rewrite <- (natrans_naturality (IsNatrans:=g)); simpl.
  now rewrite cat_comp_id_dom.
Qed.

Program Definition diag_limit_adjunction_lr
        (J C: Category)
        (lim: forall (D: J --> C), Limit D)
        (c: C)(D: J --> C)
  : Map ((C^J) (Diagonal_functor J C c) D)
        (C c (Limit_functor lim D)) :=
  [g :-> limit_univ (lim D) (diag_limit_adjunction_lr_cone lim g)].
Next Obligation.
  intros S T Heq; simpl.
  apply (limit_uniqueness (IsLimit:=lim D)(c:=[Cone by T from c])(u:=limit_univ (lim D) [Cone by S from c])); simpl.
  intros i.
  rewrite <- (Heq i).
  now rewrite (limit_universality (IsLimit:=lim D) [Cone by S from c]).
Qed.

Program Definition diag_limit_adjunction_rl
        (J C: Category)
        (lim: forall (D: J --> C), Limit D)
        (c: C)(D: J --> C)
  : Map (C c (Limit_functor lim D))
        ((C^J) (Diagonal_functor J C c) D) :=
  [f :-> [i in J :=> lim D i \o f]].
Next Obligation.
  rename X into i, Y into j, f0 into u.
  rewrite <- cat_comp_assoc, (cone_commute (IsCone:=lim D)).
  now rewrite cat_comp_id_dom.
Qed.
Next Obligation.
  intros f g Heq i; simpl.
  now rewrite Heq.
Qed.

Program Definition diag_limit_adjunction
        (J C: Category)
        (lim: forall (D: J --> C), Limit D)
  : Diagonal_functor J C -| Limit_functor lim :=
  [Adj by diag_limit_adjunction_lr lim,
          diag_limit_adjunction_rl lim].
Next Obligation.
  - now rewrite (limit_universality (IsLimit:=lim d)[Cone by f from c]).
  - symmetry.
    now apply (limit_uniqueness (IsLimit:=lim d)(c:=[Cone by i :-> (lim d) i \o g])); simpl.
  - rename d into D, d' into D', g into S, h into T.
    symmetry.
    apply (limit_uniqueness (IsLimit:=lim D')(c:=[ Cone by X :-> S X \o T X \o f])); simpl.
    intros i.
    rewrite <- !cat_comp_assoc.
    apply cat_comp_proper; try now idtac.
    rewrite (limit_universality (IsLimit:=lim D')[ Cone by i :-> S i \o (lim D) i]); simpl.
    rewrite cat_comp_assoc.
    now rewrite (limit_universality (IsLimit:=lim D) [ Cone by T from c]); simpl.
Qed.

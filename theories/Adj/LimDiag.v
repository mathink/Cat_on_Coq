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

Program Definition Colimit_functor (J C: Category)(colim: forall (D: J --> C), Colimit D)
  : (C^J) --> C :=
  [Functor by (fun D D' S => colimit_univ (colim D) [Cocone by i :-> (colim D') i \o S i] )
   with `(colim D)].
Next Obligation.
  rewrite cat_comp_assoc, natrans_naturality.
  rewrite <- cat_comp_assoc.
  now rewrite (cocone_commute (IsCocone:=colim D')).
Qed.
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

Program Definition colimit_diag_adjunction
        (J C: Category)
        (colim: forall (D: J --> C), Colimit D)
  : Colimit_functor colim -| Diagonal_functor J C :=
  [Adj by (fun D c => [f :-> [i in J :=> f \o colim D i]]),
          (fun D c => [g :-> colimit_univ (colim D) [Cocone by g to c]])].
Next Obligation.
  rename X into i, Y into j, f0 into u.
  rewrite cat_comp_assoc, (cocone_commute (IsCocone:=colim D)).
  now rewrite cat_comp_id_cod.
Qed.
Next Obligation.
  intros f g Heq i; simpl.
  now rewrite Heq.
Qed.
Next Obligation.
  rewrite (natrans_naturality (IsNatrans:=g)); simpl.
  now rewrite cat_comp_id_cod.
Qed.
Next Obligation.
  intros S T Heq; simpl.
  apply (colimit_uniqueness (IsColimit:=colim D)(c:=[Cocone by T to c])(u:=colimit_univ (colim D) [Cocone by S to c])); simpl.
  intros i.
  rewrite <- (Heq i).
  now rewrite (colimit_universality (IsColimit:=colim D) [Cocone by S to c]).
Qed.
Next Obligation.
  - symmetry.
    now apply (colimit_uniqueness (IsColimit:=colim c)(c:=[Cocone by i :-> f \o (colim c) i])); simpl.
  - now rewrite (colimit_universality (IsColimit:=colim c) [Cocone by g to d]).
  - rewrite !cat_comp_assoc.
    now rewrite (colimit_universality (IsColimit:=colim c')[Cocone by i :-> (colim c) i \o f i]).
  - rename c into D, c' into D', d into c, d' into c', f into S, g into f, h into T.
    symmetry.
    apply (colimit_uniqueness (IsColimit:=colim D')(c:=[ Cocone by X :-> f \o T X \o S X])); simpl.
    intros i.
    rewrite cat_comp_assoc.
    apply cat_comp_proper; try now idtac.
    rewrite cat_comp_assoc.
    rewrite (colimit_universality (IsColimit:=colim D')[ Cocone by i :-> (colim D) i \o S i]); simpl.
    rewrite <- cat_comp_assoc.
    now rewrite (colimit_universality (IsColimit:=colim D) [ Cocone by T to c]); simpl.
Qed.


Program Definition Limit_functor (J C: Category)(lim: forall (D: J --> C), Limit D)
  : (C^J) --> C :=
  [Functor by (fun D D' S => limit_univ (lim D') [Cone by i :-> S i \o (lim D) i] )
   with `(lim D)].
Next Obligation.
  rewrite <- cat_comp_assoc, <- natrans_naturality.
  rewrite cat_comp_assoc.
  now rewrite (cone_commute (IsCone:=lim D)).
Qed.
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

Program Definition diag_limit_adjunction
        (J C: Category)
        (lim: forall (D: J --> C), Limit D)
  : Diagonal_functor J C -| Limit_functor lim :=
  [Adj by (fun c D => [g :-> limit_univ (lim D) [Cone by g from c]]),
          (fun c D => [f :-> [i in J :=> lim D i \o f]])].
Next Obligation.
  rewrite <- (natrans_naturality (IsNatrans:=g)); simpl.
  now rewrite cat_comp_id_dom.
Qed.
Next Obligation.
  intros S T Heq; simpl.
  apply (limit_uniqueness (IsLimit:=lim D)(c:=[Cone by T from c])(u:=limit_univ (lim D) [Cone by S from c])); simpl.
  intros i.
  rewrite <- (Heq i).
  now rewrite (limit_universality (IsLimit:=lim D) [Cone by S from c]).
Qed.
Next Obligation.
  rename X into i, Y into j, f0 into u.
  rewrite <- cat_comp_assoc, (cone_commute (IsCone:=lim D)).
  now rewrite cat_comp_id_dom.
Qed.
Next Obligation.
  intros f g Heq i; simpl.
  now rewrite Heq.
Qed.
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
  - rewrite <- !cat_comp_assoc.
    now rewrite (limit_universality (IsLimit:=lim d')[Cone by i :-> g i \o (lim d) i]).
Qed.

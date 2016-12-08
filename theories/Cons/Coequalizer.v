(** * Coequalizer **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

Class IsCoequalizer (C: Category)(X Y: C)(f g: C X Y)
      (Coeq: C)
      (coeq: C Y Coeq)
      (univ: forall {Z: C}{h: C Y Z},
          h \o f == h \o g -> C Coeq Z) :=
  {
    coequalize: coeq \o f == coeq \o g;

    coequalizer_universality: forall Z (h: C Y Z)(Heq: h \o f == h \o g),
        (univ Heq) \o coeq == h;

    coequalizer_uniqueness: forall Z (h: C Y Z)(Heq: h \o f == h \o g)(u: C Coeq Z),
          u \o coeq == h -> u == univ Heq
  }.

Structure Coequalizer (C: Category)(X Y: C)(f g: C X Y) :=
  {
    coequalizer_obj: C;
    coequalizer_map:> C Y coequalizer_obj;
    coequalizer_univ: forall (Z: C)(h:C Y Z), h \o f == h \o g -> C coequalizer_obj Z;

    coequalizer_prf:> IsCoequalizer coequalizer_map coequalizer_univ
  }.
Existing Instance coequalizer_prf.

Notation "[ 'Coequalizer' 'of' f , g 'by' univ 'with' map 'to' Coeq 'in' C ]" :=
  (@Build_Coequalizer C _ _ f g Coeq map univ _).
Notation "[ 'Coequalizer' 'of' f , g 'by' univ 'with' map ]" :=
  [Coequalizer of f,g by univ with map to _ in _].
Notation "[ 'Coequalizer' 'by' univ 'with' map ]" :=
  [Coequalizer of _,_ by univ with map].
Notation "[ 'Coequalizer' 'by' univ ]" := [Coequalizer by univ with _].

Lemma coequalizer_univ_subst
      (C: Category)(X Y: C)(f g: C X Y)
      (coeq: Coequalizer f g)
      (Z: C)(h h': C Y Z)
      (Heq: h \o f == h \o g)
      (Heq': h' \o f == h' \o g):
  h == h' -> 
  coequalizer_univ coeq Heq == coequalizer_univ coeq Heq'.
Proof.
  intros Heqh.
  apply coequalizer_uniqueness; symmetry; rewrite <- Heqh.
  now rewrite coequalizer_universality.
Qed.

(** Isomorphic **)
Lemma coequalizer_isomorphic:
  forall (C: Category)(X Y: C)(f g: C X Y)
         (eq eq': Coequalizer f g),
    coequalizer_obj eq === coequalizer_obj eq' in C.
Proof.
  intros; simpl; unfold isomorphic.
  exists (coequalizer_univ eq (coequalize (IsCoequalizer:=eq'))),  (coequalizer_univ eq' (coequalize (IsCoequalizer:=eq))); split.
  - rewrite (coequalizer_uniqueness (coequalize (IsCoequalizer:=eq)) (u:=Id (coequalizer_obj eq))); [| now rewrite cat_comp_id_cod].
    apply coequalizer_uniqueness.
    now rewrite cat_comp_assoc, !coequalizer_universality.
  - rewrite (coequalizer_uniqueness (coequalize (IsCoequalizer:=eq')) (u:=Id (coequalizer_obj eq'))); [| now rewrite cat_comp_id_cod].
    apply coequalizer_uniqueness.
    now rewrite cat_comp_assoc, !coequalizer_universality.
Qed.

(** Example **)
(** Coequalizer of Setoids **)
Class IsRelation (X: Setoid)(R: X -> X -> Prop) :=
  {
    relation_proper:> Proper ((== in X) ==> (== in X) ==> iff) R
  }.

Structure Relation (X: Setoid) :=
  {
    relation_rel:> X -> X -> Prop;
    relation_prf:> IsRelation X relation_rel
  }.
Existing Instance relation_prf.
Notation "[ 'Rel' 'by' rel 'on' X ]" := (@Build_Relation X rel _).

Inductive EquivClosure (A: Setoid)(R: Relation A): A -> A -> Prop :=
| eqcl_base: forall a b, R a b -> EquivClosure R a b
| eqcl_refl: forall a b: A, a == b -> EquivClosure R a b
| eqcl_sym: forall a b: A, EquivClosure R a b -> EquivClosure R b a
| eqcl_trans: forall a b c, EquivClosure R a b -> EquivClosure R b c -> EquivClosure R a c.

Program Instance EquivClosure_Equivalence (A: Setoid)(R: Relation A)
  : Equivalence (EquivClosure R).
Next Obligation.
  now intros x; apply eqcl_refl.
Qed.
Next Obligation.
  now intros x y; apply eqcl_sym.
Qed.
Next Obligation.
  now intros x y z; apply eqcl_trans.
Qed.

Program Definition EqCl (X: Setoid)(R: Relation X) :=
  [Rel by EquivClosure R on X].
Next Obligation.
  split; intros.
  - revert y y0 H H0.
    induction H1; intros.
    + apply eqcl_base.
      now rewrite <- H0, <- H1.
    + rewrite H0, H1 in H.
      now apply eqcl_refl.
    + now apply eqcl_sym, IHEquivClosure.
    + apply eqcl_trans with b.
      * now apply IHEquivClosure1.
      * now apply IHEquivClosure2.
  - rename x into y, y into x, x0 into y0, y0 into x0.
    revert y y0 H H0.
    induction H1; intros.
    + apply eqcl_base.
      now rewrite H0, H1.
    + rewrite <- H0, <- H1 in H.
      now apply eqcl_refl.
    + now apply eqcl_sym, IHEquivClosure.
    + apply eqcl_trans with b.
      * now apply IHEquivClosure1.
      * now apply IHEquivClosure2.
Qed.
    
Program Definition QuotientSetoid (X: Setoid)(R: Relation X)
        (Heq: Equivalence R) :=
  [Setoid by R on X].

Inductive coequalize_pair (X Y: Setoid)(f g: Map X Y): Y -> Y -> Prop :=
| coequalize_pair_def: forall (x: X)(y y': Y),
    f x == y -> g x == y' ->
    coequalize_pair f g y y'.

Program Definition coequalize_pair_relation (X Y: Setoid)(f g: Map X Y) :=
  [Rel by coequalize_pair f g on Y].
Next Obligation.
  split; intros.
  - destruct H1.
    apply coequalize_pair_def with x.
    + now rewrite H in H1.
    + now rewrite H0 in H2.
  - destruct H1.
    apply coequalize_pair_def with x1.
    + now rewrite H.
    + now rewrite H0.
Qed.

Program Definition coequalizer_of_Setoids (X Y: Setoid)(f g: Map X Y) :=
  [Coequalizer of f, g
    by (fun z h H => [ y :-> h y])
   with [y :-> y]
   to QuotientSetoid (EqCl (coequalize_pair_relation f g)) (EquivClosure_Equivalence Y (coequalize_pair_relation f g))
     in Setoids].
Next Obligation.
  intros y y' Heq.
  now apply eqcl_refl.
Qed.
Next Obligation.
  intros y y' Hr.
  induction Hr.
  - destruct H0.
    rewrite <- H0, <- H1.
    now rewrite (H x).
  - now rewrite H0.
  - now symmetry.
  - now transitivity (h b).
Qed.    
Next Obligation.
  now apply eqcl_base, coequalize_pair_def with x.
Qed.

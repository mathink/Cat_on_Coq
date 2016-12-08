(** * Equalizer **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

Class IsEqualizer (C: Category)(X Y: C)(f g: C X Y)
      (Eq: C)
      (eq: C Eq X)
      (univ: forall {Z: C}{k: C Z X},
          f \o k == g \o k -> C Z Eq) :=
  {
    equalize: f \o eq == g \o eq;

    equalizer_universality: forall Z (k: C Z X)(Heq: f \o k == g \o k),
        eq \o (univ Heq) == k;

    equalizer_uniqueness: forall Z (k: C Z X)(Heq: f \o k == g \o k)(u: C Z Eq),
          eq \o u == k -> u == univ Heq
  }.

Structure Equalizer (C: Category)(X Y: C)(f g: C X Y) :=
  {
    equalizer_obj: C;
    equalizer_map:> C equalizer_obj X;
    equalizer_univ: forall (Z: C)(k: C Z X), f \o k == g \o k -> C Z equalizer_obj;

    equalizer_prf:> IsEqualizer equalizer_map equalizer_univ
  }.
Existing Instance equalizer_prf.

Notation "[ 'Equalizer' 'of' f , g 'by' univ 'with' map 'from' Eq 'in' C ]" :=
  (@Build_Equalizer C _ _ f g Eq map univ _).
Notation "[ 'Equalizer' 'of' f , g 'by' univ 'with' map ]" :=
  [Equalizer of f,g by univ with map from _ in _].
Notation "[ 'Equalizer' 'by' univ 'with' map ]" :=
  [Equalizer of _,_ by univ with map].
Notation "[ 'Equalizer' 'by' univ ]" := [Equalizer by univ with _].

Lemma equalizer_univ_subst
      (C: Category)(X Y: C)(f g: C X Y)
      (eq: Equalizer f g)
      (Z: C)(k k': C Z X)
      (Heq: f \o k == g \o k)
      (Heq': f \o k' == g \o k'):
  k == k' -> 
  equalizer_univ eq Heq == equalizer_univ eq Heq'.
Proof.
  intros Heqk.
  apply equalizer_uniqueness; symmetry; rewrite <- Heqk.
  now rewrite equalizer_universality.
Qed.

(** Isomorphic **)
Lemma equalizer_isomorphic:
  forall (C: Category)(X Y: C)(f g: C X Y)
         (eq eq': Equalizer f g),
    equalizer_obj eq === equalizer_obj eq' in C.
Proof.
  intros; simpl; unfold isomorphic.
  exists (equalizer_univ eq' (equalize (IsEqualizer:=eq))),
  (equalizer_univ eq (equalize (IsEqualizer:=eq'))); split.
  - rewrite (equalizer_uniqueness (equalize (IsEqualizer:=eq)) (u:=Id (equalizer_obj eq))); [| now rewrite cat_comp_id_dom].
    apply equalizer_uniqueness.
    now rewrite <- cat_comp_assoc, !equalizer_universality.
  - rewrite (equalizer_uniqueness (equalize (IsEqualizer:=eq')) (u:=Id (equalizer_obj eq'))); [| now rewrite cat_comp_id_dom].
    apply equalizer_uniqueness.
    now rewrite <- cat_comp_assoc, !equalizer_universality.
Qed.

(** Example **)
(** Equalizer of Setoids **)
Class IsPredicate (X: Setoid)(P: X -> Prop) :=
  {
    predicate_proper:> Proper ((== in X) ==> iff) P
  }.

Structure Predicate (X: Setoid) :=
  {
    predicate:> X -> Prop;
    predicate_prf:> IsPredicate X predicate
  }.
Existing Instance predicate_prf.

Notation "[ 'Predicate' 'by' P 'on' X ]" := (@Build_Predicate X P _).
Notation "[ 'Predicate' 'by' P ]" := [Predicate by P on _].

Inductive SubSetoid_type (X: Setoid)(P: Predicate X) :=
| subsetoid_def (x: X)(Hp: P x).
Notation "[ x 'satisfies' P 'on' X ]" := (@subsetoid_def X P x _).
Notation "[ x 'satisfies' P ]" := [x satisfies P on _].

Definition elem {X: Setoid}{P: Predicate X}(x: SubSetoid_type P): X :=
  match x with
  | @subsetoid_def _ _ x _ => x
  end.

Program Definition SubSetoid (X: Setoid)(P: Predicate X) :=
  [Setoid by `(elem x == elem y) on SubSetoid_type P].
Next Obligation.
  - now intros [x Hx] [y Hy] [z Hz]; transitivity y.
Qed.
Notation "{{ x 'in' X | P }}" := (SubSetoid [Predicate by fun x => P on X]).

Program Definition elem_map (X: Setoid)(P: Predicate X)
  : Map (SubSetoid P) X :=
  [Map by @elem _ P].

Program Definition equalize_predicate (X Y: Setoid)(f g: Map X Y) :=
  [Predicate by `(f x == g x) on X].
Next Obligation.
  now intros x y Heq; rewrite Heq.
Qed.

Program Definition equalizer_of_Setoids (X Y: Setoid)(f g: Map X Y)
  : Equalizer (C:=Setoids) f g:=
  [Equalizer of f, g
    by (fun Z k H => [z :-> subsetoid_def (H z)])
   with elem_map _ from {{x in X | f x == g x }}
     in Setoids].
Next Obligation.
  now intros x y Heq; rewrite Heq.
Qed.
Next Obligation.
  intros x y Heq.
  unfold elem.
  now rewrite Heq.
Qed.
Next Obligation.
  destruct x; unfold elem.
  now apply Hp.
Qed.

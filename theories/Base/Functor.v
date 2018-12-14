(** * Functor **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Category.

Class IsFunctor (C D: Category)
      (fobj: C -> D)
      (fmap: forall {X Y: C}, C X Y -> D (fobj X) (fobj Y)) :=
  {
    fmap_proper:>
              forall X Y: C, Proper ((==) ==> (==)) (@fmap X Y);
    fmap_comp:
      forall (X Y Z: C)(f: C X Y)(g: C Y Z),
        fmap (g \o f) == fmap g \o fmap f;
    fmap_id:
      forall X: C, fmap (Id X) == Id (fobj X)
  }.

Structure Functor (C D: Category): Type :=
  {
    fobj:> C -> D;
    fmap: forall {X Y: C}, C X Y -> D (fobj X) (fobj Y);

    fun_prf:> IsFunctor (@fmap)
  }.
Existing Instance fun_prf.

Notation "C --> D" := (Functor C D).
Arguments fmap_comp {C D fobj fmap F}{X Y Z}(f g): rename.
Arguments fmap_id {C D fobj fmap F}(X): rename.

Notation "[ 'Functor' 'by' fmap 'with' fobj ; C 'to' D ]" := (@Build_Functor C D fobj fmap _).
Notation "[ 'Functor' 'by' fmap 'with' fobj ]" := [Functor by fmap with fobj ; _ to _].
Notation "[ 'Functor' 'by' fmap ]" := [Functor by fmap with _].
Notation "[ 'Functor' 'by' f :-> Ff 'with' X :-> FX ; C 'to' D ]" := [Functor by (fun _ _ f => Ff) with (fun X => FX) ; C to D].
Notation "[ 'Functor' 'by' f :-> Ff 'with' X :-> FX ]" := [Functor by f :-> Ff with X :-> FX ; _ to _].
Notation "[ 'Functor' 'by' f :-> Ff ; C 'to' D ]" :=
  [Functor by f :-> Ff with _ :-> _ ; C to D].
Notation "[ 'Functor' 'by' f :-> Ff ]" := [Functor by f :-> Ff with _ :-> _ ; _ to _].

Program Definition Functor_compose (C D E: Category)(F: C --> D)(G: D --> E): C --> E :=
  [Functor by f :-> fmap G (fmap F f)].
Next Obligation.
  - intros f f' Heqf; simpl.
    now rewrite Heqf.
  - now rewrite !(fmap_comp _).
  - now rewrite !(fmap_id _).
Qed.  

Program Definition Functor_id (C: Category): C --> C :=
  [Functor by f :-> f].

(** *** 1.2.2 Category of Category **)
(** homogenous equality on Hom **)
Inductive hom_eq (C : Category)(X Y: C)(f: C X Y):
  forall (Z W: C), C Z W -> Prop :=
  hom_eq_def:
    forall (g: C X Y), f == g -> hom_eq f g.
Notation "f =H g 'in' C" := (@hom_eq C _ _ f _ _ g) (at level 70, g at next level).
Infix "=H" := hom_eq (at level 70, only parsing).

Lemma hom_eq_refl:
  forall (C: Category)(df cf: C)(bf: C df cf),
    bf =H bf.
Proof.
  intros C df cf bf; apply hom_eq_def; reflexivity.
Qed.

Lemma hom_eq_sym:
  forall (C: Category)
         (df cf: C)(bf: C df cf)
         (dg cg: C)(bg: C dg cg),
    bf =H bg -> bg =H bf.
Proof.
  intros C df cf bf dg cg bg [g Heq].
  apply hom_eq_def; apply symmetry; assumption.
Qed.

Lemma hom_eq_trans:
  forall (C : Category)
         (df cf: C)(bf: C df cf)
         (dg cg: C)(bg: C dg cg)
         (dh ch: C)(bh: C dh ch),
    bf =H bg -> bg =H bh -> bf =H bh.
Proof.
  intros C df cf bf dg cg bg dh ch bh [g Heqg] [h Heqh].
  apply hom_eq_def.
  transitivity g; assumption.
Qed.

Definition Functor_eq (C D: Category)(F G: Functor C D) :=
  forall (X Y: C)(f: C X Y), fmap F f =H fmap G f.
Arguments Functor_eq C D F G / .

Program Definition Functor_setoid (C D: Category): Setoid :=
  [Setoid by (@Functor_eq C D) on C --> D].
Next Obligation.
  - intros F G Heq X Y f.
    now apply hom_eq_sym, Heq.
  - intros F G H HeqFG HeqGH X Y f.
    eapply hom_eq_trans.
    + now apply HeqFG.
    + now apply HeqGH.
Qed.
Canonical Structure Functor_setoid.

Program Definition Cat: Category :=
  [Category by Functor_setoid with Functor_compose, Functor_id].
Next Obligation.
  rename X into C, Y into D, Z into E.
  intros F F' HeqF G G' HeqG X Y f; simpl in *.
  destruct (HeqF _ _ f).
  destruct (HeqG _ _ g).
  apply hom_eq_def.
  now rewrite H, H0.
Qed.
Canonical Structure Cat.

(** constant functor **)
Program Definition constant_functor (C D: Category)(d: D): C --> D :=
  [Functor by f :-> Id d with c :-> d].
Next Obligation.
  now rewrite cat_comp_id_dom.
Qed.
Notation "[ * 'in' D |-> c 'in' C ]" := (constant_functor D C c).

(** Hom(X,-): C -> Setoids **)
Program Definition covariant_hom_functor (C: Category)(X: C)
  : C --> Setoids :=
  [Functor by (fun (Y Z: C)(g: C Y Z) => [ f in C X Y :-> g \o f])
   with (fun Y => C X Y)].
Next Obligation.
  now intros f f' Heq; rewrite Heq.
Qed.
Next Obligation.
  - rename X0 into Y, Y into Z.
    intros g g' Heqg f; simpl.
    now rewrite Heqg.
  - now rewrite cat_comp_assoc.
  - now rewrite cat_comp_id_cod.
Qed.
Notation "'Hom' ( X , - )" := (covariant_hom_functor _ X) (format "'Hom' ( X ,  - )").

(** Hom(-,Y): C^op -> Setoids **)
Program Definition contravariant_hom_functor (C: Category)(Y: C)
  : C^op --> Setoids :=
  [Functor by (fun (X W: C)(f: C W X) => [g in C X Y :-> g \o f] )
   with (fun X => C X Y)].
Next Obligation.
  now intros g g' Heq; rewrite Heq.
Qed.
Next Obligation.
  - rename Y0 into W.
    intros f f' Heqf g; simpl.
    now rewrite Heqf.
  - now rewrite cat_comp_assoc.
  - now rewrite cat_comp_id_dom.
Qed.
Notation "'Hom' ( - , Y )" := (contravariant_hom_functor _ Y) (format "'Hom' ( - ,  Y )").

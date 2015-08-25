Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid.
Require Import COC.Category.Core.

(** 
 ** 射の等価性
いわゆる heterogeneous equality とかいうやつらしい。
JMeq の仲間(だろう、多分)。

ちなみに、 [eq_Hom] ではなく [JMeq] を使うと、後々示したいものが示せなくなるので注意。
 **)
Inductive eq_Hom (C : Category)(X Y: C)(f: C X Y):
  forall (Z W: C), C Z W -> Prop :=
| eq_Hom_def:
    forall (g: C X Y), f == g -> eq_Hom f g.
Infix "=H" := eq_Hom (at level 70).

Lemma eq_Hom_refl:
  forall (C: Category)(df cf: C)(bf: C df cf),
    bf =H bf.
Proof.
  intros C df cf bf; apply eq_Hom_def, reflexivity.
Qed.

Lemma eq_Hom_symm:
  forall (C: Category)
         (df cf: C)(bf: C df cf)
         (dg cg: C)(bg: C dg cg),
    bf =H bg -> bg =H bf.
Proof.
  intros C df cf bf dg cg bg [g Heq].
  apply eq_Hom_def; apply symmetry; assumption.
Qed.

Lemma eq_Hom_trans:
  forall (C : Category)
         (df cf: C)(bf: C df cf)
         (dg cg: C)(bg: C dg cg)
         (dh ch: C)(bh: C dh ch),
    bf =H bg -> bg =H bh -> bf =H bh.
Proof.
  intros C df cf bf dg cg bg dh ch bh [g Heqg] [h Heqh].
  apply eq_Hom_def.
  apply transitivity with g; assumption.
Qed.

(** 
 ** 函手
 **)
Module Functor.
  Class spec (C D: Category)
        (fobj: C -> D)
        (fmap: forall {X Y: C}, (C X Y) -> (D (fobj X) (fobj Y))) :=
    proof {
        fmap_isMap:> forall (X Y: C), isMap (@fmap X Y) ;
        fmap_comp:
          forall (X Y Z: C)(f: C X Y)(g: C Y Z),
            fmap (g \o f) == fmap g \o fmap f;

        fmap_id:
          forall (X: C), fmap (Id X) == Id (fobj X)
      }.

  Structure type (C D: Category) :=
    make {
        fobj: C -> D;
        fmap: forall X Y: C, (C X Y) -> (D (fobj X) (fobj Y));

        prf: spec (@fmap)
      }.

  Notation build fobj fmap :=
    (@make _ _ fobj fmap (@proof _ _ _ _ _ _ _))
      (only parsing).

  Module Ex.
    Notation Functor := type.
    Notation isFunctor := spec.
    Coercion fobj: Functor >-> Funclass.
    Coercion prf: Functor >-> isFunctor.
    Definition fmap := fmap.
    Arguments fmap: clear implicits.
    Arguments fmap {C D}(F){X Y} _: rename.

    Existing Instances prf fmap_isMap.

    Notation Fmap C D F := (forall (X Y: Category.obj C), (Category.arr C X Y) -> (Category.arr D (F X) (F Y))).
  End Ex.

  Import Ex.

  Lemma fmap_substitute:
    forall {C D: Category}(F: Functor C D){X Y: C}(f f': C X Y),
      f == f' -> fmap F f == fmap F f'.
  Proof.
    intros.
    apply Map.substitute, H.
  Qed.
  
  Program Definition op (C D: Category)(F: Functor C D):
    Functor (Category.op C) (Category.op D) :=
    build _ (fun X Y f => fmap F f).
  Next Obligation.
    intros C D F Y X f f' Heq; simpl.
    apply (Map.substitute (spec:=fmap_isMap (spec:=F)(X:=X)(Y:=Y))), Heq.
    (* Toplevel input, characters 0-42: *)
    (* > Check (@fmap_isMap _ _ _ _ _ _ _ _ _ Heq). *)
    (* > ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)
    (* Anomaly: File "pretyping/evarconv.ml", line 789, characters 44-50: Assertion failed. *)
    (* Please report. *)

  Qed.
  Next Obligation.
    simpl; intros C D F Z Y X g f; simpl.
    apply (fmap_comp (spec:=F)).
  Qed.
  Next Obligation.
    simpl; intros C D F X.
    apply (fmap_id (spec:=F)).
  Qed.

  Program Definition compose (C D E: Category)
          (F: Functor C D)(G: Functor D E): Functor C E :=
    build _ (fun X Y f => fmap G (fmap F f)).
  Next Obligation.
    intros; intros f g Heq.
    do 2 apply (Map.substitute).
    exact Heq.
  Qed.
  Next Obligation.
    intros.
    eapply transitivity.
    - apply Map.substitute.
      apply Functor.fmap_comp.
    - apply Functor.fmap_comp.
  Qed.
  Next Obligation.
    intros; simpl.
    eapply transitivity.
    - apply Map.substitute.
      apply Functor.fmap_id.
    - apply Functor.fmap_id.
  Qed.

  Program Definition id (C: Category): Functor C C :=
    build _ (fun X Y f => f ) .
  Next Obligation.
    intros; exact Map.id.
  Qed.
  Next Obligation.
    intros; apply reflexivity.
  Qed.
  Next Obligation.
    intros; apply reflexivity.
  Qed.


  Definition equal {C D: Category}(F G : Functor C D) :=
    (forall (X Y: C)(f: C X Y),
      fmap F f =H fmap G f).
  Arguments equal {C D} / F G.

  Program Definition setoid (C D: Category) :=
    Setoid.build (@equal C D).
  Next Obligation.
    intros C D F X Y f; simpl; apply eq_Hom_refl.
  Qed.
  Next Obligation.
    intros C D F G Heq X Y f; simpl; apply eq_Hom_symm; apply Heq.
  Qed.
  Next Obligation.
    intros C D F G H HeqFG HeqGH X Y f; simpl.
    generalize (HeqGH _ _ f); simpl.
    apply eq_Hom_trans, HeqFG.
  Qed.

End Functor.
Export Functor.Ex.

Definition full (C D: Category)(F: Functor C D) :=
  forall (X Y: C)(g: D (F X) (F Y)),
    exists_ f: C X Y, g == fmap F f.

Definition faithful (C D: Category)(F: Functor C D) :=
  forall (X Y: C)(f1 f2: C X Y),
    fmap F f1 == fmap F f2 -> f1 == f2.

Require Import COC.Category.Morphism.

Lemma fmap_monic:
  forall (C D: Category)(F: Functor C D)(X Y: C)(f: C X Y),
    faithful F -> monic (fmap F f) -> monic f.
Proof.
  unfold faithful, monic; intros.
  apply H, H0.
  eapply transitivity; [| apply Functor.fmap_comp].
  eapply transitivity; [apply symmetry, Functor.fmap_comp |].
  apply Functor.fmap_substitute, H1.
Qed.                                                  
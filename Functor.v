Require Import 
Ssreflect.ssreflect
COC.Setoid COC.Category.

Set Implicit Arguments.
Unset Strict Implicit.

Structure Functor (C D: Category): Type :=
  make_Functor
  { fobj:> C -> D;
    fmap {X Y: C}: Map (X --> Y)  (fobj X --> fobj Y);
    
    fmap_id:
      forall (X: C), fmap id === id_(fobj X) ;

    fmap_compose:
      forall (X Y Z: C)(f: X --> Y)(g: Y --> Z),
        fmap g•fmap f === fmap (g•f) }.
Notation "C ---> D" := (Functor C D) (at level 55, no associativity).

Inductive eq_Hom (C : Category)(X Y: C)(f: X --> Y):
  forall (Z W: C), (Z --> W) -> Prop :=
| eq_Hom_def:
    forall (g: X --> Y), f === g -> eq_Hom f g.
Infix "==_H" := eq_Hom (at level 70).

Inductive morphism (C: Category) :=
| morphism_triple (dom cod: C)(body: dom --> cod).

Definition eq_morphism {C: Category}(f g: morphism C) :=
  let (_,_,bf) := f in
  let (_,_,bg) := g in
  bf ==_H bg.

Program Definition Hom_Setoid (C: Category) :=
  {| equal := @eq_morphism C |}.
Next Obligation.
  split; rewrite /eq_morphism.
  - move=> [df cf bf] //=; apply eq_Hom_def; apply reflexivity.
  - move=> [df cf bf] [dg cg bg] //= [g Heq].
    by apply eq_Hom_def; apply symmetry.
  - move=> [df cf bf] [dg cg bg] [dh ch bh] //= [g Heqg] [h Heqh].
    by apply eq_Hom_def; apply transitivity with g.
Qed.
Existing Instance Hom_Setoid_obligation_1.
Canonical Structure Hom_Setoid.

Definition eq_Functor {C D: Category}(F G : Functor C D) :=
  forall (X Y: C)(f: X --> Y),
    eq_morphism (morphism_triple (fmap F f)) (morphism_triple (fmap G f)).

Program Canonical Structure Functor_Setoid (C D: Category) :=
  {| equal := @eq_Functor C D |}.
Next Obligation.
  split; rewrite /eq_Functor.
  - move=> F //= X Y f.
    apply eq_Hom_def; apply reflexivity.
  - move=> F G //= H X Y f; move: (H X Y f) => [] g H'.
    by apply eq_Hom_def; apply symmetry.
  - move=> F G H //= Heq Heq' X Y f.
    move: (Heq X Y f) (Heq' X Y f) => [] g Hg [] h Hh.
    by apply eq_Hom_def; apply transitivity with g.
Qed.


Structure contravariantFunctor (C D: Category): Type :=
  { op_fobj:> C -> D;
    op_fmap {X Y: C}:> Map (X --> Y)  (op_fobj Y --> op_fobj X);
    
    op_fmap_id:
      forall (X: C), op_fmap id === id_(op_fobj X);

    op_fmap_compose:
      forall (X Y Z: C)(f: X --> Y)(g: Y --> Z),
        op_fmap f•op_fmap g === op_fmap (g•f) }.

(* Program Definition contFunctor_Functor {C D: Category}(opF: contravariantFunctor C D) *)
(* : (op_Category C) ---> D := *)
(*   {| fobj X := op_fobj opF X; *)
(*      fmap X Y := op_fmap opF |}. *)
(* Next Obligation. *)
(*   by apply (op_fmap_id (C:=C)). *)
(* Qed. *)
(* Next Obligation. *)
(*   by apply (op_fmap_compose (C:=C)). *)
(* Qed. *)

Program Definition IdFunctor (C: Category): C ---> C :=
  {| fobj X := X;
     fmap X Y := id_Map (X --> Y) |}.
Next Obligation.
  by equiv_refl.
Qed.
Next Obligation.
  by equiv_refl.
Qed.

Program Definition ComposeFunctor {C D E: Category}
        (F: C ---> D)(G: D ---> E): C ---> E :=
  {| fmap X Y := compose_Map (fmap F) (fmap G) |}.
Next Obligation.
  apply transitivity with (fmap G (id_ (F X))); auto.
  - apply map_preserve_eq, fmap_id.
  - apply fmap_id.
Qed.
Next Obligation.
  eapply transitivity; [ apply fmap_compose | ].
  by apply map_preserve_eq, fmap_compose.
Qed.

Program Definition op_Functor C D (F: C ---> D)
: C ^^op ---> D ^^op :=
  {| fmap X Y := fmap F |}.
Next Obligation.
  rewrite /id_; apply fmap_id.
Qed.
Next Obligation.
  by apply fmap_compose.
Qed.

(* Universe inconsistency! *)
(*
Lemma functor_id_dom:
  forall (C D: Category)(F: Functor_Setoid C D),
    eq_Functor (ComposeFunctor (IdFunctor C) F) F.
Proof.
  move=> C D F.
  rewrite /eq_Functor /=.
  by move=> X Y f; apply eq_Hom_def; apply reflexivity.
Qed.
*)
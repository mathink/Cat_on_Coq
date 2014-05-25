(* 
   This file contains
   - Setoid
   - Category
   - Functor
   - Natural translation (Natrans)
   - Monad

   and some instance e.g. Setoids, Cat.
 *)


Require Import
Coq.Classes.Init Coq.Program.Basics Coq.Program.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.


Module Relations.


  Definition relation A := A -> A -> Prop.

  Class Reflexive {A} (R : relation A) :=
    reflexivity : forall x, R x x.


  Class Symmetric {A} (R : relation A) :=
    symmetry : forall x y, R x y -> R y x.

  Class Transitive {A} (R : relation A) :=
    transitivity : forall x y z, R x y -> R y z -> R x z.


  Class Equivalence {A} (R : relation A) : Prop :=
    { Equivalence_Reflexive :> Reflexive R ;
      Equivalence_Symmetric :> Symmetric R ;
      Equivalence_Transitive :> Transitive R }.

End Relations.
Import Relations.



Delimit Scope coc_scope with coc.
Open Scope coc.

Module Setoid.
    
  Structure type: Type :=
    builder
      { carrier: Type;
        equal: relation carrier;

        equal_refl: Reflexive equal;
        equal_symm: Symmetric equal;
        equal_trans: Transitive equal }.


  Instance equal_equiv (S: type)
  : Equivalence (@equal S).
  Proof.
    generalize dependent S.
    intros [S eq Hr Hs Ht].
    split; auto.
  Qed.


  Module Notations.
    Coercion carrier: type >-> Sortclass.
    Coercion equal_equiv: type >-> Equivalence.
    Notation Setoid := type.
    Notation "x === y" := (equal x y)
                            (at level 80, no associativity): coc_scope.
   End Notations.
End Setoid.
Export Setoid.Notations.
(* Existing Instance Setoid.equal_equiv. *)

Ltac subst_by H :=
  match type of H with
    | ?x === ?y =>
      match goal with
        | [ |- ?p === ?q] =>
          (apply (transitivity (y:=y)); [apply H |])
            || (apply (transitivity (y:=y)); [apply symmetry, H |])
            || (apply (transitivity (y:=y)); [| apply H])
            || (apply (transitivity (y:=y)); [| apply symmetry, H])
            || (apply (transitivity (y:=x)); [apply H |])
            || (apply (transitivity (y:=x)); [apply symmetry, H |])
            || (apply (transitivity (y:=x)); [| apply H])
            || (apply (transitivity (y:=x)); [| apply symmetry, H])
            || fail
      end
  end.

(* Definition of Map *)
Module Map.
  
  Structure type (X Y: Setoid) :=
    builder
      { function: X -> Y;

        preserve_equal:
          forall (x x': X)(Heq: x === x'),
            function x === function x' }.

  Section Properties.
    Local Coercion function: type >-> Funclass.
    Local Notation Map := type.

    Definition equal {X Y: Setoid}(f g: Map X Y) :=
      forall x: X, f x === g x.

    Program Definition setoid (X Y: Setoid): Setoid :=
      {| Setoid.equal := @equal X Y |}.
    Next Obligation.
      intros f x; apply reflexivity.
    Qed.
    Next Obligation.
      intros f g Heq x; apply symmetry, Heq.
    Qed.
    Next Obligation.
      intros f g h Heq Heq' x.
      subst_by (Heq x).
      apply Heq'.
    Qed.

    Program Definition compose {X Y Z: Setoid}
            (f: Map X Y)(g: Map Y Z): Map X Z :=
      {| Map.function := fun x => g (f x) |}.
    Next Obligation. 
      repeat apply Map.preserve_equal; auto.
    Qed.
    Hint Unfold compose.

    Program Definition id (X: Setoid): Map X X :=
      {| Map.function := fun x => x |}.

    Lemma f_equal:
      forall (X Y: Setoid)(f g: setoid X Y),
        f === g -> forall x: X, f x === g x.
    Proof.
      unfold equal; intros; auto.
    Qed.      
    
  End Properties.

  Module Notations.
    Coercion function: type >-> Funclass.
    Notation Map := setoid.
  End Notations.
End Map.
Export Map.Notations.

(*
Module Composable.

  Reserved Notation "X --> Y" (at level 60, no associativity).
  Reserved Notation "g • f" (at level 60, right associativity).

  Structure type :=
    builder
      { obj: Type;
        arr: obj -> obj -> Setoid where  "X --> Y" := (arr X Y);
        compose {X Y Z: obj}:
          (X --> Y) -> (Y --> Z) -> (X --> Z) where "g • f" := (compose f g);

        compose_assoc:
          forall (X Y Z W: obj)(f: X --> Y)(g: Y --> Z)(h: Z --> W),
            (h•g)•f === h•(g•f);

        compose_subst:
          forall (X Y Z: obj)(f f': X --> Y)(g g': Y --> Z)
                 (Heq_fst: f === f')(Heq_snd: g === g'),
            g•f === g'•f' }.
*)


Module Category.

  Reserved Notation "X --> Y" (at level 60, no associativity).
  Reserved Notation "g • f" (at level 60, right associativity).

  Structure type :=
    builder
      { obj: Type;
        arr: obj -> obj -> Setoid where  "X --> Y" := (arr X Y);
        compose {X Y Z: obj}:
          (X --> Y) -> (Y --> Z) -> (X --> Z) where "g • f" := (compose f g);

        id {X: obj}: X --> X;

        compose_assoc:
          forall (X Y Z W: obj)(f: X --> Y)(g: Y --> Z)(h: Z --> W),
            (h•g)•f === h•(g•f);

        compose_subst:
          forall (X Y Z: obj)(f f': X --> Y)(g g': Y --> Z)
                 (Heq_fst: f === f')(Heq_snd: g === g'),
            g•f === g'•f';

        id_dom: (* renamed from id_left *)
          forall (X Y: obj)(f: X --> Y), compose id f === f;
        id_cod: (* renamed from id_rigth *)
          forall (X Y: obj)(f: X --> Y), compose f id === f }.

  Arguments arr {category}(X Y): rename.
  Arguments compose {category}{X Y Z}(f g): rename.
  Arguments id {category}{X}: rename.

  Section Properties.
    Local Coercion obj: type >-> Sortclass.
    Local Notation Category := type.
    Local Notation Hom C := (arr (category:=C)).
    Local Notation "X --> Y" := (Hom _ X Y) (at level 60, no associativity).
    Local Notation "g • f" := (compose f g) (at level 60, right associativity).

    Lemma compose_subst_fst:
      forall (C: Category)(X Y Z: C)(f f': X --> Y)(g: Y --> Z),
        f === f' -> g•f === g•f'.
    Proof.
      intros C X Y Z f f' g Heq; apply compose_subst;
      [ apply Heq | apply reflexivity ].
    Qed.

    Lemma compose_subst_snd:
      forall (C: Category)(X Y Z: C)(f: X --> Y)(g g': Y --> Z),
        g === g' -> g•f === g'•f.
    Proof.
      intros C X Y Z f g g' Heq.
      apply compose_subst; [ apply reflexivity | apply Heq ].
    Qed.
    
    Inductive eq_Hom (C : Category)(X Y: C)(f: X --> Y):
      forall (Z W: C), (Z --> W) -> Prop :=
    | eq_Hom_def:
        forall (g: X --> Y), f === g -> eq_Hom f g.
    Infix "==_H" := eq_Hom (at level 70).

    Lemma eq_Hom_refl:
      forall (C: Category)(df cf: C)(bf: df --> cf),
        bf ==_H bf.
    Proof.
      intros C df cf bf; apply eq_Hom_def; apply reflexivity.
    Qed.

    Lemma eq_Hom_symm:
      forall (C: Category)
             (df cf: C)(bf: df --> cf)
             (dg cg: C)(bg: dg --> cg),
        bf ==_H bg -> bg ==_H bf.
    Proof.
      intros C df cf bf dg cg bg [g Heq].
      apply eq_Hom_def; apply symmetry; assumption.
    Qed.

    Lemma eq_Hom_trans:
      forall (C : Category)
             (df cf: C)(bf : df --> cf)
             (dg cg: C)(bg : dg --> cg)
             (dh ch: C)(bh : dh --> ch),
        bf ==_H bg -> bg ==_H bh -> bf ==_H bh.
    Proof.
      intros C df cf bf dg cg bg dh ch bh [g Heqg] [h Heqh].
      apply eq_Hom_def.
      subst_by Heqg; apply Heqh.
    Qed.

    Inductive morphism (C: Category) :=
    | morphism_triple (dom cod: C)(body: dom --> cod).

    Definition eq_morphism {C: Category}: relation (morphism C) :=
      fun (f g: morphism C) =>
        let (_,_,bf) := f in
        let (_,_,bg) := g in
        bf ==_H bg.
(*
    Program Definition Hom_Setoid (C: Category) :=
      {| Setoid.equal := @eq_morphism C |}.
    Next Obligation.
      intros [df cf bf]; apply eq_Hom_refl.
    Qed.
    Next Obligation.
      intros [df cf bf] [dg cg bg]; apply eq_Hom_symm.
    Qed.
    Next Obligation.
      intros [df cf bf] [dg cg bg] [dh ch bh];
      apply eq_Hom_trans.
    Qed.
*)
  End Properties.



  Module Notations.
    Coercion obj: type >-> Sortclass.
    Notation Category := type.
    Notation Hom C := (@arr C).
    Notation "X --> Y" := (Hom _ X Y) (at level 60, no associativity): coc_scope.
    Notation "g • f" := (compose f g) (at level 60, right associativity): coc_scope.
    Infix "==_H" := eq_Hom (at level 70): coc_scope.
    Notation id := id.
    Notation id_ X := (@id _ X).
  End Notations.
End Category.
Export Category.Notations.

(* isomorphic *)
Definition iso {C: Category}{X Y: C}(f: X --> Y)(g: Y --> X) :=
  g•f === id /\ f•g === id.

Definition Iso {C: Category}(X Y: C) :=
  exists (f: X --> Y)(g: Y --> X), iso f g.

(*
Program Definition obj_Setoid (C: Category): Setoid :=
  {| Setoid.equal := @Iso C |}.
Next Obligation.
  unfold Iso, iso.
  intros x; simpl; exists Category.id, Category.id; split;
  apply Category.id_dom.
Qed.
Next Obligation.
  unfold Iso, iso.
  intros x y [f [g [Hgf Hfg]]]; exists g, f; split; auto.
Qed.
Next Obligation.
  Import Category.
  unfold Iso, iso.
  - intros x y z [f [g [Hgf Hfg]]] [h [i [Hih Hhi]]].
    exists (h•f), (g•i); split.
    + eapply transitivity; [apply symmetry,compose_assoc |].
      eapply transitivity; [apply compose_subst_snd, compose_assoc |].
      eapply transitivity;
        [apply compose_subst_snd, compose_subst_fst, Hih |].
      eapply transitivity;
        [apply compose_subst_snd, id_dom | apply Hgf].
    + eapply transitivity; [apply symmetry,compose_assoc |].
      eapply transitivity; [apply compose_subst_snd, compose_assoc |].
      eapply transitivity;
        [apply compose_subst_snd, compose_subst_fst, Hfg |].
      eapply transitivity;
        [apply compose_subst_snd, id_dom | apply Hhi].
Qed.
*)

Section Setoids.

  Import Category.

  Program Definition Setoids: Category :=
    {| obj := Setoid;
       arr := Map.setoid;
       compose := @Map.compose;
       id := Map.id |}.
  Next Obligation.
    unfold Map.equal; intros x; apply reflexivity.
  Qed.
  Next Obligation.
    unfold Map.equal in *; intros x; simpl.
    subst_by (Heq_snd (f x)).
    apply Map.preserve_equal, Heq_fst.
  Qed.
  Next Obligation.
    unfold Map.equal; intros x; apply reflexivity.
  Qed.
  Next Obligation.
    unfold Map.equal; intros x; apply reflexivity.
  Qed.

End Setoids.


Module Functor.
  Import Category.
  
  Structure type (C D: Category): Type :=
    make_Functor
      { fobj: C -> D;
        fmap {X Y: C}: Map (X --> Y)  (fobj X --> fobj Y);
        
        fmap_id:
          forall (X: C), fmap id === id_(fobj X) ;

        fmap_compose:
          forall (X Y Z: C)(f: X --> Y)(g: Y --> Z),
            fmap g•fmap f === fmap (g•f) }.

  Section Properties.
    Local Coercion fobj: type >-> Funclass.
    Local Notation Functor := type.
    Local Notation "C ---> D" := (Functor C D) (at level 55, no associativity).


    Definition equal {C D: Category}(F G : Functor C D) :=
      forall (X Y: C)(f: X --> Y),
        eq_morphism (morphism_triple (fmap F f)) (morphism_triple (fmap G f)).

    Program Definition setoid (C D: Category) :=
      {| Setoid.equal := @equal C D |}.
    Next Obligation.
      unfold equal.
      intros F X Y f.
      apply eq_Hom_def; apply reflexivity.
    Qed.
    Next Obligation.
      unfold equal; simpl.
      intros F G H X Y f; destruct (H X Y f).
      apply eq_Hom_def; apply symmetry; assumption.
    Qed.
    Next Obligation.
      unfold equal; simpl.
      intros F G H Heq Heq' X Y f.
      generalize (Heq X Y f) (Heq' X Y f);
        intros [g Hg] [h Hh].
      apply eq_Hom_def; apply (transitivity Hg Hh).
    Qed.

    Program Definition compose {C D E: Category}
            (F: C ---> D)(G: D ---> E): C ---> E :=
      {| fobj X := G (F X);
         fmap X Y := Map.compose (fmap F) (fmap G) |}.
    Next Obligation.
      simpl.
      subst_by (fmap_id G (F X)).
      apply Map.preserve_equal, fmap_id.
    Qed.
    Next Obligation.
      eapply transitivity; [ apply fmap_compose | ].
      apply Map.preserve_equal, fmap_compose.
    Qed.

    Program Definition id (C: Category): C ---> C :=
      {| fobj X := X;
         fmap X Y := Map.id (X --> Y) |}.
    Next Obligation.
      apply reflexivity.
    Qed.
    Next Obligation.
      apply reflexivity.
    Qed.

    Lemma compose_assoc:
      forall (X Y Z W: Category)
             (F: X ---> Y)(G: Y ---> Z)(H: Z ---> W),
        equal (compose F (compose G H)) (compose (compose F G) H).
    Proof.
      intros X Y Z W F G H.
      unfold equal; simpl.
      intros d c f; apply eq_Hom_refl.
    Qed.

    Lemma id_dom:
      forall (C D: Category)(F: setoid C D),
        equal (compose (id C) F) F.
    Proof.
      intros C D F.
      unfold equal; simpl.
      intros X Y f; apply eq_Hom_refl.
    Qed.

    Lemma id_cod:
      forall (C D: Category)(F: setoid C D),
        equal F (compose (id C) F).
    Proof.
      intros C D F.
      unfold equal; simpl.
      intros X Y f; apply eq_Hom_refl.
    Qed.
  End Properties.

  Module Notations.
    Coercion fobj: type >-> Funclass.
    Notation Functor := type.
    Notation fobj := fobj.
    Notation fmap := fmap.
    Notation "C ---> D" := (Functor C D) (at level 55, no associativity): coc_scope.
  End Notations.

End Functor.
Export Functor.Notations.

Section Cat.
  Import Category.

  Program Definition Cat: Category :=
    {| arr := Functor.setoid;
       compose := @Functor.compose;
       id := Functor.id |}.
  Next Obligation.
    apply Functor.compose_assoc.
  Qed.
  Next Obligation.
    unfold Functor.equal in *; simpl in *.
    intros dh ch bh.
    generalize (Heq_fst dh ch bh) Z g g' Heq_snd; clear Z g g' Heq_snd.
    intros [fh Hfh].
    intros Z g g' Heq_snd.
    generalize (Heq_snd (f dh) (f ch) fh).
    intros [gfh Hgfh].
    apply eq_Hom_def.
    subst_by Hgfh.
    apply Map.preserve_equal, Hfh.
  Qed.
  Next Obligation.
    apply Functor.id_dom.
  Qed.
  Next Obligation.
    apply Functor.id_cod.
  Qed.

End Cat.

Module Natrans.
  Import Category.

  Structure type {C D: Category}(F G: C ---> D) :=
    { natrans (X: C): F X --> G X;

      naturality:
        forall (X Y: C)(f: X --> Y),
          (natrans Y) • fmap F f === fmap G f • (natrans X) }.

  Section Properties.
    Local Coercion natrans: type >-> Funclass.
    Local Notation Natrans := type.
    Local Notation "F ==> G" := (Natrans F G) (at level 70, no associativity).

    Section Equality.

      Definition equal_2 {C D: Category}
                 {F G: C ---> D}(S: F ==> G)
                 {F' G': C ---> D}(T: F' ==> G') :=
        forall X: C, S X ==_H T X.

      Context {C D: Category}(F G: C ---> D).
      Definition equal: relation (F ==> G) :=
        fun (S T: F ==> G) => forall X: C, S X === T X.
      Hint Unfold equal.

      Program Definition setoid: Setoid :=
        {| Setoid.equal := equal |}.
      Next Obligation.
        intros S X; apply reflexivity.
      Qed.              
      Next Obligation.
        intros S T Heq X; apply symmetry, Heq.
      Qed.              
      Next Obligation.
        intros S T U Heq Heq' X.
        generalize (Heq X) (Heq' X).
        apply transitivity.
      Qed.

    End Equality.

    Section Compositions.

      Program Definition v_compose
              {C D: Category}{F G H: C ---> D}
              (S: F ==> G)(T: G ==> H): F ==> H :=
        {| natrans X :=  T X • S X |}.
      Next Obligation.
        apply (transitivity (y:=T Y•(S Y•fmap F f)));
        [ apply compose_assoc |].
        apply (transitivity (y:=T Y•fmap G f•S X));
          [ apply compose_subst_fst, naturality |].
        apply (transitivity (y:=(T Y•fmap G f)•S X));
          [ apply symmetry, compose_assoc |].
        apply (transitivity (y:=(fmap H f•T X)•S X));
          [| apply compose_assoc ].
        apply compose_subst_snd, naturality.
      Qed.

      Lemma v_compose_assoc:
        forall (C D: Category)(F G H I:C ---> D)
               (S: F ==> G)(T: G ==> H)(U: H ==> I),
          equal (v_compose S (v_compose T U))
                (v_compose (v_compose S T) U).
      Proof.
        intros C D F G H I S T U.
        unfold equal; intro X; simpl.
        apply compose_assoc.
      Qed.          


      Program Definition h_compose
              {C D E: Category}{F G: C ---> D}{F' G': D ---> E}
              (S: F ==> G)(T: F' ==> G')
      : (Functor.compose F F') ==> (Functor.compose G G') :=
        {| natrans X := fmap G' (S X) • T (F X) |}.
      Next Obligation.
        apply symmetry.
        eapply transitivity; [ apply symmetry, compose_assoc | ].
        eapply transitivity; [ apply compose_subst_snd | ].
        apply Functor.fmap_compose.
        eapply transitivity; [ apply compose_subst_snd | ].
        apply Map.preserve_equal; apply symmetry, naturality.
        eapply transitivity;
          [ apply symmetry, compose_subst_snd, Functor.fmap_compose | ].
        eapply transitivity; [ apply compose_assoc | ].
        eapply transitivity; [| apply symmetry, compose_assoc ].
        apply compose_subst_fst.
        apply symmetry, naturality.
      Qed.  


      Lemma h_compose_assoc:
        forall {C D E K: Category}
               {F G: C ---> D}{F' G': D ---> E}{F'' G'': E ---> K}
               (S: F ==> G)(T: F' ==> G')(U: F'' ==> G''),
          equal_2 (h_compose S (h_compose T U))
                     (h_compose (h_compose S T) U).
      Proof.
        intros.
        unfold equal_2.
        intro X; simpl.
        apply eq_Hom_def.
        eapply transitivity;
          [ apply symmetry, compose_assoc | apply compose_subst_snd ].
        apply Functor.fmap_compose.
      Qed.


      Lemma interchange_law:
        forall (C D E: Category)(F G H: C ---> D)(F' G' H': D ---> E)
               (S: F ==> G)(T: G ==> H)(S': F' ==> G')(T': G' ==> H'),
          equal (h_compose (v_compose S T) (v_compose S' T'))
                (v_compose (h_compose S S') (h_compose T T')).
      Proof.
        simpl in *.
        intros; intro X; simpl.
        eapply transitivity;
          [ apply symmetry, compose_subst_snd, Functor.fmap_compose |].
        eapply transitivity; [apply symmetry, compose_assoc |].
        eapply transitivity; [| apply compose_assoc ].
        apply compose_subst_snd.
        eapply transitivity; [apply compose_assoc |].
        eapply transitivity; [| apply symmetry, compose_assoc ].
        apply symmetry,compose_subst_fst, naturality.
      Qed.


      Program Definition dom_compose
              {B C D: Category}{F G: C ---> D}
              (E: B ---> C)(S: F ==> G)
      : (Functor.compose E F) ==> (Functor.compose E G) :=
        {| natrans X := (S (E X)) |}.
      Next Obligation.
        simpl in *.
        apply naturality.
      Qed.

      Lemma dom_compose_assoc:
        forall (A B C D: Category)(F G: C ---> D)
               (E: A ---> B)(E': B ---> C)(S: F ==> G),
          equal_2 (dom_compose E (dom_compose E' S))
                     (dom_compose (Functor.compose E E') S).
      Proof.
        simpl; intros; intro X; apply eq_Hom_def; simpl.
        apply reflexivity.
      Qed.        

      Lemma dom_compose_distr:
        forall (B C D: Category)(F G H: C ---> D)
               (E: B ---> C)(S: F ==> G)(T: G ==> H),
          equal (dom_compose E (v_compose S T))
                (v_compose (dom_compose E S) (dom_compose E T)).
      Proof.
        simpl; intros; intro X; simpl.
        apply reflexivity.
      Qed.        


      Program Definition cod_compose
              {C D E: Category}{F G: C ---> D}
              (S: F ==> G)(H: D ---> E)
      : (Functor.compose F H) ==> (Functor.compose G H) :=
        {| natrans X := fmap H (S X) |}.
      Next Obligation.
        simpl in *.
        eapply transitivity; [ apply Functor.fmap_compose |].
        eapply transitivity; [| apply symmetry, Functor.fmap_compose].
        apply Map.preserve_equal; apply naturality.
      Qed.

      Lemma cod_compose_assoc:
        forall (C D E K: Category)(F G: C ---> D)
               (S: F ==> G)(H: D ---> E)(I: E ---> K),
          equal_2 (cod_compose S (Functor.compose H I))
                     (cod_compose (cod_compose S H) I).
      Proof.
        simpl; intros; intro X; apply eq_Hom_def; simpl.
        apply reflexivity.
      Qed.        

      Lemma cod_compose_distr:
        forall (C D E: Category)(F G H: C ---> D)
               (S: F ==> G)(T: G ==> H)(K: D ---> E),
          equal (cod_compose (v_compose S T) K)
                (v_compose (cod_compose S K) (cod_compose T K)).
      Proof.
        simpl; intros; intro X; simpl.
        apply symmetry, Functor.fmap_compose.
      Qed.

      Lemma dom_cod_compose_assoc:
        forall (B C D E: Category)(F G: C ---> D)
               (I: B ---> C)(S: F ==> G)(J: D ---> E),
          equal_2 (dom_compose I (cod_compose S J))
                  (cod_compose (dom_compose I S) J).
      Proof.
        simpl; intros; intro X; apply eq_Hom_def; simpl.
        apply reflexivity.
      Qed.

    End Compositions.

    Section Identity.

      Program Definition id {C D: Category}(F: C ---> D): F ==> F :=
        {| natrans X := id_ (F X) |}.
      Next Obligation.
        eapply transitivity; [ apply id_cod |].
        eapply transitivity; [| apply symmetry, id_dom ].
        apply reflexivity.
      Qed.

      Lemma v_compose_id_dom:
        forall {C D: Category}(F G: C ---> D)(S: F ==> G),
          equal (v_compose (id F) S) S.
      Proof.
        simpl; intros; intro X; simpl.
        apply id_dom.
      Qed.

      Lemma v_compose_id_cod:
        forall {C D: Category}(F G: C ---> D)(S: F ==> G),
          equal (v_compose S (id G)) S.
      Proof.
        simpl; intros; intro X; simpl.
        apply id_cod.
      Qed.

    End Identity.

  End Properties.

  Module Notations.
    Coercion natrans: type >-> Funclass.
    Notation Natrans := type.
    Notation natrans := natrans.
    Notation "F ==> G" := (Natrans F G) (at level 70, no associativity): coc_scope.
  End Notations.

End Natrans.
Export Natrans.Notations.

Section Fun.
  (* Category cons *)
  Import Category.

  Program Definition Fun (C D: Category): Category :=
    {| arr := Natrans.setoid;
       compose := @Natrans.v_compose C D;
       id := Natrans.id |}.
  Next Obligation.
    simpl.
    apply Natrans.v_compose_assoc.
  Qed.
  Next Obligation.
    rename X into F, Y into G, Z into H,
           f into S, f' into S', g into T, g' into T'.
    unfold Natrans.equal in *.
    simpl; intro X; apply compose_subst;
     [ apply Heq_fst | apply Heq_snd ].
  Qed.
  Next Obligation.
    rename X into F, Y into G, f into S.
    unfold Natrans.equal in *; simpl.
    intro; apply id_dom.
  Qed.
  Next Obligation.
    rename X into F, Y into G, f into S.
    unfold Natrans.equal in *; simpl.
    intro; apply id_cod.
  Qed.

  Definition IdFun (C: Category) := Fun C C.

End Fun.

Module Monad.
  Import Category.

  Structure type (C: Category) :=
    { T: C ---> C;
      unit: Functor.id C ==> T;
      join: Functor.compose T T ==> T;

      join_unit_T:
        forall (X: C),
          join X • unit (T X) === id;
      join_T_unit:
        forall (X: C),
          join X • fmap T (unit X) === id;
      join_join:
        forall (X: C),
          join X • join (T X) === join X • fmap T (join X) }.

  Section Equality.
    Local Notation Monad := type.
    Local Notation η := unit.
    Local Notation μ := join.
    
    Context {C: Cat}.

    Definition equal (m1 m2: Monad C): Prop :=
      Natrans.equal_2 (unit m1) (unit m2) /\
      Natrans.equal_2 (join m1) (join m2).
    Hint Unfold equal.

    Program Definition setoid: Setoid :=
      {| Setoid.equal := equal |}.
    Next Obligation.
      intros m; simpl in*.
      split; unfold Natrans.equal_2; simpl; intro X; apply eq_Hom_refl.
    Qed.
    Next Obligation.
      intros m1 m2; simpl in *.
      intros [Hequ Heqj]; split; intro X; apply eq_Hom_symm;
      [ apply Hequ | apply Heqj ].
    Qed.
    Next Obligation.
      intros m1 m2 m3; simpl in *.
      intros [Hequ12 Heqj12] [Hequ23 Heqj23]; split; intro X;
      [ generalize (Hequ12 X) (Hequ23 X)
      | generalize (Heqj12 X) (Heqj23 X) ];
      apply eq_Hom_trans.
    Qed.
    
  End Equality.    

  Module Notations.
    Notation Monad := type.
    Notation η := unit.
    Notation μ := join.
  End Notations.

End Monad.
Export Monad.Notations.

Module Kleisli.
  Import Category.  

  Structure type (C: Category) :=
    { T: (obj C) -> (obj C);
      unit (X: C): X --> T X;
      bind {X Y: C}: Map (X --> T Y) (T X --> T Y);

      bind_unit_id:
        forall (X: C),
          bind (unit X) === id;

      unit_bind_f:
        forall (X Y: C)(f: X --> T Y),
          bind f•unit X === f;

      bind_assoc:
        forall (X Y Z: C)(f: X --> T Y)(g: Y --> T Z),
          bind g•bind f === bind (bind g•f) }.

  Section Equality.
    Local Notation KT := type.
    Local Notation η := unit.
    Local Notation "[ f #]" := (bind _ f).

    Context {C: Cat}.

    Definition equal (kt1 kt2: KT C): Prop :=
      (forall X: C, unit kt1 X ==_H unit kt2 X)/\
      (forall (X Y: C)(f: X --> T kt1 Y)(X' Y': C)(f': X' --> T kt2 Y'),
         f ==_H f' ->
         bind kt1 f ==_H bind kt2 f').
    
  End Equality.
 
  Module Notations.
    Notation KT := type.
    Notation η := unit.
    Notation "[ f #]" := (bind _ f).
  End Notations.
End Kleisli.
Export Kleisli.Notations.
 

Section MonadKT.
  Import Category.  
  Context {C: Category}.
  
  Section FromMonad.
    Import Monad.

    Program Definition KT_from_Monad (m: Monad C): KT C :=
      {| Kleisli.T := fobj (T m);
         Kleisli.unit := natrans (unit m);
         Kleisli.bind X Y :=
           {| Map.function f := join m Y•fmap (T m) f |}
      |}.
    Next Obligation.
      apply compose_subst_fst, Map.preserve_equal, Heq.
    Qed.
    Next Obligation.
      apply join_T_unit.
    Qed.
    Next Obligation.
      simpl.
      eapply transitivity; [ apply compose_assoc |].
      eapply transitivity;
        [ apply symmetry, compose_subst_fst,
          (Natrans.naturality (Monad.unit m))|].
      eapply transitivity; [ apply symmetry, compose_assoc |].
      eapply transitivity; [ apply compose_subst_snd, Monad.join_unit_T |].
      eapply transitivity; [ apply compose_subst_fst | apply id_cod].
      apply reflexivity.
    Qed.
    Next Obligation.
      simpl in *.
      eapply transitivity.
      - eapply transitivity; [ apply symmetry, compose_assoc |].
        eapply transitivity; [apply compose_subst_snd |].
        + eapply transitivity; [ apply compose_assoc |].
          apply compose_subst_fst.
          apply symmetry, (Natrans.naturality (join m )).
        + apply compose_subst_snd.
          eapply transitivity; [ apply symmetry, compose_assoc |].
          apply compose_subst_snd.
          apply join_join.
      - eapply transitivity; [ apply compose_assoc |]; simpl.
        apply symmetry.
        eapply transitivity; [apply compose_subst_fst |].
        * apply symmetry, Functor.fmap_compose.
        * eapply transitivity; [ apply symmetry, compose_assoc |]; simpl.
          eapply transitivity; [ apply compose_subst_snd |]; simpl.
          apply symmetry, compose_subst_fst, Functor.fmap_compose.
          eapply transitivity; [| apply compose_assoc ].
          apply compose_subst_snd.
          eapply transitivity; [| apply symmetry, compose_assoc ].
          apply reflexivity.
    Qed.

  End FromMonad.

  Section FromKT.
    Import Kleisli.

    Program Definition Monad_from_KT (kt: KT C): Monad C :=
      {| Monad.T :=
           {| fmap X Y :=
                {| Map.function f := bind kt (unit kt Y•f) |} |};
         Monad.unit :=
           {| natrans X := unit kt X |};
         Monad.join :=
           {| natrans X := bind kt (id_ (T kt X)) |} |}.
    Next Obligation.
      apply Map.preserve_equal, compose_subst_fst, Heq.
    Qed.
    Next Obligation.
      simpl.
      eapply transitivity; [ apply Map.preserve_equal, id_dom |].
      apply bind_unit_id.
    Qed.    
    Next Obligation.
      simpl.
      eapply transitivity; [ apply bind_assoc |].
      apply Map.preserve_equal.
      eapply transitivity; [ apply symmetry, compose_assoc |].
      eapply transitivity; 
        [ apply compose_subst_snd, unit_bind_f |].
      apply compose_assoc.
    Qed.    
    Next Obligation.
      simpl.
      apply symmetry, unit_bind_f.
    Qed.    
    Next Obligation.
      simpl.
      eapply transitivity; [ apply bind_assoc |].
      eapply transitivity; [| apply symmetry, bind_assoc ].
      apply Map.preserve_equal.
      eapply transitivity; [| apply symmetry, id_dom ].
      eapply transitivity; [ apply symmetry, compose_assoc |].
      eapply transitivity; [ apply compose_subst_snd, unit_bind_f |].
      apply id_cod.
    Qed.    
    Next Obligation.
      simpl.
      apply unit_bind_f.
    Qed.    
    Next Obligation.
      simpl.
      eapply transitivity; [ apply bind_assoc |].
      eapply transitivity;
        [ apply symmetry, Map.preserve_equal, compose_assoc |].
      eapply transitivity; 
        [ apply Map.preserve_equal, compose_subst_snd, unit_bind_f |].
      eapply transitivity; 
        [ apply Map.preserve_equal, id_cod |].
      apply bind_unit_id.
    Qed.    
    Next Obligation.
      simpl.
      eapply transitivity; [ apply bind_assoc |].
      eapply transitivity; [| apply symmetry, bind_assoc ].
      apply Map.preserve_equal.
      eapply transitivity; [| apply compose_assoc].
      eapply transitivity;
        [| apply symmetry, compose_subst_snd, unit_bind_f ].
      eapply transitivity; [ apply id_dom |].
      apply symmetry, id_cod.
    Qed.
  End FromKT.

  Section KC_fromMonad.
    Import Monad.

    Program Definition KC_M
            {C: Cat}(m: Monad C): Category :=
      {| arr X Y := X --> T m Y;
         compose X Y Z f g := join m Z•fmap (T m) g•f;
         id := unit m |}.
    Next Obligation.
      simpl in *.
      eapply transitivity; [ apply symmetry, compose_assoc |].
      eapply transitivity; [ apply compose_subst_snd |].
      - eapply transitivity; [ apply compose_subst_fst |].
        + apply symmetry, Functor.fmap_compose.
        + eapply transitivity; [apply symmetry, compose_assoc |].
          apply compose_subst_snd.
          apply symmetry, join_join.
      - eapply transitivity; [ apply compose_subst_snd |].
        eapply transitivity; [ apply compose_assoc |].
        apply compose_subst_fst.
        eapply transitivity; [ apply compose_subst_fst |].
        + instantiate (1:=fmap (Functor.compose (T m) (T m)) h•fmap (T m) g); simpl.
          eapply transitivity; [| apply symmetry, Functor.fmap_compose ].
          apply reflexivity.
        + eapply transitivity; [ apply symmetry, compose_assoc |].
          apply compose_subst_snd.
          apply (Natrans.naturality (join m)).
        + eapply transitivity; [| apply compose_assoc ].
          eapply transitivity; [| apply compose_assoc ].
          eapply transitivity; [| apply compose_assoc ].
          apply compose_subst_snd.
          eapply transitivity; [| apply symmetry, compose_assoc ].
          eapply transitivity; [| apply symmetry, compose_assoc ].
          apply compose_subst_fst.
          apply compose_assoc.
    Qed.
    Next Obligation.
      apply compose_subst_fst.
      apply compose_subst; [ apply Heq_fst |].
      apply Map.preserve_equal, Heq_snd.
    Qed.
    Next Obligation.
      eapply transitivity; [apply compose_subst_fst |].
      apply symmetry, (Natrans.naturality (unit m)).
      eapply transitivity; [apply symmetry, compose_assoc |].
      eapply transitivity; [apply compose_subst_snd |].
      apply join_unit_T; simpl.
      apply id_cod.
    Qed.
    Next Obligation.
      eapply transitivity; [apply symmetry, compose_assoc |].
      eapply transitivity; [apply compose_subst_snd |].
      apply join_T_unit.
      apply id_cod.
    Qed.

  End KC_fromMonad.

  Section KC_fromKT.
    Import Kleisli.

    Program Definition KC_KT
            {C: Category}(kt: KT C): Category :=
      {| arr X Y := X --> T kt Y;
         compose X Y Z f g := [ g #]•f;
         id := unit kt |}.
    Next Obligation.
      eapply transitivity; [| apply compose_assoc ].
      apply symmetry, compose_subst_snd, bind_assoc.
    Qed.      
    Next Obligation.
      apply compose_subst;
      [ apply Heq_fst | apply Map.preserve_equal, Heq_snd ].
    Qed.      
    Next Obligation.
      apply unit_bind_f.
    Qed.
    Next Obligation.
      eapply transitivity;
      [ apply compose_subst_snd, bind_unit_id | apply id_cod ].
    Qed.

  End KC_fromKT.

End MonadKT.


Section ListMonad.
  
  Require Import List.
  Import ListNotations.
  Import Category.

  (* Monad *)
  Fixpoint concat {A: Type}(ll: list (list A)): list A :=
    match ll with
      | l::tail => app l (concat tail)
      | _ => []
    end.

  Lemma concat_app_distr:
    forall {A: Type}(ll1 ll2: list (list A)),
      concat (ll1 ++ ll2) = concat ll1 ++ concat ll2.
  Proof.
    induction ll1 as [| l1 tail1]; simpl; auto.
    intro ll2; rewrite IHtail1.
    rewrite app_assoc; reflexivity.
  Qed.
  

  Program Definition function (X Y: Type): Setoid :=
    {| Setoid.equal := fun (f g: X -> Y) => forall x, f x = g x |}.
  Next Obligation.
    intros f x; reflexivity.
  Qed.
  Next Obligation.
    intros f g Heq x.
    rewrite <- Heq; reflexivity.
  Qed.
  Next Obligation.
    intros f g h Heqfg Heqgh x.
    rewrite <- Heqgh; apply Heqfg.
  Qed.

  Program Definition Sets: Category :=
    {| arr := fun (X Y: Type) => function X Y;
       compose X Y Z f g := fun x => g (f x);
       id X := fun x => x |}.
  Next Obligation.
    simpl.
    rewrite Heq_fst, Heq_snd; reflexivity.
  Qed.


  Program Definition ListMonad: Monad Sets :=
    {| Monad.T :=
         {| fmap X Y := 
              {| Map.function := @map X Y |} |};
       Monad.unit :=
         {| natrans X := fun x:X => [x] |};
       Monad.join :=
         {| natrans X := @concat X |}
    |}.
  Next Obligation.
    simpl.
    induction x0 as [| h t]; auto.
    simpl; rewrite IHt, Heq; reflexivity.
  Qed.
  Next Obligation.
    simpl.
    induction x as [| h t]; simpl; auto.
    rewrite IHt; reflexivity.
  Qed.
  Next Obligation.
    simpl.
    induction x as [| h t]; simpl; auto.
    rewrite IHt; reflexivity.
  Qed.
  Next Obligation.
    simpl.
    induction x as [| h t]; simpl; auto.
    rewrite IHt, map_app; reflexivity.
  Qed.
  Next Obligation.
    simpl.
    apply app_nil_r.
  Qed.
  Next Obligation.
    simpl.
    induction x as [| h t]; simpl; auto.
    rewrite IHt; reflexivity.
  Qed.
  Next Obligation.
    simpl.
    induction x as [| h t]; simpl; auto.
    rewrite <- IHt, concat_app_distr; reflexivity.
  Qed.


  (* Kleisli triple *)
  Lemma flat_map_app:
    forall (X Y: Type)(f: X -> list Y)(l1 l2: list X),
      flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
  Proof.
    induction l1 as [| h1 t1]; simpl; auto.
    intro l2; rewrite IHt1, app_assoc; reflexivity.
  Qed.    

  Program Definition ListKT: KT Sets :=
    {| Kleisli.T := list;
       Kleisli.unit X x := [x];
       Kleisli.bind X Y :=
         {| Map.function := @flat_map X Y |} |}.
  Next Obligation.
    simpl.
    induction x0 as [| h t]; simpl; auto.
    rewrite IHt, Heq; reflexivity.
  Qed.
  Next Obligation.
    simpl.
    induction x as [| h t]; simpl; auto.
    rewrite IHt; reflexivity.
  Qed.
  Next Obligation.
    simpl.
    apply app_nil_r.
  Qed.
  Next Obligation.
    simpl.
    induction x as [| h t]; simpl; auto.
    rewrite <- IHt, flat_map_app; reflexivity.
  Qed.

End ListMonad.


Program Definition op_Category (C: Category): Category :=
  {| Category.arr X Y := Hom C Y X;
     Category.compose X Y Z f g := f•g;
     Category.id X := id_ X |}.
Next Obligation.
  apply symmetry, Category.compose_assoc.
Qed.
Next Obligation.
  apply Category.compose_subst; auto.
Qed.
Next Obligation.
  apply Category.id_cod.
Qed.
Next Obligation.
  apply Category.id_dom.
Qed.
Notation "'op' C" := (op_Category C: Cat) (at level 5, right associativity).
Hint Unfold op_Category.
Coercion op_Category: Category >-> Category.


Module Product.

  Section Setoid.
    Context (X Y: Setoid).

    Program Definition setoid: Setoid :=
      {| Setoid.equal :=
           fun p q:(X*Y)%type => fst p === fst q/\snd p === snd q |}.
    Next Obligation.
      simpl.
      intros [x y]; simpl; split; apply reflexivity.
    Qed.
    Next Obligation.
      simpl.
      intros [x y] [x' y']; simpl;
      intros [Heq Heq']; simpl; split;
      apply symmetry; auto.
    Qed.
    Next Obligation.
      simpl.
      intros [x y] [x' y'] [x'' y'']; simpl;
      intros [Heqf Heqs] [Heqf' Heqs']; simpl; split;
      [generalize Heqf Heqf' | generalize Heqs Heqs' ];
      apply transitivity.
    Qed.

  End Setoid.

  Section Cat.
    Context (C D: Category).
    Import Category.
    Program Definition category: Category :=
      {| arr X Y :=
           setoid (Hom C (fst X) (fst Y)) (Hom D (snd X)(snd Y));
         compose X Y Z f g := (fst g•fst f,snd g•snd f);
         id X := (id_ (fst X), id_ (snd X)) |}.
    Next Obligation.
      simpl in *; split; apply compose_assoc.
    Qed.      
    Next Obligation.
      simpl in *; split; apply compose_subst; auto.
    Qed.      
    Next Obligation.
      simpl in *; split; apply id_dom.
    Qed.      
    Next Obligation.
      simpl in *; split; apply id_cod.
    Qed.

  End Cat.

End Product.

Section EvaluationFunctor.
  Import Category.
  Context (B C: Category).
  Let P := Product.category (Fun C B) C.

  Definition fobj_EF (FX: P): B := fst FX (snd FX).

  Program Definition fmap_EF (FX GY: P)
  : Map (Hom P FX GY) (Hom B (fobj_EF FX) (fobj_EF GY)) :=
    {| Map.function Sf := fmap (fst GY) (snd Sf)•(natrans (fst Sf) (snd FX)) |}.
  Next Obligation.
    simpl in *.
    apply Category.compose_subst;
      [ apply H | apply Map.preserve_equal, H0 ].
  Qed.    

  Program Definition EvalFunctor
  : Product.category (Fun C B) C ---> B :=
    {| fmap FX GY := fmap_EF FX GY |}.
  Next Obligation.
    simpl; unfold fobj_EF; simpl.
    subst_by (Functor.fmap_id t o).
    apply id_dom.
  Qed.
  Next Obligation.
    simpl in *.
    eapply transitivity; [| apply compose_assoc ].
    eapply transitivity; [apply symmetry, compose_assoc |].
    apply compose_subst_snd.
    eapply transitivity; [| apply (Natrans.naturality t) ].
    eapply transitivity;
      [| apply compose_subst_fst, Functor.fmap_compose ].
    eapply transitivity; [| apply compose_assoc ].
    apply compose_subst_snd.
    apply symmetry, (Natrans.naturality t).
  Qed.

End EvaluationFunctor.



Module Yoneda.
  Import Category.

  Section CovariantHom.
    Context {C: Category}.
    
    Program Definition fmap_HomFunctor (X Y Z: C)(g: Y --> Z)
    : Map (Hom C X Y)  (Hom C X Z) :=
      {| Map.function f := g•f |}.
    Next Obligation.
      apply compose_subst_fst; auto.
    Qed.      

    Program Definition HomFunctor (X: C): C ---> Setoids :=
      {| fobj Y := Hom C X Y;
         fmap Y Z := {| Map.function g := fmap_HomFunctor X g |} |}.
    Next Obligation.
      simpl; unfold Map.equal; simpl.
      intro f; apply compose_subst_snd; auto.
    Qed.
    Next Obligation.
      simpl; unfold Map.equal; simpl.
      intro f; apply id_cod.
    Qed.  
    Next Obligation.
      simpl; unfold Map.equal; simpl.
      intro h; apply symmetry, compose_assoc.
    Qed.

  End CovariantHom.

  Section ContravariantHom.
    Context {C: Category}.
    
    Program Definition fmap_CoHomFunctor (X Y Z: C)(f: X --> Y)
    : Map (Hom C Y Z)  (Hom C X Z) :=
      {| Map.function g := g•f |}.
    Next Obligation.
      apply compose_subst_snd; auto.
    Qed.      

    Program Definition CoHomFunctor (Z: C): op C ---> Setoids :=
      {| fobj X := Hom C X Z;
         fmap Y X := {| Map.function f := fmap_CoHomFunctor Z f|} |}.
    Next Obligation.
      simpl; unfold Map.equal; simpl.
      intro f; apply compose_subst_fst; auto.
    Qed.
    Next Obligation.
      simpl; unfold Map.equal; simpl.
      intro f; apply id_dom.
    Qed.  
    Next Obligation.
      simpl; unfold Map.equal; simpl.
      intro h; apply compose_assoc.
    Qed.

  End ContravariantHom.


  Section NF.
    Context (C: Category).
    
    Definition fobj_NF
               (FX: Product.category (Fun C Setoids) C)
    : Setoids :=
      Natrans.setoid (HomFunctor (snd FX)) (fst FX).
    Check CoHomFunctor.

    Program Definition map_natrans_fmap_NF
            (FX GY: Product.category (Fun C Setoids) C)
            (Sf: Hom (Product.category (Fun C Setoids) C) FX GY)
            (alpha: fobj_NF FX)(X: C)
    : Map (Hom C (snd GY) X) (fst GY X) :=
      {| Map.function g :=
           (natrans (fst Sf) X•natrans alpha X•fmap (CoHomFunctor X) (snd Sf)) g |}.
    Next Obligation.
      simpl.
      do 2 apply Map.preserve_equal.
      apply compose_subst_snd, Heq.
    Qed.

    Program Definition natrans_fmap_NF
            (FX GY: Product.category (Fun C Setoids) C)
            (Sf: Hom (Product.category (Fun C Setoids) C) FX GY)
            (alpha: fobj_NF FX)
    : Natrans (HomFunctor (snd GY)) (fst GY) :=
      {| Natrans.natrans X :=
           map_natrans_fmap_NF Sf alpha X |}.
    Next Obligation.
      simpl in *.
      unfold Map.equal; simpl.
      rename o into Z.
      intro h.
      eapply transitivity; [| apply (Natrans.naturality t)].
      simpl.
      apply Map.preserve_equal.
      eapply transitivity; [| apply (Natrans.naturality alpha)].
      simpl.
      apply Map.preserve_equal, compose_assoc.
    Qed.


    Program Definition map_fmap_NF 
            (FX GY: Product.category (Fun C Setoids) C)
            (Sf: Hom (Product.category (Fun C Setoids) C) FX GY)
    : Map (Natrans.setoid (HomFunctor (snd FX)) (fst FX))
          (Natrans.setoid (HomFunctor (snd GY)) (fst GY)) :=
      {| Map.function alpha := natrans_fmap_NF Sf alpha |}.
    Next Obligation.
      simpl in *.
      unfold Natrans.equal; simpl.
      unfold Map.equal; simpl.
      intros.
      apply Map.preserve_equal; simpl.
      apply Heq.
    Qed.

    Program Definition NFunctor
    : Product.category (Fun C Setoids) C ---> Setoids :=
      {| fmap FX GY :=
           {| Map.function Sf := map_fmap_NF Sf |} |}.
    Next Obligation.
      simpl in *.
      unfold Map.equal; simpl.
      unfold Natrans.equal; simpl.
      unfold Map.equal; simpl.
      intros S X f; simpl.
      eapply transitivity; [apply Map.f_equal, H |].
      do 2 apply Map.preserve_equal.
      apply compose_subst_fst, H0.
    Qed.
    Next Obligation.
      simpl in *.
      unfold Map.equal; simpl.
      unfold Natrans.equal; simpl.
      unfold Map.equal; simpl.
      intros S X f.
      apply Map.preserve_equal, id_dom.
    Qed.    
    Next Obligation.
      simpl in *.
      unfold Map.equal; simpl.
      unfold Natrans.equal; simpl.
      unfold Map.equal; simpl.
      intros S X f.
      do 3 apply Map.preserve_equal.
      apply compose_assoc.
    Qed.

  End NF.

  Check (forall (C: Category) X,
           Map (EvalFunctor Setoids C X) (NFunctor C X)).
  Check (forall (C: Category),
           Natrans (EvalFunctor Setoids C) (NFunctor C)).

  Section YonedaLemma.
    Context {C: Cat}(F: Fun C Setoids)(X: C).

    Program Definition yoneda
    : (NFunctor C (F,X)) --> (EvalFunctor Setoids C (F,X)) :=
      {| Map.function alpha := alpha X (id_ X) |}.
    Next Obligation.
      apply Heq.
    Qed.    

    Program Definition inv_yoneda
    : (EvalFunctor Setoids C (F,X)) --> (NFunctor C (F,X)) :=
      {| Map.function x := 
           {| Natrans.natrans A :=
                {| Map.function f := fmap F f x |} |} |}.
    Next Obligation.
      apply Map.f_equal, Map.preserve_equal, Heq.
    Qed.
    Next Obligation.
      unfold Map.equal; simpl.
      rename Y into Z, X0 into Y, f into g.
      intros f.
      eapply transitivity;
        [ apply symmetry, Map.f_equal, (Functor.fmap_compose F) |].
      apply reflexivity.
    Qed.
    Next Obligation.
      unfold Natrans.equal; simpl;
      unfold Map.equal; simpl.
      intros Y f.
      apply Map.preserve_equal, Heq.
    Qed.


    Lemma yoneda_inv_yoned_iso_1:
      inv_yoneda •yoneda === id.
    Proof.
      intro alpha; simpl in *.
      unfold Natrans.equal; simpl;
      unfold Map.equal; simpl.
      intros Y f; simpl.
      eapply transitivity;
        [ apply symmetry, (Natrans.naturality alpha) |]; simpl.
      eapply transitivity;
        [ apply Map.f_equal |]; simpl.
      - unfold Map.equal; simpl.
        intros.
        instantiate (1:= {| Map.function x' := alpha Y (f•x') |}); simpl.
        apply reflexivity.
      - simpl.
        apply Map.preserve_equal, id_dom.
        Grab Existential Variables.
        simpl.
        intros.
        apply Map.preserve_equal.
        apply compose_subst_fst, Heq.
    Qed.
    
    Lemma yoneda_inv_yoned_iso_2:
      yoneda •inv_yoneda === id.
    Proof.
      intro alpha; simpl.
      eapply transitivity;
        [ apply Map.f_equal, (Functor.fmap_id F) |].
      apply reflexivity.
    Qed.

    Lemma yoneda_lemma:
      iso yoneda inv_yoneda.
    Proof.
      split; intro x; simpl;
      [ apply yoneda_inv_yoned_iso_1 |  apply yoneda_inv_yoned_iso_2 ].
    Qed.

  End YonedaLemma.
  
  
  Section YonedaFunctor.
    Context {C: Cat}.

    Program Definition map_natrans_fmap_YonedaFunctor
            (Z Y X: C)(f: X --> Y): (HomFunctor Y Z) --> (HomFunctor X Z) :=
      {| Map.function g := g•f |}.
    Next Obligation.
      apply compose_subst_snd, Heq.
    Qed.

    Program Definition natrans_fmap_YonedaFunctor
            (Y X: op C)(f: Hom (op C) Y X)
    : Natrans.setoid (HomFunctor (C:=C) Y) (HomFunctor (C:=C) X) :=
      {| Natrans.natrans Z := map_natrans_fmap_YonedaFunctor Z f |}.
    Next Obligation.
      simpl.
      unfold Map.equal; simpl.
      intros; apply Category.compose_assoc.
    Qed.

    Program Definition fmap_YonedaFunctor (Y X: op C)
    : Map (Hom (op C) Y X) (Natrans.setoid (HomFunctor (C:=C) Y) (HomFunctor (C:=C)X)) :=
      {| Map.function f := natrans_fmap_YonedaFunctor f |}.
    Next Obligation.
      simpl.
      unfold Natrans.equal, natrans_fmap_YonedaFunctor; simpl.
      unfold Map.equal, map_natrans_fmap_YonedaFunctor; simpl.
      intros; apply compose_subst_fst, Heq.
    Qed.

    Program Definition YonedaFunctor
    : Functor (op C: Cat) (Fun C Setoids) :=
      {|fmap := fmap_YonedaFunctor |}.
    Next Obligation.
      simpl.
      unfold Natrans.equal, natrans_fmap_YonedaFunctor; simpl.
      unfold Map.equal, map_natrans_fmap_YonedaFunctor; simpl.
      intros; apply id_dom.
    Qed.
    Next Obligation.
      simpl.
      unfold Natrans.equal, natrans_fmap_YonedaFunctor; simpl.
      unfold Map.equal, map_natrans_fmap_YonedaFunctor; simpl.
      intros; apply Category.compose_assoc.
    Qed.      

  End YonedaFunctor.
  Notation GrothendieckFunctor := YonedaFunctor.


  Section CoYonedaFunctor.
    Context {C: Cat}.

    Program Definition fmap_CoYonedaFunctor
            {X Y: C}(f: X --> Y)
    : Natrans (CoHomFunctor X) (CoHomFunctor Y) :=
      {| Natrans.natrans Z :=
           {| Map.function g := f•g |} |}.
    Next Obligation.
      apply compose_subst_fst, Heq.
    Qed.
    Next Obligation.
      simpl.
      unfold Map.equal, map_natrans_fmap_YonedaFunctor; simpl.
      intros g; apply symmetry, compose_assoc.
    Qed.

    Program Definition CoYonedaFunctor
    : Functor (C: Cat) (Fun (op C) Setoids) :=
      {| fmap X Y :=
           {| Map.function f := fmap_CoYonedaFunctor f |} |}.
    Next Obligation.
      simpl.
      unfold Natrans.equal, natrans_fmap_YonedaFunctor; simpl.
      unfold Map.equal, map_natrans_fmap_YonedaFunctor; simpl.
      intros Z f; apply compose_subst_snd, Heq.
    Qed.
    Next Obligation.
      simpl.
      unfold Natrans.equal, natrans_fmap_YonedaFunctor; simpl.
      unfold Map.equal, map_natrans_fmap_YonedaFunctor; simpl.
      intros; apply id_cod.
    Qed.      
    Next Obligation.
      simpl.
      unfold Natrans.equal, natrans_fmap_YonedaFunctor; simpl.
      unfold Map.equal, map_natrans_fmap_YonedaFunctor; simpl.
      intros; apply symmetry, compose_assoc.
    Qed.
    
  End CoYonedaFunctor.

End Yoneda.
Export Yoneda.

Eval compute in
    (fmap (YonedaFunctor (nat: Sets))
          (fun b:bool => if b then 1 else 0)
          (fun n:nat => match n with 0 => true | _ => false end) 0).

Eval compute in
    (fmap (CoYonedaFunctor (nat: op Sets))
          (fun b:bool => if b then 1 else 0)
          (fun n:nat => match n with 0 => true | _ => false end) 0).

Definition function_compose
           {X Y: Set}(f: X -> Y) :=
  fmap (YonedaFunctor (X: Sets)) f.
Eval compute in  function_compose.
Extraction Language Haskell.
Extraction "../ext/yoneda.hs" function_compose.



Require Import Utf8 Setoid Coq.Classes.Init.

Set Implicit Arguments.

Reserved Notation "X ⟶ Y" (at level 60, right associativity).
Reserved Notation "g ◦ f" (at level 60, right associativity).

Class Category :=
  { obj: Type;
    arr (X Y: obj): Setoid where "X ⟶ Y" := (arr X Y);

    compose {X Y Z: obj}:
      (X ⟶ Y) -> (Y ⟶ Z) -> (X ⟶ Z) where "g ◦ f" := (compose f g);

    id {X: obj}: X ⟶ X;

    compose_assoc:
      forall (X Y Z W: obj)(f: X ⟶ Y)(g: Y ⟶ Z)(h: Z ⟶ W),
        (h◦g)◦f == h◦(g◦f);
    compose_subst:
      forall (X Y Z: obj)(f f': X ⟶ Y)(g g': Y ⟶ Z)
         (Heq_fst: f == f')(Heq_snd: g == g'),
        g◦f == g'◦f';

    id_dom: (* renamed from id_left *)
      forall (X Y: obj)(f: X ⟶ Y), compose id f == f;
    id_cod: (* renamed from id_rigth *)
      forall (X Y: obj)(f: X ⟶ Y), compose f id == f }.
Coercion obj: Category >-> Sortclass.
Notation "X ⟶ Y" := (arr X Y) (at level 60, right associativity).
Notation "g ◦ f" := (compose f g) (at level 60, right associativity).
Definition id_ {C: Category}(X: C) := id (X:=X).

Lemma compose_subst_fst:
  forall (C: Category)(X Y Z: C)(f f': X ⟶ Y)(g: Y ⟶ Z),
    f == f' -> g◦f == g◦f'.
Proof.
  intros.
  apply compose_subst; [ apply H | equiv_refl ].
Qed.

Lemma compose_subst_snd:
  forall (C: Category)(X Y Z: C)(f: X ⟶ Y)(g g': Y ⟶ Z),
    g == g' -> g◦f == g'◦f.
Proof.
  intros.
  apply compose_subst; [ equiv_refl | apply H ].
Qed.


Program Instance Sets: Category :=
  { obj := Set;
    arr X Y := FunctionSetoid X Y;
    compose X Y Z f g := fun x => g (f x);
    id X := fun x: X => x }.
Next Obligation.
  congruence.
Qed.

Program Instance Setoids: Category :=
  { obj := Setoid;
    arr X Y := MapSetoid X Y;
    compose X Y Z f g := ComposeMap f g;
    id X := IdMap X }.
Next Obligation.
  simpl; intros; try equiv_refl.
Qed.
Next Obligation.
  equiv_trns_with (g' (f x)); auto.
  apply ap_preserve_eq; auto.
Qed.
Next Obligation.
  simpl; intros; try equiv_refl.
Qed.
Next Obligation.
  simpl; intros; try equiv_refl.
Qed.

Program Instance op_Category (C: Category): Category :=
  { obj := obj ;
    arr X Y := arr Y X;
    compose X Y Z f g := f ◦ g;
    id X := id }.
Next Obligation.
  equiv_symm; apply compose_assoc.
Qed.
Next Obligation.
  apply compose_subst; auto.
Qed.
Next Obligation.
  apply id_cod.
Qed.
Next Obligation.
  apply id_dom.
Qed.
Notation "C ^^op" := (op_Category C) (at level 5, left associativity).


Section CategoryProperties.
  Variables (C: Category).

  Definition mono {X Y: C}(f: X ⟶ Y) :=
    forall (Z: C)(g h: Y ⟶ Z),
      g◦f == h◦f -> g == h.
  
  Definition epi {X Y: C}(f: X ⟶ Y) :=
    forall (U: C)(g h: U ⟶ X),
      f◦g == f◦h -> g == h.
  
  Definition iso {X Y: C}(f: X ⟶ Y)(g: Y ⟶ X) :=
    g◦f == id ∧ f◦g == id.

  Definition Iso (X Y: C) :=
    exists (f: X ⟶ Y)(g: Y ⟶ X), iso f g.
  Notation "X ≃ Y" := (Iso X Y) (at level 70, no associativity).
  
  Definition initial (I: C)(In: forall X:C, I ⟶ X) :=
    forall (X: C)(f: I ⟶ X), In X == f.

  Definition terminal (T: C)(Te: forall X: C, X ⟶ T) :=
    forall (X: C)(f: X ⟶ T), Te X == f.

  Definition null (Z: C) ZIn ZTe := initial Z ZIn ∧ terminal Z ZTe.

End CategoryProperties.

Lemma initial_unique_up_to_iso:
  forall C I In I' In', 
    initial C I In -> initial C I' In' -> Iso C I I'.
Proof.
  intros C I In I' In' Hinit Hinit'.
  unfold Iso, iso.
  unfold initial in *.
  generalize (Hinit I id) (Hinit' I' id);
    intros Hin Hin'.
  exists (In I'), (In' I).
  split.
  - equiv_trns_with (In I); auto.
    equiv_symm; auto.
  - equiv_trns_with (In' I'); auto.
    equiv_symm; auto.
Qed.

Lemma terminal_unique_up_to_iso:
  forall C T Te T' Te',
    terminal C T Te -> terminal C T' Te' -> Iso C T T'.
Proof.
  intros C T Te T' Te' Hterm Hterm'.
  unfold Iso, iso, terminal in *.
  generalize (Hterm T id) (Hterm' T' id);
    intros Hte Hte'.
  exists (Te' T), (Te T'); split.
  - equiv_trns_with (Te T); auto.
    equiv_symm; auto.
  - equiv_trns_with (Te' T'); auto.
    equiv_symm; auto.
Qed.

Lemma initial_dual_terminal:
  forall (C: Category) I In,
    initial C I In -> terminal C ^^op I In.
Proof.
  unfold initial, terminal.
  intros C I In Hinit X f.
  apply Hinit.
Qed.

Lemma terminal_dual_initial:
  forall (C: Category) T Te,
    terminal C T Te -> initial C ^^op T Te.
Proof.
  unfold initial, terminal.
  intros C T Te Hterm X f.
  apply Hterm.
Qed.

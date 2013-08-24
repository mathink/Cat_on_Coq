

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


  Definition product (X Y P: C)(proj_X: P ⟶ X)(proj_Y: P ⟶ Y) :=
    forall (Q: C)(f: Q ⟶ X)(g: Q ⟶ Y),
      { fg: Q ⟶ P | 
        (proj_X ◦ fg == f ∧ proj_Y ◦ fg == g) 
          ∧ (forall h: Q ⟶ P, proj_X ◦ h == f ∧ proj_Y ◦ h == g -> fg == h)}.

  Definition coproduct (X Y coP: C)(in_X: X ⟶ coP)(in_Y: Y ⟶ coP) :=
    forall (Q: C)(f: X ⟶ Q)(g: Y ⟶ Q),
      { fg: coP ⟶ Q |
        (fg ◦ in_X == f ∧ fg ◦ in_Y == g) 
          ∧ (forall h: coP ⟶ Q, h ◦ in_X == f ∧ h ◦ in_Y == g -> fg == h) }.

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
  intros; apply H.
Qed.

Lemma terminal_dual_initial:
  forall (C: Category) T Te,
    terminal C T Te -> initial C ^^op T Te.
Proof.
  intros; apply H.
Qed.

Lemma product_dual_coproduct:
  forall (C: Category)(X Y: C)(XY: C)
     (proj_X: XY ⟶ X)(proj_Y: XY ⟶ Y),
    product C X Y XY proj_X proj_Y ->
    coproduct C ^^op X Y XY proj_X proj_Y.
Proof.
  intros; apply X0.
Qed.

Lemma coproduct_dual_product:
  forall (C: Category)(X Y: C)(XY: C)
     (in_X: X ⟶ XY)(in_Y: Y ⟶ XY),
    coproduct C X Y XY in_X in_Y ->
    product C ^^op X Y XY in_X in_Y.
Proof.
  intros; apply X0.
Qed.  

(* Example *)
(* Sets の始対象は Empty_set です 

   以下における定義と証明は，人によってはなんか腑に落ちんなぁという人もいるかもしれない．
 *)
Definition from_Empty_set (A: Set)(f: Empty_set): A.
  elim f.
Defined.

Lemma Empty_set_initial:
  initial Sets Empty_set from_Empty_set.
Proof.
  unfold initial; simpl.
  intros X f x.
  elim x.
Qed.

(* Sets の終対象は unit です 

   こちらは大丈夫(何が?)
 *)
Definition to_unit (A: Set): A -> unit :=
  fun _ => tt.

Lemma unit_terminal:
  terminal Sets unit to_unit.
Proof.
  unfold terminal; simpl.
  intros X f x.
  destruct (f x).
  unfold to_unit.
  reflexivity.
Qed.

(* 直積型は直積対象です *)
Lemma prod_product:
  forall (X Y: Sets),
    product Sets X Y (prod X Y) (@fst X Y) (@snd X Y).
Proof.
  unfold product; simpl.
  intros X Y Q f g.
  exists (fun q => (f q, g q)); simpl.
  repeat split.
  intros h [Hf Hg] q.
  generalize (Hf q); intro Hfq.
  generalize (Hg q); intro Hgq.
  remember (h q) as hq.
  destruct hq as [hx hy]; simpl in *.
  subst.
  reflexivity.
Qed.

(* 直和型は余直積対象です *)
Lemma sum_coproduct:
  forall (X Y: Sets),
    coproduct Sets X Y (sum X Y) (@inl X Y) (@inr X Y).
Proof.
  unfold coproduct; simpl.
  intros X Y Q f g.
  exists (fun m => match m with inl x => f x | inr y => g y end); simpl.
  repeat split.
  intros h [Hf Hg] [ x | y ].
  rewrite Hf; reflexivity.
  rewrite Hg; reflexivity.
Qed.


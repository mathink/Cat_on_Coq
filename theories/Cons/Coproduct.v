(** * Coproduct **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

Class IsCoproduct (C: Category)(X Y: C)
      (CP: C)(in1: C X CP)(in2: C Y CP)
      (univ: forall (Z: C), C X Z -> C Y Z -> C CP Z) :=
  {
    coproduct_universality_1:
      forall (Z: C)(i1: C X Z)(i2: C Y Z),
        (i1 == univ Z i1 i2 \o in1);
    
    coproduct_universality_2:
      forall (Z: C)(i1: C X Z)(i2: C Y Z),
        (i2 == univ Z i1 i2 \o in2);
    
    coproduct_uniqueness:
      forall (Z: C)(i1: C X Z)(i2: C Y Z)(u: C CP Z),
        (i1 == u \o in1) ->
        (i2 == u \o in2) ->
        u == univ Z i1 i2
  }.

Structure Coproduct (C: Category)(X Y: C) :=
  {
    coproduct_obj:> C;
    coproduct_inj1: C X coproduct_obj;
    coproduct_inj2: C Y coproduct_obj;

    coproduct_univ: forall (Z: C), C X Z -> C Y Z -> C coproduct_obj Z;

    coproduct_prf:> IsCoproduct coproduct_inj1 coproduct_inj2 (@coproduct_univ)
  }.
Existing Instance coproduct_prf.

Notation "[ 'Coproduct' P 'by' univ 'with' in1 , in2 ]" :=
  (@Build_Coproduct _ _ _ P in1 in2 univ _).
Notation "[ 'Coproduct' 'by' univ 'with' in1 , in2 ]" :=
  [Coproduct _ by univ with in1, in2].

Notation "[ f , g 'from' P ]" := (coproduct_univ P f g).
Notation "in1_{ P }" := (coproduct_inj1 P) (at level 0, no associativity, format "in1_{ P }").
Notation "in2_{ P }" := (coproduct_inj2 P) (at level 0, no associativity, format "in2_{ P }").

Program Instance coproduct_univ_proper (C: Category)(X Y: C)
        (cp: Coproduct C X Y)
        (Z: C)
  : Proper ((== in C X Z) ==> (== in C Y Z) ==> (==))
           (@coproduct_univ _ _ _ cp Z).
Next Obligation.
  intros f f' Heqf g g' Heqg.
  apply coproduct_uniqueness.
  - rewrite <- Heqf.
    now apply coproduct_universality_1.
  - rewrite <- Heqg.
    now apply coproduct_universality_2.
Qed.  

Definition coproduct_map (C: Category)
           (coprod: forall (X Y: C), Coproduct C X Y)
           (X X' Y Y': C)(f: C X Y)(g: C X' Y')
  : C (coprod X X') (coprod Y Y') :=
  [in1_{coprod Y Y'} \o f, in2_{coprod Y Y'} \o g from (coprod X X')].
Notation "[ f \+ g 'with' coprod ]" := (coproduct_map coprod f g).

Program Instance coproduct_map_proper
        (C: Category)(coprod: forall (X Y: C), Coproduct C X Y)
        (X X' Y Y': C)
  : Proper ((==) ==> (==) ==> (==)) (@coproduct_map _ coprod X X' Y Y').
Next Obligation.
  intros f f' Heqf g g' Heqg.
  unfold coproduct_map.
  now rewrite Heqf, Heqg.
Qed.

Lemma coproduct_map_compose:
  forall (C: Category)(coprod: forall (X Y: C), Coproduct C X Y)
         (X X' Y Y' Z Z': C)
         (f: C X Y)(g: C Y Z)
         (f': C X' Y')(g': C Y' Z'),
    [(g \o f) \+ (g' \o f') with coprod] ==
    [g \+ g' with coprod] \o [ f \+ f' with coprod].
Proof.
  intros.
  unfold coproduct_map.
  symmetry.
  apply coproduct_uniqueness.
  - rewrite cat_comp_assoc.
    rewrite <- (coproduct_universality_1 _ _).
    rewrite <- !cat_comp_assoc.
    now rewrite <- (coproduct_universality_1 _ _).
  - rewrite cat_comp_assoc.
    rewrite <- (coproduct_universality_2 _ _).
    rewrite <- !cat_comp_assoc.
    now rewrite <- (coproduct_universality_2 _ _).
Qed.

Lemma coproduct_map_id:
  forall (C: Category)(coprod: forall (X Y: C), Coproduct C X Y)
         (X X': C),
    [Id X \+ Id X' with coprod] == Id (coprod X X').
Proof.
  intros.
  unfold coproduct_map.
  rewrite !cat_comp_id_dom.
  symmetry.
  now apply (coproduct_uniqueness); rewrite !cat_comp_id_cod.
Qed.

(** Isomorphic **)
Lemma coproduct_isomorphic:
  forall (C: Category)(X Y: C)(P Q: Coproduct C X Y),
    P === Q in C.
Proof.
  intros; simpl; unfold isomorphic.
  exists [in1_{Q}, in2_{Q} from P], [in1_{P}, in2_{P} from Q]; split.
  - rewrite (coproduct_uniqueness (i1:=in1_{P})(i2:=in2_{P})(u:=Id P));
      try now rewrite cat_comp_id_cod.
    apply coproduct_uniqueness.
    + rewrite cat_comp_assoc.
      rewrite <- (coproduct_universality_1 (IsCoproduct:=P)).
      now rewrite <- (coproduct_universality_1 (IsCoproduct:=Q)).
    + rewrite cat_comp_assoc.
      rewrite <- (coproduct_universality_2 (IsCoproduct:=P)).
      now rewrite <- (coproduct_universality_2 (IsCoproduct:=Q)).
  - rewrite (coproduct_uniqueness (i1:=in1_{Q})(i2:=in2_{Q})(u:=Id Q));
      try now rewrite cat_comp_id_cod.
    apply coproduct_uniqueness.
    + rewrite cat_comp_assoc.
      rewrite <- (coproduct_universality_1 (IsCoproduct:=Q)).
      now rewrite <- (coproduct_universality_1 (IsCoproduct:=P)).
    + rewrite cat_comp_assoc.
      rewrite <- (coproduct_universality_2 (IsCoproduct:=Q)).
      now rewrite <- (coproduct_universality_2 (IsCoproduct:=P)).
Qed.

(** Examples **)
Inductive coproduct (A B: Type): Type :=
| inj1: A -> coproduct A B
| inj2: B -> coproduct A B.

Program Definition coproduct_of_Types (X Y: Type)
  : Coproduct Types X Y :=
  [Coproduct (coproduct X Y)
    by (fun P f g xy => match xy with
                        | inj1 _ x => f x
                        | inj2 _ y => g y
                        end)
   with @inj1 X Y, @inj2 X Y].
Next Obligation.
  destruct x as [x | y].
  - now rewrite H.
  - now rewrite H0.
Qed.

Program Definition coproduct_setoid (X Y: Setoid) :=
  [Setoid by (fun a b => match a, b with
                         | inj1 _ x, inj1 _ x' => x == x' in X
                         | inj2 _ y, inj2 _ y' => y == y' in Y
                         | _, _ => False
                         end)].
Next Obligation.
  - now intros [x | y].
  - now intros [x | y] [x' | y'].
  - intros [x | y] [x' | y'] [x'' | y'']; try contradiction;
      now apply transitivity.
Qed.

Program Instance inj1_proper (X Y: Setoid)
  : Proper ((== in X) ==> (== in coproduct_setoid X Y)) (@inj1 X Y).

Program Instance inj2_proper (X Y: Setoid)
  : Proper ((== in Y) ==> (== in coproduct_setoid X Y)) (@inj2 X Y).

Program Definition coproduct_of_Setoids (X Y: Setoid)
  : Coproduct Setoids X Y :=
  [Coproduct (coproduct_setoid X Y)
    by (fun P f g => [xy :-> match xy with
                             | inj1 _ x => f x
                             | inj2 _ y => g y
                             end])
   with [Map by @inj1 X Y],
        [Map by @inj2 X Y]].
Next Obligation.
  intros [x | y] [x' | y']; try contradiction; now apply map_proper.
Qed.
Next Obligation.
  destruct x as [x | y]; symmetry.
  - now apply H.
  - now apply H0.
Qed.

Definition coproduct_hom (C D: Category)(X Y: coproduct C D): Setoid :=
  match X, Y with
  | inj1 _ X, inj1 _ Y => C X Y
  | inj2 _ X, inj2 _ Y => D X Y
  | _, _ => empty_setoid
  end.

Program Definition coproduct_category (C D: Category): Category :=
  [Category by (@coproduct_hom C D)
   with (fun X Y Z f g => _),
        (fun X => match X with
                  | inj1 _ X => Id X
                  | inj2 _ X => Id X
                  end)].
Next Obligation.
  destruct X as [X | X], Y as [Y | Y], Z as [Z | Z]; simpl in *;
    try contradiction.
  - exact (g \o f).
  - exact (g \o f).
Defined.
Next Obligation.
  - now destruct X as [X | X], Y as [Y | Y], Z as [Z | Z]; 
      intros f f' Heqf g g' Heqg; simpl in *;
        try contradiction; rewrite Heqf, Heqg.
  - destruct X as [X | X], Y as [Y | Y], Z as [Z | Z], W as [W | W];
      simpl in *; try contradiction;
        now rewrite !cat_comp_assoc.
  - destruct X as [X | X], Y as [Y | Y];
      simpl in *; try contradiction;
        now rewrite cat_comp_id_dom.
  - destruct X as [X | X], Y as [Y | Y];
      simpl in *; try contradiction;
        now rewrite cat_comp_id_cod.
Qed.

Definition fobj_for_coproduct_of_Cat (C D: Category)
           (E: Category)(F: C --> E)(G:D --> E)
  : coproduct_category C D -> E :=
  fun X => match X with
           | inj1 _ X => F X
           | inj2 _ X => G X
           end.

Program Definition functor_for_coproduct_of_Cat (C D: Category)
        (E: Category)(F: C --> E)(G:D --> E)
  : (coproduct_category C D) --> E :=
  let fobj := fobj_for_coproduct_of_Cat F G in
  [Functor by (fun X Y =>
                 match X as X', Y as Y' return
                       (coproduct_category C D) X' Y' ->
                       E (fobj X')
                         (fobj Y') with
                 | inj1 _ X, inj1 _ Y => fun f => fmap F f
                 | inj2 _ X, inj2 _ Y => fun f => fmap G f
                 | _, _ => fun f => match f with end
                 end)].
Next Obligation.
  - now destruct X as [X | X], Y as [Y | Y];
      intros f f' Heq; simpl in *;
        try contradiction; rewrite Heq.
  - now destruct X as [X | X], Y as [Y | Y], Z as [Z | Z]; simpl in *;
      try contradiction; rewrite fmap_comp.
  - now destruct X; simpl; rewrite fmap_id.
Qed.

Program Definition coproduct_of_Cat (C D: Category)
  : Coproduct Cat C D :=
  [Coproduct (coproduct_category C D)
    by @functor_for_coproduct_of_Cat C D
   with [Functor by f :-> f with X :-> inj1 D X],
        [Functor by f :-> f with X :-> inj2 C X]].
Next Obligation.
  - destruct X as [X | X], Y as [Y | Y]; simpl in *;
      try contradiction; apply hom_eq_sym.
    + now apply H.
    + now apply H0.
Qed.

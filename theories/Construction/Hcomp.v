Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.
Require Import COC.Construction.Cat.

Module Hcomp.
  (* 
                 -- G -> 
                /   |   \
    C -- F --> D    S    E 
                \   V   /
                 -- H -> 
             ||
             \/

        -- G o F ->
       /     |     \
      C    S o F    E
       \     V     /
        -- H o F ->
   *)
  Program Definition dom {C D E: Category}
        (F: Functor C D){G H: Functor D E}(S: Natrans G H)
  : Natrans (G \o{Cat} F) (H \o{Cat} F) :=
    Natrans.build _ _ (fun X => S (F X)).
  Next Obligation.
    now rewrite Natrans.naturality; simpl.
  Qed.

  (* 
      -- F -> 
     /   |   \
    C    S    D -- H -> H
     \   V   /
      -- G -> 
             ||
             \/

        -- H o F ->
       /     |     \
      C    H o S    E
       \     V     /
        -- H o G ->
   *)
  Program Definition cod {C D E: Category}
          {F G: Functor C D}(S: Natrans F G)(H: Functor D E)
    : Natrans (H \o{Cat} F) (H \o{Cat} G) :=
    Natrans.build _ _ (fun X => fmap H (S X) ).
  Next Obligation.
    now rewrite <- !fnC, Natrans.naturality.
  Qed.

  (* 
      -- F ->   -- G ->
     /   |   \ /   |   \
    C    S    D    T    E
     \   V   / \   V   /
      -- F'->   -- G'->
             ||
             \/

        -- G o F ->
       /     |     \
      C    T o S    E
       \     V     /
        -- G'o F'->
   *)
  Program Definition both {C D E: Category}
          {F F': Functor C D}(S: Natrans F F')
          {G G': Functor D E}(T: Natrans G G')
    : Natrans (G \o{Cat} F) (G' \o{Cat} F') :=
    Natrans.build _ _ (fun X => T (F' X) \o fmap G (S X) ).
  Next Obligation.
    rewrite catCa, <- fnC, !Natrans.naturality.
    now rewrite <- catCa, <- !fnC.
  Qed.
    

  Module Ex.
    Notation "S \oF F" := (@dom _ _ _ F _ _ S) (at level 50, left associativity).
    Notation "F \Fo S" := (@cod _ _ _ _ _ S F) (at level 50, left associativity).
    Notation "T \vo S" := (@both _ _ _ _ _ S _ _ T) (at level 50, left associativity).
  End Ex.
  Import Ex.


  (* 以前の定義だとそもそも型が合わずに Lemma コマンドが失敗する *)
  Lemma dom_compose_cod:
    forall {C D E K: Category}
           (F: Functor C D){G H: Functor D E}(S: Natrans G H)(I: Functor E K),
      (I \Fo (S \oF F) == (I \Fo S) \oF F :> Natrans.setoid _ _)%category.
  Proof.
    simpl; intros.
    intros X; simpl.
    apply reflexivity.
  Qed.

  Lemma dom_compose_v:
    forall {C D E: Category}
           (F: Functor C D){G H: Functor D E}(S: Natrans G H),
      (S \oF F == S \vo (Natrans.id F) :> Natrans.setoid _ _)%category.
  Proof.
    simpl; intros.
    intros X; simpl.
    apply symmetry.
    eapply transitivity; [| apply Category.comp_id_dom ].
    apply Category.comp_subst; [apply Functor.fmap_id | apply reflexivity].
  Qed.

  Lemma cod_compose_v:
    forall {C D E: Category}
           {F G: Functor C D}(S: Natrans F G)(H: Functor D E),
      (H \Fo S == (Natrans.id H) \vo S :> Natrans.setoid _ _)%category.
  Proof.
    simpl; intros.
    intros X; simpl.
    apply symmetry.
    apply Category.comp_id_cod.
  Qed.
End Hcomp.
Export Hcomp.Ex.
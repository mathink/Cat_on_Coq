(* -*- mode: coq -*- *)
(* Time-stamp: <2014/11/29 0:59:43> *)
(*
  Natrans.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Require Import Category Functor.

(** * 自然変換：函手の間のモルフィズム *)
Class isNatrans (C D: Category)(F G: Functor C D)(natrans: forall X, D (F X) (G X)): Prop :=
  naturality:
    forall (X Y: C)(f: C X Y),
      natrans Y \o fmap F f == fmap G f \o natrans X.
Arguments naturality {C D F G natrans}(N){X Y f}: rename.

Structure Natrans (C D: Category)(F G: Functor C D) :=
  { natrans:> forall X, D (F X) (G X);
    prf_Natrans:> isNatrans natrans }.
Existing Instance prf_Natrans.
Notation makeNatrans natrans := (@Build_Natrans _ _ _ _ natrans _).
Notation "[: X .. Y :=> F :]" := 
  (makeNatrans (fun X => .. (makeNatrans (fun Y => F)) ..))
    (at level 200, X binder, right associativity,
     format "'[' [: X .. Y :=> '/ ' F :] ']'").

(** ** def: natural isomorphic *)
Definition natural_isomorphism
           (C D: Category)(F G: Functor C D)(S: Natrans F G) :=
  forall X: C, exists g, Iso (S X) g.


(** ** 自然変換の垂直合成  *)
Program Definition compose_Natrans (C D: Category)(F G H: Functor C D)
           (S: Natrans F G)(T: Natrans G H): Natrans F H :=
  {| natrans X := T X \o S X |}.
Next Obligation.
  intros X Y f; simpl.
  now rewrite compose_assoc, (naturality S), <-compose_assoc, (naturality T), compose_assoc.
Qed.
 
Program Definition id_Natrans (C D: Category)(F: Functor C D): Natrans F F :=
  {| natrans X := Id (F X) |}.
Next Obligation.
  intros X Y f; simpl.
  now rewrite identity_dom, identity_cod.
Qed.
 
Definition equal_Natrans (C D: Category)(F G: Functor C D)(S T: Natrans F G) :=
  forall X: C, S X == T X.
Arguments equal_Natrans {C D F G} / S T.
 
Instance equal_Natrans_Equiv (C D: Category)(F G: Functor C D)
: Equivalence (@equal_Natrans C D F G).
Proof.
  split; simpl.
  - now intros S X.
  - now intros S T Heq X; rewrite Heq.
  - now intros S T U Heq1 Heq2 X; rewrite Heq1.
Qed.
 
Definition equal2_Natrans
           {C D: Category}
           {F G: Functor C D}(S: Natrans F G)
           {F' G': Functor C D}(T: Natrans F' G') :=
  forall X: C, S X ==_H T X.

Definition Setoid_Natrans (C D: Category)(F G: Functor C D) :=
  Build_Setoid (equal_Natrans_Equiv F G).
 
 
Instance Compose_Natrans (C D: Category): Compose (@Setoid_Natrans C D) :=
  { compose := @compose_Natrans C D  }.
Proof.
  intros F G H S S' HeqS T T' HeqT X; simpl.
  now rewrite (HeqS X), (HeqT X).
Defined.
 
Instance Identity_Natrans (C D: Category): Identity (@Setoid_Natrans C D) :=
  { identity := @id_Natrans C D  }.
 
(** ** Example: Fun  *)
Instance Fun_IsCategory (C D: Category)
: isCategory (Compose_Natrans C D) (@Identity_Natrans C D).
Proof.
  split.
  - now intros X Y Z W f g h x; simpl; rewrite compose_assoc.
  - now intros X Y f x; simpl; rewrite identity_dom.
  - now intros X Y f x; simpl; rewrite identity_cod.
Defined.
 
Definition Fun (C D: Category): Category :=
  Build_Category (Fun_IsCategory C D).
Infix ":=>" := Fun (at level 60, right associativity).

(** ** 自然変換の水平合成 *)
(**
              C -- F --> D
   B -- E --<      S      
              C -- G --> D
 *)
Program Definition dom_comp_Natrans
        (B C D :Category)
        (E: Functor B C)
        (F G: Functor C D)
        (S: Natrans F G)
: Natrans (F \o E) (G \o E) := [: X :=> S (E X) :].
Next Obligation.
  intros X Y f; simpl.
  now rewrite (naturality S).
Qed.        
        
(**
   C -- F --> D
        S       >-- H --> E
   C -- G --> D
 *)
Program Definition cod_comp_Natrans
        (C D E :Category)
        (F G: Functor C D)
        (S: Natrans F G)
        (H: Functor D E)
: Natrans (H \o F) (H \o G) := [: X :=> fmap H (S X) :].
Next Obligation.
  intros X Y f; simpl.
  now rewrite <- (fmap_comp H), (naturality S), <- (fmap_comp H).
Qed.        

(**

   C -- F --> D -- G --> E
        S          T
   C -- F'--> D -- G'--> E

  *)
Program Definition h_compose_Natrans_dc
        (C D E: Category)
        (F G: Functor C D)
        (F' G': Functor D E)
        (S: Natrans F G)
        (T: Natrans F' G')
: Natrans (F' \o F) (G' \o G) :=
  [: X :=> cod_comp_Natrans S G' X \o dom_comp_Natrans F T X :].
Next Obligation.
  intros X Y f; simpl.
  rewrite <- (naturality T).
  rewrite <- (compose_assoc _ _ (fmap G' (fmap G f))).
  rewrite <- (fmap_comp G').
  rewrite <- (naturality T).
  rewrite (compose_assoc _ _ (T (G Y))).
  rewrite <- (fmap_comp F').
  rewrite <- (naturality S).
  reflexivity.
Qed.

Program Definition h_compose_Natrans_cd
        (C D E: Category)
        (F G: Functor C D)
        (F' G': Functor D E)
        (S: Natrans F G)
        (T: Natrans F' G')
: Natrans (F' \o F) (G' \o G) :=
  [: X :=> dom_comp_Natrans G T X \o cod_comp_Natrans S F' X :].
Next Obligation.
  intros X Y f; simpl.
  rewrite compose_assoc, <- (fmap_comp F').
  rewrite (naturality S).
  rewrite <- compose_assoc, <- (naturality T).
  rewrite compose_assoc, <- (fmap_comp F').
  reflexivity.
Qed.


(* 上で定義したものたちの間の関係(optional) *)
Lemma dc_equiv_cd 
      (C D E: Category)
      (F G: Functor C D)
      (F' G': Functor D E)
      (S: Natrans F G)
      (T: Natrans F' G'):
  equal_Natrans (h_compose_Natrans_dc S T) (h_compose_Natrans_cd S T).
Proof.
  simpl; intro X; simpl.
  now rewrite (naturality T).
Qed.

Lemma h_compose_Assoc
      (B C D E: Category)
      (F0 G0: Functor B C)
      (F G: Functor C D)
      (F' G': Functor D E)
      (R: Natrans F0 G0)
      (S: Natrans F G)
      (T: Natrans F' G'):
  equal2_Natrans
    (h_compose_Natrans_dc R (h_compose_Natrans_dc S T))
    (h_compose_Natrans_dc (h_compose_Natrans_dc R S) T).
Proof.
  intros X; simpl; apply eq_Hom_def; simpl.
  repeat rewrite <- compose_assoc.
  rewrite <- (naturality T).
  rewrite <- (naturality S).
  rewrite <- (fmap_comp G').

  rewrite <- (naturality T).
  rewrite <- (naturality S).
  reflexivity.
Qed.


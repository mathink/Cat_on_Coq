(* -*- mode: coq -*- *)
(* Time-stamp: <2014/9/23 15:17:15> *)
(*
  Category.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable All Variables.
Set Universe Polymorphism.

(** * 圏：定義と幾つかの性質たち *)

Require Export Setoid.

(** ** Category *)
Class isCategory
      {obj: Type}{arr: obj -> obj -> Setoid}
      (comp: Compose arr)(ident: Identity arr): Prop :=
  { compose_assoc X Y Z W:
      forall (f: arr X Y)(g: arr Y Z)(h: arr Z W),
        (h \o g) \o f == h \o (g \o f);

    identity_dom X Y (f: arr X Y): f \o Id X == f;

    identity_cod X Y (f: arr X Y): Id Y \o f == f }.
Existing Instance compose_Proper.

Structure Category :=
  { obj: Type;
    arr: obj -> obj -> Setoid;
    comp: Compose arr;
    ident: Identity arr;
    
    prf_Category: isCategory comp ident }.
Existing Instance comp.
Existing Instance ident.
Existing Instance prf_Category.
Coercion obj: Category >-> Sortclass.
Coercion arr: Category >-> Funclass.

Notation "g \o{ C } f" := (compose (Compose:=comp C) f g) (at level 55, right associativity).

(** ** dual  *)
Definition  opposite (C: Category): Category :=
  (Build_Category
     (@Build_isCategory
        (@obj C) (fun X Y: @obj C => @arr C Y X)
        (Build_Compose 
           (fun X Y Z f f' Heqf g g' Heqg =>
              (@compose_Proper _ _ (@comp C) Z Y X g g' Heqg f f' Heqf)))
        (@ident C)
        (fun (X Y Z W: obj C) f g h =>
           Equivalence_Symmetric
             _ _ (@compose_assoc _ _ _ _ (prf_Category C) W Z Y X h g f))
        (fun X Y (f: @arr C Y X) => identity_cod f)
        (fun X Y (f: @arr C Y X) => identity_dom f))).
Notation "'op' C" := (opposite C)
    (at level 7, right associativity).

(** ** Example: Setoids  *)
Instance Setoids_IsCategory: isCategory Compose_Map Identity_Map.
Proof.
  split.
  - now intros X Y Z W f g h x.
  - now intros X Y f x.
  - now intros X Y f x.
Defined.

Definition Setoids: Category := Build_Category Setoids_IsCategory.
Canonical Structure Setoids.

(** ** Attribute *)
Definition Iso (C: Category)(X Y: C)(f: C X Y)(g: C Y X) :=
  (g \o f == Id X) /\ (f \o g == Id Y).
Arguments Iso {C X Y} / f g.

Definition iso (C: Category)(X Y: C) :=
  exists (f: C X Y)(g: C Y X), Iso f g.
Arguments iso {C} / X Y.

(** ** Product *)
Class isProd (C: Category)(X Y P: C)(pX: C P X)(pY: C P Y)
      (parr: forall (Q: C)(qX: C Q X)(qY: C Q Y), C Q P)
: Prop :=
  { prod_arr_commute_1:
      forall (Q: C)(qX: C Q X)(qY: C Q Y),
        (pX \o parr Q qX qY) == qX;
    prod_arr_commute_2:
      forall (Q: C)(qX: C Q X)(qY: C Q Y),
        (pY \o parr Q qX qY) == qY;
    prod_universality:
      forall (Q: C)(qX: C Q X)(qY: C Q Y)(f: C Q P),
        (pX \o f == qX) /\ (pY \o f == qY) -> f == parr Q qX qY }.

Structure Prod (C: Category)(X Y: C) :=
  { prod:> C;
    prod_inj_1: C prod X;
    prod_inj_2: C prod Y;
    prod_arr: forall (Q: C)(qX: C Q X)(qY: C Q Y), C Q prod;

    prf_Prod: isProd prod_inj_1 prod_inj_2 prod_arr }.
Existing Instance prf_Prod.
Arguments Prod {C}(X Y).
Notation pi1 P := (prod_inj_1 P).
Notation pi2 P := (prod_inj_2 P).

Lemma Prod_unique (C: Category)(X Y: C)(P Q: Prod X Y):
  iso P Q.
Proof.
  generalize (prod_arr_commute_1 (P:=P)(Q:=Q) (pi1 Q) (pi2 Q)); intro Heqqp1.
  generalize (prod_arr_commute_2 (P:=P)(Q:=Q) (pi1 Q) (pi2 Q)); intro Heqqp2.
  generalize (prod_arr_commute_1 (P:=Q)(Q:=P) (pi1 P) (pi2 P)); intro Heqpq1.
  generalize (prod_arr_commute_2 (P:=Q)(Q:=P) (pi1 P) (pi2 P)); intro Heqpq2.
  remember (prod_arr Q (pi1 P) (pi2 P)) as pq.
  remember (prod_arr P (pi1 Q) (pi2 Q)) as qp.
  exists pq, qp; simpl; split.
  - assert (Heq1: pi1 P \o{ C} qp \o{ C} pq == pi1 P) by
        now rewrite <- compose_assoc, Heqqp1, Heqpq1.
    assert (Heq2: pi2 P \o{ C} qp \o{ C} pq == pi2 P) by
        now rewrite <- compose_assoc, Heqqp2, Heqpq2.
    rewrite (prod_universality (conj Heq1 Heq2)); simpl.
    now rewrite (prod_universality (conj (identity_dom _) (identity_dom _))).
  - assert (Heq1: pi1 Q \o{ C} pq \o{ C} qp == pi1 Q) by
        now rewrite <- compose_assoc, Heqpq1, Heqqp1.
    assert (Heq2: pi2 Q \o{ C} pq \o{ C} qp == pi2 Q) by
        now rewrite <- compose_assoc, Heqpq2, Heqqp2.
    rewrite (prod_universality (conj Heq1 Heq2)); simpl.
    now rewrite (prod_universality (conj (identity_dom _) (identity_dom _))).
Qed.

(** ** Initial *)
Class isInitial (C: Category)(Init: C)(initial: forall X, C Init X): Prop :=
  initial_uniqueness:
    forall (X: C)(f: C Init X), f == initial X.

Structure Initial (C: Category) :=
  { init:> C;
    initial: forall X, C init X;

    prf_Initial: isInitial initial }.
Existing Instance prf_Initial.

Lemma Initial_unique (C: Category)(Init Init': Initial C):
  iso Init Init'.
Proof.
  simpl.
  exists (initial Init Init'), (initial Init' Init); simpl; split;
  now rewrite initial_uniqueness, <- (initial_uniqueness (Id _)).
Qed.

(* TODO: 直積みたいに書き直しましょう *)
(** ** CoProduct *)
Class isCoProd (C: Category)(X Y P: C)(Xp: C X P)(Yp: C Y P): Prop :=
  coprod_universality:
    forall (Q: C)(Xq: C X Q)(Yq: C Y Q),
      Exists! f: C P Q,
        (f \o Xp == Xq) /\ (f \o Yp == Yq).

Structure CoProd (C: Category)(X Y: C) :=
  { coprod:> C;
    coprod_intro_1: C X coprod;
    coprod_intro_2: C Y coprod;

    prf_CoProd: isCoProd coprod_intro_1 coprod_intro_2 }.
Existing Instance prf_CoProd.
Notation "X \+ Y" := (CoProd X Y) (at level 65, left associativity).
Notation tau1 P := (coprod_intro_1 P).
Notation tau2 P := (coprod_intro_2 P).

Lemma CoProd_unique (C: Category)(X Y: C)(P Q: X \+ Y):
  iso P Q.
Proof.
  destruct (coprod_universality (P:=Q) (tau1 P) (tau2 P)) as [qp [[Heqp1 Heqp2] _]].
  destruct (coprod_universality (P:=P) (tau1 Q) (tau2 Q)) as [pq [[Heqq1 Heqq2] _]].
  simpl.
  exists pq, qp; split.
  - rewrite <- Heqq1, <- compose_assoc in Heqp1.
    rewrite <- Heqq2, <- compose_assoc in Heqp2.
    destruct (coprod_universality (P:=P) (tau1 P) (tau2 P)) as [pp [[_ _] HuniqP]].
    rewrite <- (HuniqP _ (conj (identity_cod _) (identity_cod _))).
    rewrite <- (HuniqP _ (conj Heqp1 Heqp2)).
    reflexivity.
  - rewrite <- Heqp1, <- compose_assoc in Heqq1.
    rewrite <- Heqp2, <- compose_assoc in Heqq2.
    destruct (coprod_universality (P:=Q) (tau1 Q) (tau2 Q)) as [qq [[_ _] HuniqQ]].
    rewrite <- (HuniqQ _ (conj (identity_cod _) (identity_cod _))).
    rewrite <- (HuniqQ _ (conj Heqq1 Heqq2)).
    reflexivity.
Qed.

(** ** Terminal *)
Class isTerminal (C: Category)(Term: C)(terminal: forall X, C X Term): Prop :=
  terminal_uniqueness:
    forall (X: C)(f: C X Term), f == terminal X.

Structure Terminal (C: Category) :=
  { term:> C;
    terminal: forall X, C X term;

    prf_Terminal: isTerminal terminal }.
Existing Instance prf_Terminal.

Lemma Terminal_unique (C: Category)(Term Term': Terminal C):
  iso Term Term'.
Proof.
  exists (terminal Term' Term), (terminal Term Term'); simpl; split;
  now rewrite terminal_uniqueness, <- (terminal_uniqueness (Id _)).
Qed.


(** ** Terminal is unit of Product *)
(** X * T == X *)
Lemma Terminal_Product_1 (C: Category)(X: C)(Term: Terminal C)(P: Prod X Term):
  iso P X.
Proof.
  generalize (prod_arr_commute_1 (P:=P)(Id X)(terminal Term X)); intro Heq1.
  generalize (prod_arr_commute_2 (P:=P)(Id X)(terminal Term X)); intro Heq2.
  remember (prod_arr P (Q:=X) (Id X) (terminal Term X)) as Xp.
  exists (pi1 P), Xp; split; simpl ; [| exact Heq1].
  rewrite (prod_universality(P:=P)(qX:=pi1 P)(qY:=pi2 P)(conj (identity_dom _) (identity_dom _)) ).
  apply prod_universality; split.
  - now rewrite <- compose_assoc, Heq1, identity_cod.
  - rewrite (terminal_uniqueness (terminal:=terminal Term) (pi2 P)).
    now apply terminal_uniqueness.
Qed.

(** T * X == X *)
Lemma Terminal_Product_2 (C: Category)(X: C)(Term: Terminal C)(P: Prod Term X):
  iso P X.
Proof.
  generalize (prod_arr_commute_1 (P:=P)(terminal Term X)(Id X)); intro Heq1.
  generalize (prod_arr_commute_2 (P:=P)(terminal Term X)(Id X)); intro Heq2.
  remember (prod_arr P (Q:=X) (terminal Term X) (Id X)) as Xp.
  exists (pi2 P), Xp; split; simpl ; [| exact Heq2].
  rewrite (prod_universality(P:=P)(qX:=pi1 P)(qY:=pi2 P)(conj (identity_dom _) (identity_dom _)) ).
  apply prod_universality; split.
  - rewrite (terminal_uniqueness (terminal:=terminal Term) (pi1 P)).
    now apply terminal_uniqueness.
  - now rewrite <- compose_assoc, Heq2, identity_cod.
Qed.


(** ** Initial is unit of CoProduct *)
(** X + I == X *)
Lemma Initial_CoProduct_1 (C: Category)(X: C)(Init: Initial C)(P: X \+ Init):
  iso X P.
Proof.
  exists (tau1 P).
  destruct (coprod_universality(P:=P)(Id X)(initial Init X)) as [pX [[Heq1 Heq2] _]].
  exists pX; split; [assumption |].
  destruct (coprod_universality(P:=P)(tau1 P)(tau2 P)) as [pp [[_ _] HuniqP]].
  rewrite <- (HuniqP (Id _) (conj (identity_cod _) (identity_cod _))).
  rewrite (HuniqP (tau1 P \o pX)); [reflexivity |]; split.
  - now rewrite compose_assoc, Heq1, identity_dom.
  - rewrite compose_assoc, Heq2, initial_uniqueness.
    now symmetry; apply initial_uniqueness.
Qed.

(** I + X == X *)
Lemma Initial_CoProduct_2 (C: Category)(X: C)(Init: Initial C)(P: Init \+ X):
  iso X P.
Proof.
  exists (tau2 P).
  destruct (coprod_universality(P:=P)(initial Init X)(Id X)) as [pX [[Heq1 Heq2] _]].
  exists pX; split; [assumption |].
  destruct (coprod_universality(P:=P)(tau1 P)(tau2 P)) as [pp [[_ _] HuniqP]].
  rewrite <- (HuniqP (Id _) (conj (identity_cod _) (identity_cod _))).
  rewrite (HuniqP (tau2 P \o pX)); [reflexivity |]; split.
  - rewrite compose_assoc, Heq1, initial_uniqueness.
    now symmetry; apply initial_uniqueness.
  - now rewrite compose_assoc, Heq2, identity_dom.
Qed.


(** ** Product Category *)
(** *** Product of Setoid  *)
Definition equal_Product (A B: Setoid)(p q: A * B) :=
  (fst p == fst q) /\ (snd p == snd q).
Arguments equal_Product A B / p q.

Instance equal_Product_Equiv (A B: Setoid): Equivalence (@equal_Product A B).
Proof.
  split.
  - now intros [a b]; simpl; split.
  - now intros [a b] [a' b']; simpl; intros [Heqa Heqb]; split; symmetry.
  - intros [a b] [a' b'] [a'' b''] [Heqa Heqb] [Heqa' Heqb']; split;
    simpl in *; [transitivity a' | transitivity b']; assumption.
Qed.

Definition Setoid_Product (A B: Setoid): Setoid := 
  Build_Setoid (equal_Product_Equiv A B).
Infix "[x]" := Setoid_Product (at level 55, right associativity).
Canonical Structure Setoid_Product.

(** *** Product of Map  *)
Program Definition Map_Product (A B C D: Setoid)(f: Map A B)(g: Map C D)
: Map (A [x] C) (B [x] D) := [ p :-> (f (fst p), g (snd p)) ].
Next Obligation.
  now intros [a c] [a' c'] [Heqa Heqc]; simpl in *; split; [rewrite Heqa | rewrite Heqc].
Qed.
Notation "f {x} g" := (@Map_Product _ _ _ _ f g)(at level 55, right associativity).


(** *** Product of Category *)
Definition arr_Product (C D: Category) :=
  (fun X Y => (C (fst X) (fst Y)) [x] (D (snd X) (snd Y))).
Arguments arr_Product / C D X Y.

Instance ProductCompose (C D: Category)
: Compose (@arr_Product C D) :=
  { compose X Y Z f g := (fst g \o fst f,snd g \o snd f) }.
Proof.
  intros [X X'] [Y Y'] [Z Z']; simpl;
  intros [f1 f1'] [f2 f2']; simpl; intros [Heqf1 Heqf2];
  intros [g1 g1'] [g2 g2']; simpl; intros [Heqg1 Heqg2].
  now rewrite Heqf1, Heqf2, Heqg1, Heqg2; split.
Defined.

Instance ProductIdentity (C D: Category)
: Identity (@arr_Product C D) :=
  { identity X := (Id (fst X), Id (snd X)) }.

Instance Product_IsCategory (C D: Category)
: isCategory (ProductCompose C D) (@ProductIdentity C D).
Proof.
  split.
  - now intros [X X'] [Y Y'] [Z Z'] [W W']; simpl;
    intros [f f'] [g g'] [h h']; simpl; do 2 rewrite compose_assoc; split.
  - now intros [X X'] [Y Y']; simpl; intros [f f']; simpl;
    do 2 rewrite identity_dom; split.
  - now intros [X X'] [Y Y']; simpl; intros [f f']; simpl;
    do 2 rewrite identity_cod; split.
Qed.

Definition Product_Category (C D: Category): Category :=
  Build_Category (Product_IsCategory C D).
Infix "[*]" := Product_Category (at level 70, right associativity).
Set Implicit Arguments.
Unset Strict Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Setoid
        COC.Category
        COC.Construction
        COC.Constitution.

Require Import COC.Adjunction.Exponential.

(** * Cartesian Closed Cccegory **)
(**
以下を見たす圏を Cartesian Closed Cccegory と呼ぶ
- 終対象を持つ
- 任意の二対象の積を持つ
- 任意の二対象の羃を持つ
 **)

Module CCC.
  Structure type  :=
    make {
        category: Category;
        terminal: Terminal category;
        prod: forall (X Y: category), Product X Y;
        exp: forall (X Y: category), Exponential prod X Y
      }.

  Module Ex.
    Notation CCC := type.
    Coercion category: CCC >-> Category.

    Delimit Scope ccc_scope with ccc.
    
    Infix "X [*] Y" := (@prod _ X Y) (at level 40, left associativity): ccc_scope.
    Notation  "Y ^ X" := (@exp _ X Y): ccc_scope.
    Notation "'1'" := (@terminal _): ccc_scope.
  End Ex.
End CCC.
Export CCC.Ex.

(** * Setoids is CCC **)
Section SetoidsIsCCC.
  (** ** unit is a terminal object in Setoids **)
  Canonical Structure unit_setoid :=
    @Setoid.make _ (@eq unit) _.

  Program Definition to_unit_setoid (X: Setoids): Map X unit_setoid :=
    [ x :-> tt].
  Next Obligation.
    intros x y Heq; reflexivity.
  Qed.

  Program Instance unit_setoid_is_terminal: isTerminal (@to_unit_setoid).
  Next Obligation.
    destruct (f x); reflexivity.
  Qed.

  Definition unit_setoid_terminal :=
    Terminal.make unit_setoid_is_terminal.

  (** ** Prod.setoid X Y is a product of X and Y in Setoids **)
  Program Definition Prod_fst_map (X Y: Setoids): Setoids (X [*] Y) X :=
    [ xy :-> Prod.fst xy ].
  Next Obligation.
    now intros [x y] [x' y'] [Heqx Heqy]; simpl in *.
  Qed.

  Program Definition Prod_snd_map (X Y: Setoids): Setoids (X [*] Y) Y :=
    [ xy :-> Prod.snd xy ].
  Next Obligation.
    now intros [x y] [x' y'] [Heqx Heqy]; simpl in *.
  Qed.

  Program Definition Prod_prod_map (X Y Z: Setoids)(f: Setoids Z X)(g: Setoids Z Y)
    : Setoids Z (X [*] Y) :=
    [ z :-> (f z, g z)%cat ].
  Next Obligation.
    intros z z' Heqz; simpl; rewrite Heqz; split; reflexivity.
  Qed.
  
  Program Instance Prod_is_product (X Y: Setoids)
    : isProduct (Prod_fst_map X Y) (Prod_snd_map X Y) (@Prod_prod_map X Y).
  Next Obligation.
    intros f f' Heqf g g' Heqg; simpl.
    intros x; split.
    - now apply Heqf.
    - now apply Heqg.
  Qed.
  Next Obligation.
    split; intros x; reflexivity.
  Qed.

  Definition Prod_product (X Y: Setoids) :=
    Product.make (Prod_is_product X Y).

  (** ** Map.setoid X Y is a exponential of X and Y in Setoids **)
  Program Definition apply_map (X Y: Setoids): Setoids ((Map.setoid X Y) [*] X) Y :=
    [ fx :-> let (f,x) := fx in f x ].
  Next Obligation.
    now intros [f x] [g y] [Heqfg Heqxy]; simpl in *; rewrite Heqxy; apply Heqfg.
  Qed.

  Program Instance make_proper (X Y: Setoids)
    : Proper ((==:> X) ==> (==:> Y) ==> (==:> X[*]Y)) (@Prod.make X Y).
  Next Obligation.
    now intros x x' Heqx y y' Heqy; simpl; split.
  Qed.
  
  Program Definition exp_univ_map (X Y Z: Setoids)(f: Setoids (Z [*] X) Y)
    : Setoids Z (Map.setoid X Y) :=
    [ z x :-> f (z,x) ].
  Next Obligation.
    now intros x x' Heq; rewrite Heq.
  Qed.
  Next Obligation.
    now intros z z' Heqz x; simpl; rewrite Heqz.
  Qed.
  
  Program Instance Map_setoid_is_exponential (X Y: Setoids)
    : isExponential (prod:=Prod_product) (apply_map X Y) (@exp_univ_map X Y).
  Next Obligation.
    rename X0 into Z.
    intros f f' Heqf; simpl in *.
    intros z x.
    now apply Heqf.
  Qed.
  Next Obligation.
    destruct x; reflexivity.
  Qed.
  Next Obligation.
    now rewrite (H (x, x0)).
  Qed.

  Definition Map_setoid_exponential (X Y: Setoids) :=
    Exponential.make (Map_setoid_is_exponential X Y).

  (** ** Setoids is CCC **)
  Canonical Structure Setoids_ccc :=
    CCC.make unit_setoid_terminal Map_setoid_exponential.
End SetoidsIsCCC.



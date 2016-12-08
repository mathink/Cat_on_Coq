(** * Functor **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

From COC.Base Require Import Category Functor.


Class IsNatrans
      (C D: Category)
      (F G: C --> D)
      (natrans: forall (X: C), D (F X) (G X)) :=
  {
    natrans_naturality:
      forall (X Y: C)(f: C X Y),
        natrans Y \o fmap F f == fmap G f \o natrans X
  }.

Structure Natrans {C D: Category}(F G: C --> D): Type :=
  {
    natrans:> forall X: C, D (F X) (G X);
    natrans_prf:> IsNatrans natrans
  }.
Existing Instance natrans_prf.

Notation "F ==> G" := (Natrans F G).
Notation "[ X 'in' T :=> f 'from' F 'to' G ]" := (@Build_Natrans _ _ F G (fun X: T => f) _).
Notation "[ X :=> f 'from' F 'to' G ]" := [X in _ :=> f from F to G].
Notation "[ X 'in' T :=> f ]" := [X in T :=> f from _ to _].
Notation "[ X :=> f ]" := ([ X in _ :=> f]).

Program Definition Natrans_compose (C D: Category)(F G H: C --> D)(S: F ==> G)(T: G ==> H): F ==> H :=
  [X :=> T X \o S X].
Next Obligation.
  now rewrite cat_comp_assoc, (natrans_naturality (IsNatrans := S)), <- cat_comp_assoc, (natrans_naturality (IsNatrans:=T)), cat_comp_assoc.
Qed.

Program Definition Natrans_id (C D: Category)(F: C --> D): Natrans F F :=
  [X :=> Id (F X)].
Next Obligation.
  now rewrite cat_comp_id_dom, cat_comp_id_cod.
Qed.

Program Definition Natrans_dom_compose (B C D: Category)(E: B --> C)(F G: C --> D)(S: F ==> G): (F \o E) ==> (G \o E) :=
  [X :=> S (E X)].
Next Obligation.
  now rewrite natrans_naturality.
Qed.
Notation "S o> E" := (Natrans_dom_compose E S) (at level 50, left associativity).

Program Definition Natrans_cod_compose (C D E: Category)(F G: C --> D)(H: D --> E)(S: F ==> G): (H \o F) ==> (H \o G) :=
  [X :=> fmap H (S X)].
Next Obligation.
  now rewrite <- !(fmap_comp _), natrans_naturality.
Qed.
Notation "H <o S" := (Natrans_cod_compose H S) (at level 50, left associativity).

Program Definition Natrans_hcompose
        (C D E: Category)
        (F G: C --> D)(H K: D --> E)
        (S: F ==> G)(T: H ==> K)
  : (H \o F) ==> (K \o G) :=
  [ X :=> fmap K (S X) \o T (F X) ].
Next Obligation.
  rewrite cat_comp_assoc, natrans_naturality, <- !cat_comp_assoc.
  rewrite <- !(fmap_comp ).
  now rewrite <- (natrans_naturality (IsNatrans:=S)).
Qed.
Notation "T <o> S" := (Natrans_hcompose S T) (at level 60, right associativity).

Program Definition Natrans_setoid (C D: Category)(F G: C --> D): Setoid :=
  [Setoid by (fun (S T: F ==> G) => forall X, S X == T X)].
Next Obligation.
  intros S T U HeqST HeqTU X.
  now rewrite (HeqST X), (HeqTU X).
Qed.
Canonical Structure Natrans_setoid.

Program Definition Fun (C D: Category): Category :=
  [Category by (@Natrans_setoid C D)
   with (@Natrans_compose C D), (@Natrans_id C D)].
Next Obligation.
  - rename X into F, Y into G, Z into H.
  intros S S' HeqS T T' HeqT X; simpl.
  now rewrite HeqS, HeqT.

  - now rewrite cat_comp_assoc.
    
  - now rewrite cat_comp_id_dom.

    -now rewrite cat_comp_id_cod.
Qed.
Canonical Structure Fun.
Notation "D ^ C" := (Fun C D).

Program Definition Natrans_id_dom (C D: Category)(F: C --> D): (F \o Id C) ==> F :=
  [X :=> fmap F (Id X)].
Next Obligation.
  now rewrite !fmap_id, cat_comp_id_dom, cat_comp_id_cod.
Qed.
Notation "[ * \o '1' ==> * ]" := (Natrans_id_dom _).

Program Definition Natrans_id_dom_inv (C D: Category)(F: C --> D): F ==> (F \o Id C) :=
  [X :=> fmap F (Id X)].
Next Obligation.
  now rewrite !fmap_id, cat_comp_id_dom, cat_comp_id_cod.
Qed.
Notation "[ * ==> * \o '1' ]" := (Natrans_id_dom_inv _).

Program Definition Natrans_id_cod (C D: Category)(F: C --> D): (Id D \o F) ==> F :=
  [X :=> Id (F X)].
Next Obligation.
  now rewrite cat_comp_id_dom, cat_comp_id_cod.
Qed.
Notation "[ '1' \o * ==> * ]" := (Natrans_id_cod _).

Program Definition Natrans_id_cod_inv (C D: Category)(F: C --> D): F ==> (Id D \o F) :=
  [X :=> Id (F X)].
Next Obligation.
  now rewrite cat_comp_id_dom, cat_comp_id_cod.
Qed.
Notation "[ * ==> '1' \o * ]" := (Natrans_id_cod_inv _).

Program Definition Natrans_assoc (B C D E: Category)(F: B --> C)(G: C --> D)(H: D --> E): (H \o (G \o F)) ==> ((H \o G) \o F) :=
  [ X in B :=> Id (H (G (F X)))].
Next Obligation.
  now rewrite cat_comp_id_dom, cat_comp_id_cod.
Qed.
Notation Nassoc := (Natrans_assoc _ _ _).
  
Program Definition Natrans_assoc_inv (B C D E: Category)(F: B --> C)(G: C --> D)(H: D --> E): ((H \o G) \o F) ==> (H \o (G \o F)) :=
  [ X in B :=> Id (H (G (F X)))].
Next Obligation.
  now rewrite cat_comp_id_dom, cat_comp_id_cod.
Qed.
Notation Nassoc_inv := (Natrans_assoc_inv _ _ _).

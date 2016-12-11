(** * Adjunction **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

Class IsAdjunction
      (C D: Category)(F: C --> D)(G: D --> C)
      (lr: forall {c: C}{d: D}, Map (D (F c) d) (C c (G d)))
      (rl: forall {c: C}{d: D}, Map (C c (G d)) (D (F c) d)) :=
  {
    adj_iso_lr_rl:
      forall (c: C)(d: D)(f: D (F c) d),
        rl (lr f) == f;

    adj_iso_rl_lr:
      forall (c: C)(d: D)(g: C c (G d)),
        lr (rl g) == g;

    adj_lr_naturality:
      forall (c c': C)(d d': D)(f : C c' c)(g: D d d')(h: D (F c) d),
        lr (g \o h \o fmap F f) == fmap G g \o lr h \o f
  }.

Structure Adjunction (C D: Category)(F: C --> D)(G: D --> C) :=
  {
    adj_lr: forall {c: C}{d: D}, Map (D (F c) d) (C c (G d));
    adj_rl: forall {c: C}{d: D}, Map (C c (G d)) (D (F c) d);

    prf:> IsAdjunction (@adj_lr) (@adj_rl)
  }.
Existing Instance prf.

Notation "F -| G ; C <--> D" := (Adjunction (C:=C) (D:=D) F G) (at level 40, no associativity).
Notation "F -| G" := (F -| G ; _ <--> _) (at level 40, no associativity).
Notation "[ 'Adj' 'of' F , G 'by' lr , rl ]" :=
  (@Build_Adjunction _ _ F G lr rl _).
Notation "[ 'Adj' 'by' lr , rl ]" := [Adj of _, _ by lr, rl].
Notation "[ F -| G 'by' lr , rl ]" := [Adj of F,G by lr,rl].

(*  *)
Lemma adj_rl_naturality
      (C D: Category)(F: C --> D)(G: D --> C)
      (adj: F -| G):
  forall (c c': C)(d d': D)(f : C c' c)(g: D d d')(h: C c (G d)),
    adj_rl adj (fmap G g \o h \o f) == g \o adj_rl adj h \o fmap F f.
Proof.
  intros.
  rewrite <- (adj_iso_rl_lr (IsAdjunction:=adj) h) at 1.
  now rewrite <- adj_lr_naturality, adj_iso_lr_rl.
Qed.

(** unit of adjunction **)
Program Definition adj_unit
        (C D: Category)(F: C --> D)(G: D --> C)(adj: F -| G)
  : (Id C) ==> (G \o F) :=
  [ c :=> adj_lr adj (Id (F c))].
Next Obligation.
  rewrite <- cat_comp_id_cod.
  rewrite <- (fmap_id (F Y)).
  rewrite <- adj_lr_naturality.
  rewrite !cat_comp_id_cod.
  symmetry.
  rewrite <- cat_comp_id_dom, cat_comp_assoc.
  rewrite <- adj_lr_naturality.
  now rewrite cat_comp_id_cod, fmap_id, cat_comp_id_dom.
Qed.

(** counit of adjunction *)
Program Definition adj_counit
        (C D: Category)(F: C --> D)(G: D --> C)(adj: F -| G):
  (F \o G) ==> (Id D)  :=
  [d :=> adj_rl adj (Id (G d))].
Next Obligation.
  intros; simpl.
  rewrite <- cat_comp_id_cod.
  rewrite <- adj_rl_naturality.
  rewrite fmap_id, cat_comp_id_cod.
  symmetry.
  rewrite <- cat_comp_id_dom, <- fmap_id, cat_comp_assoc.
  rewrite <- adj_rl_naturality.
  now rewrite !cat_comp_id_dom, cat_comp_id_cod.
Qed.

(* Adjunction by unit and counit *)
Definition adj_triangle 
           (C D: Category)
           (F: C --> D)(G: D --> C)
           (au: (Id C) ==> (G \o F))
           (ac: (F \o G) ==> (Id D)) :=
  ([1 \o * ==> *]
     \o (ac o> F)
     \o Nassoc
     \o (F <o au)
     \o [* ==> * \o 1]
   == Id F
    in Natrans_setoid _ _)      (* acF \o Fau == Id_F *)
  /\
  ([* \o 1 ==> *]
     \o (G <o ac)
     \o Nassoc_inv
     \o (au o> G)
     \o [* ==> 1 \o *]
   == Id G
    in Natrans_setoid _ _).     (* Gac \o auG == Id_G *)

Lemma adj_satisfies_triangle:
  forall (C D: Category)(F: C --> D)(G: D --> C)(adj: F -| G),
    adj_triangle (adj_unit adj) (adj_counit adj).
Proof.
  intros; split; simpl; [intro c | intro d];
    rewrite ?cat_comp_id_dom, ?cat_comp_id_cod.
  - rewrite <- cat_comp_id_cod, <- adj_rl_naturality.
    rewrite fmap_id, !cat_comp_id_cod.
    now rewrite adj_iso_lr_rl.
  - rewrite <- cat_comp_id_dom, cat_comp_assoc, <- adj_lr_naturality.
    rewrite fmap_id, !cat_comp_id_dom.
    now rewrite adj_iso_rl_lr.
Qed.

Program Definition Adjunction_by_unit_and_counit
        (C D: Category)
        (F: C --> D)(G: D --> C)
        (au: (Id C) ==> (G \o F))
        (ac: (F \o G) ==> (Id D))
        (Hadj: adj_triangle au ac)
  : F -| G :=
  [Adj by (fun c d => [g in D (F c) d :-> fmap G g \o au c]),
          (fun c d => [f in C c (G d) :-> ac d \o fmap F f])].
Next Obligation.
  now intros g g' Heq; rewrite Heq.
Qed.
Next Obligation.
  now intros f f' Heq; rewrite Heq.
Qed.
Next Obligation.
  - rewrite fmap_comp, <- cat_comp_assoc.
    rewrite (natrans_naturality (IsNatrans:=ac) f); simpl.
    rewrite cat_comp_assoc.
    destruct Hadj as [HF HG].
    generalize (HF c); simpl.
    rewrite !cat_comp_id_cod, !cat_comp_id_dom.
    now intros H; rewrite H, cat_comp_id_dom.
  - rewrite fmap_comp, cat_comp_assoc.
    rewrite <- (natrans_naturality (IsNatrans:=au) g); simpl.
    rewrite <- cat_comp_assoc.
    destruct Hadj as [HF HG].
    generalize (HG d); simpl.
    rewrite !cat_comp_id_cod, !cat_comp_id_dom.
    now intros H; rewrite H, cat_comp_id_cod.
  - rewrite !fmap_comp, !cat_comp_assoc.
    now rewrite (natrans_naturality (IsNatrans:=au) f).
Qed.


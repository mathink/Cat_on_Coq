(** * Adjunction and Kan extension **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Base.Main
        COC.Adj.Main
        COC.KanExt.Lan
        COC.KanExt.Ran.

Class PreserveLan
      {C D E E': Category}{F: C --> E}{K: C --> D}
      (lan: Lan F K)
      (L: E --> E')
      (new: forall (S: D --> E'),
          (L \o F) ==> (S \o K) ->
          (L \o lanF lan) ==> S) :=
  preserve_lan:
    IsLan (lanF:=L \o lanF lan) (Nassoc \o (L <o lanN lan)) (@new).

(** left adjoint preserve lan **)
Program Instance left_adjoint_preserve_lan
        (C D E E': Category)
        (F: C --> E)(K: C --> D)(lan: Lan F K)
        (L: E --> E')(R: E' --> E)(adj: L -| R)
  : PreserveLan
      (fun S e =>
         [ 1 \o * ==> * ]
           \o (adj_counit adj o> S)
           \o Nassoc
           \o (L <o (lanU lan
                           (Nassoc
                              \o (R <o e)
                              \o Nassoc_inv
                              \o (adj_unit adj o> F)
                              \o [ * ==> 1 \o * ])))).
Next Obligation.
  - simpl; intros.
    rewrite !cat_comp_id_cod, !cat_comp_assoc, <- fmap_comp; simpl.
    generalize (lan_universality
                  (IsLan:=lan)
                  (Nassoc \o (R <o e) \o Nassoc_inv \o (adj_unit adj o> F) \o [ * ==> 1 \o * ]) X); simpl.
    intro H; rewrite H; simpl.
    rewrite cat_comp_id_cod, cat_comp_id_dom.
    rewrite <- (cat_comp_id_cod (adj_rl _ _ \o _)).
    rewrite <- adj_rl_naturality.
    rewrite fmap_id, !cat_comp_id_cod.
    rewrite <- (cat_comp_id_dom (fmap R _ \o _)), cat_comp_assoc.
    rewrite adj_rl_naturality.
    now rewrite adj_iso_lr_rl, fmap_id, !cat_comp_id_dom.
  - simpl; intros.
    rewrite !cat_comp_id_cod, <- (cat_comp_id_cod (adj_rl _ _ \o _)).
    rewrite <- adj_rl_naturality.
    rewrite fmap_id, !cat_comp_id_cod.
    generalize (lan_uniqueness
                  (IsLan:=lan)
                  (e:=Nassoc \o (R <o e) \o Nassoc_inv \o (adj_unit adj o> F) \o Natrans_id_cod_inv F)
                  (u:=(R <o u) \o Nassoc_inv \o{Fun _ _} (adj_unit adj o> lanF lan) \o{Fun _ _} [* ==> 1 \o * ]));
      simpl; intros Heq.
    rewrite <- Heq.
    + rewrite !cat_comp_id_cod.
      rewrite adj_rl_naturality.
      now rewrite fmap_id, cat_comp_id_dom, adj_iso_lr_rl, cat_comp_id_dom.
    + intros c.
      rewrite !cat_comp_id_cod.
      rewrite <- adj_lr_naturality.
      rewrite cat_comp_id_cod.
      rewrite (fmap_id (F:=L)), cat_comp_id_dom.
      rewrite <- adj_lr_naturality.
      rewrite (fmap_id (F:=L)), !cat_comp_id_dom.
      rewrite <- H.
      rewrite cat_comp_id_cod.
      rewrite <- (cat_comp_id_cod (u (K c) \o _)).
      rewrite (adj_lr_naturality (IsAdjunction:=adj) _ _ (u (K c))).
      now rewrite fmap_id, cat_comp_id_cod.
Qed.

(** lan from adjunction **)
Program Definition lan_from_adjunction
        (C D: Category)
        (F: C --> D)(G: D --> C)(adj: F -| G)
  : Lan (Id C) F :=
  [Lan by (fun S e => ([ * \o 1 ==> *]
                         \o (S <o adj_counit adj)
                         \o Nassoc_inv
                         \o (e o> G)
                         \o [* ==> 1 \o *]))
   with G, adj_unit adj].
Next Obligation.
  rewrite <- !cat_comp_assoc.
  rewrite <- (fmap_id (F:=S) (F X)), <- fmap_comp.
  rewrite !cat_comp_id_dom.
  rewrite cat_comp_assoc.
  generalize (natrans_naturality (IsNatrans:=e) (adj_lr adj (Id F X))); simpl; intros H; rewrite H; clear H.
  rewrite <- cat_comp_assoc, <- fmap_comp.
  rewrite cat_comp_assoc.
  rewrite <- adj_rl_naturality.
  rewrite !fmap_id, !cat_comp_id_cod.
  now rewrite adj_iso_lr_rl, fmap_id, cat_comp_id_cod.

  rewrite !cat_comp_id_cod, cat_comp_id_dom.
  rewrite <- H.
  rewrite <- cat_comp_assoc.
  rewrite <- (natrans_naturality (IsNatrans:=u) ((adj_rl adj) (Id G X))).
  rewrite cat_comp_assoc.
  rewrite <- (cat_comp_id_dom (fmap G _ \o _)), cat_comp_assoc.
  rewrite <- adj_lr_naturality, fmap_id, !cat_comp_id_dom.
  now rewrite adj_iso_rl_lr, cat_comp_id_dom.
Qed.

(** ran from adjunction **)
Program Definition ran_from_adjunction
        (C D: Category)
        (F: C --> D)(G: D --> C)(adj: F -| G)
  : Ran (Id D) G :=
  [Ran by (fun S e =>
             [1 \o * ==> *]
               \o (e o> F)
               \o Nassoc
               \o (S <o adj_unit adj)
               \o  [* ==> * \o 1])
   with F, adj_counit adj].
Next Obligation.
  rewrite !cat_comp_id_cod, !cat_comp_id_dom.
  rewrite <- cat_comp_assoc.
  generalize (natrans_naturality (IsNatrans:=e) (adj_rl adj (Id (G X)))); simpl; intros H; rewrite <- H; clear H.
  rewrite cat_comp_assoc, <- fmap_comp.
  rewrite <- (cat_comp_id_dom (_ \o adj_lr adj _)).
  rewrite cat_comp_assoc, <- adj_lr_naturality.
  rewrite !fmap_id, !cat_comp_id_dom.
  now rewrite adj_iso_rl_lr, fmap_id, cat_comp_id_dom.

  rewrite !cat_comp_id_cod, cat_comp_id_dom.
  rewrite <- H.
  rewrite cat_comp_assoc.
  rewrite (natrans_naturality (IsNatrans:=u) (adj_lr adj (Id (F X)))).
  rewrite <- cat_comp_assoc.
  rewrite <- (cat_comp_id_cod (_ \o fmap F _)), <- !cat_comp_assoc.
  rewrite (cat_comp_assoc (fmap F _)).
  rewrite <- adj_rl_naturality, fmap_id, !cat_comp_id_cod.
  now rewrite adj_iso_lr_rl, cat_comp_id_cod.
Qed.

(** adjunction from lan **)
Program Definition counit_from_lan
        (C D: Category)
        (F: C --> D)(G: D --> C)
        (au: (Id C) ==> (G \o F))
        (luniv: forall (S: D --> C),
            (Id C) ==> (S \o F) -> G ==> S)
        (Hlan: IsLan (lanF:=G) au luniv)
        (puniv: forall (S: D --> D),
            (F \o Id C) ==> (S \o F) ->
            (F \o G) ==> S)
        (Hp: PreserveLan (lan:=Build_Lan Hlan)(L:=F) puniv)
  : (F \o G) ==> (Id D) :=
  puniv (Id D) ([* ==> 1 \o *] \o Id F \o [* \o 1 ==> *]).

Lemma counit_from_lan_makes_triangle:
  forall (C D: Category)
         (F: C --> D)(G: D --> C)
         (au: (Id C) ==> (G \o F))
         (luniv: forall (S: D --> C),
             (Id C) ==> (S \o F) -> G ==> S)
         (Hlan: IsLan (lanF:=G) au luniv)
         (puniv: forall (S: D --> D),
             (F \o Id C) ==> (S \o F) ->
             (F \o G) ==> S)
         (Hp: PreserveLan (lan:=Build_Lan Hlan)(L:=F) puniv),
    adj_triangle au (puniv (Id D) ([* ==> 1 \o *] \o Id F \o [* \o 1 ==> *])).
Proof.
  intros; split.
  - simpl; intros c.
    rewrite !cat_comp_id_cod, cat_comp_id_dom.
    generalize (lan_universality (IsLan:=Hp) ([ * ==> 1 \o * ] \o Natrans_id F \o [ * \o 1 ==> * ]) c); simpl.
    rewrite cat_comp_id_cod.
    intros H; rewrite H.
    now rewrite !cat_comp_id_cod.
  -
    generalize (lan_uniqueness (IsLan:=Hlan)(e:=au)(u:=Id G)).
    intros H'; rewrite H'; clear H'.
    + apply lan_uniqueness.
      simpl; intros c.
      rewrite !cat_comp_id_cod, cat_comp_id_dom.
      rewrite cat_comp_assoc.
      rewrite (natrans_naturality (IsNatrans:=au) (au c)); simpl.
      rewrite <- cat_comp_assoc, <- fmap_comp.

      generalize (lan_universality (IsLan:=Hp) ([ * ==> 1 \o * ] \o Natrans_id F \o [ * \o 1 ==> * ]) c); simpl.
      rewrite !cat_comp_id_cod.
      intros H; rewrite H.
      now rewrite !cat_comp_id_cod, !fmap_id, !cat_comp_id_cod.
    + now simpl; intros c; rewrite cat_comp_id_cod.
Qed.

Definition adjunction_from_lan
        (C D: Category)
        (F: C --> D)(G: D --> C)
        (au: (Id C) ==> (G \o F))
        (luniv: forall (S: D --> C),
            (Id C) ==> (S \o F) -> G ==> S)
        (Hlan: IsLan (lanF:=G) au luniv)
        (puniv: forall (S: D --> D),
            (F \o Id C) ==> (S \o F) ->
            (F \o G) ==> S)
        (Hp: PreserveLan (lan:=Build_Lan Hlan)(L:=F) puniv)
  : F -| G :=
  Adjunction_by_unit_and_counit
    (counit_from_lan_makes_triangle Hp).

(** *** 5.3.2 Lan -| Inverse -| Ran **)
Program Definition Inverse_functor_natrans
        (C D: Category)(K: C --> D)
        (E: Category)
        (F G: D --> E)
        (S: F ==> G)
  : (F \o K) ==> (G \o K)  :=
  [c :=> S (K c)].
Next Obligation.
  now rewrite <- natrans_naturality.
Qed.

Program Definition Inverse_functor
        (C D: Category)(K: C --> D)
        (E: Category)
  : (E^D) --> (E^C) :=
  [Functor by S :-> Inverse_functor_natrans K S with F :-> F \o K].
Next Obligation.
  rename X into F, Y into G.
  intros S T Heq c; simpl.
  now rewrite (Heq (K c)).
Qed.

Program Definition Lan_functor
        (C D: Category)(K: C --> D)
        (E: Category)
        (lan: forall (F: C --> E), Lan F K)
  : (E^C) --> (E^D) :=
  [Functor by (fun F G S => lanU (lan F) (lanN (lan G) \o S))
   with `(lanF (lan F))].
Next Obligation.
  - rename X into F, Y into G.
    intros S T Heq d.
    apply (lan_uniqueness (IsLan:=lan F)(e:=lanN (lan G) \o T)).
    rewrite (lan_universality (IsLan:=lan F)(lanN (lan G) \o S)).
    now simpl; intros c; rewrite (Heq c).
  - rename X into F, Y into G, Z into H, f into S, g into T, X0 into d.
    symmetry.
    apply (lan_uniqueness (IsLan:=lan F)(e:=(lanN (lan H) \o T \o S))(u:=(lanU (lan G) (lanN (lan H) \o T))\o (lanU (lan F) (lanN (lan G) \o S)))); simpl; intros c.
    rewrite cat_comp_assoc.
    rewrite (lan_universality (IsLan:=lan F)(lanN (lan G) \o S) c).
    simpl.
    rewrite <- cat_comp_assoc.
    rewrite (lan_universality (IsLan:=lan G)(lanN (lan H) \o T) c).
    simpl.
    now rewrite cat_comp_assoc.
  - rename X into F, X0 into d.
    symmetry.
    apply (lan_uniqueness (IsLan:=lan F)(e:=(lanN (lan F) \o Natrans_id F))(u:=Natrans_id _)); simpl; intros c.
    now rewrite cat_comp_id_cod, cat_comp_id_dom.
Qed.

Program Definition Ran_functor
        (C D: Category)(K: C --> D)
        (E: Category)
        (ran: forall (F: C --> E), Ran F K)
  : (E^C) --> (E^D) :=
  [Functor by (fun F G S => ranU (ran G) (S \o ranN (ran F)))
   with `(ranF (ran F))].
Next Obligation.
  - rename X into F, Y into G.
    intros S T Heq d.
    apply (ran_uniqueness (IsRan:=ran G)(e:=T \o ranN (ran F))).
    rewrite (ran_universality (IsRan:=ran G)(S \o ranN (ran F))).
    now simpl; intros c; rewrite (Heq c).
  - rename X into F, Y into G, Z into H, f into S, g into T, X0 into d.
    symmetry.
    apply (ran_uniqueness (IsRan:=ran H)(e:=((T \o S) \o ranN (ran F)))(u:=(ranU (ran H) (T \o ranN (ran G))) \o (ranU (ran G) (S \o ranN (ran F))))); simpl; intros c.
    rewrite <- cat_comp_assoc.
    rewrite (ran_universality (IsRan:=ran H)(T \o ranN (ran G)) c).
    simpl.
    rewrite cat_comp_assoc.
    rewrite (ran_universality (IsRan:=ran G)(S \o ranN (ran F)) c).
    simpl.
    now rewrite cat_comp_assoc.
  - rename X into F, X0 into d.
    symmetry.
    apply (ran_uniqueness (IsRan:=ran F)(e:=(Natrans_id F \o ranN (ran F)))(u:=Natrans_id _)); simpl; intros c.
    now rewrite cat_comp_id_cod, cat_comp_id_dom.
Qed.

(** Lan -| Inverse **)
Program Definition lan_inverse_adjunction_lr
        (C D: Category)(K: C --> D)
        (E: Category)
        (lan: forall (F: C --> E), Lan F K)
        (F: C --> E)(G: D --> E) :=
  [S in lanF (lan F) ==> G :-> (S o> K) \o lanN (lan F)].
Next Obligation.
  intros S T Heq c; simpl.
  now rewrite (Heq (K c)).
Qed.

Program Definition lan_inverse_adjunction_rl
        (C D: Category)(K: C --> D)
        (E: Category)
        (lan: forall (F: C --> E), Lan F K)
        (F: C --> E)(G: D --> E) :=
  [S in F ==> (G \o K) :-> lanU (lan F) S].
Next Obligation.
  intros S T Heq d; simpl.
  apply (lan_uniqueness (IsLan:=lan F)(e:= T)); simpl; intros c.
  now rewrite (lan_universality (IsLan:=lan F) S c), (Heq c).
Qed.

Program Definition lan_inverse_adjunction
        (C D: Category)(K: C --> D)
        (E: Category)
        (lan: forall (F: C --> E), Lan F K)
  : Lan_functor lan -| Inverse_functor K E :=
  [Adj by lan_inverse_adjunction_lr lan,
          lan_inverse_adjunction_rl lan].
Next Obligation.
  - rename c into F, d into G, f into S, X into d.
    symmetry.
    now apply (lan_uniqueness (IsLan:=lan F)(e:=S o> K \o lanN (lan F))).
  - rename c into F, d into G, g into T, X into c.
    now rewrite (lan_universality (IsLan:=lan F) T c).
  - rename c into F, c' into F', d into G, d' into G', f into S, g into T, h into U, X into c.
    rewrite !cat_comp_assoc.
    now rewrite (lan_universality (IsLan:=lan F') (lanN (lan F) \o S) c); simpl.
Qed.

(** Inverse -| Ran **)
Program Definition ran_inverse_adjunction_lr
        (C D: Category)(K: C --> D)
        (E: Category)
        (ran: forall (F: C --> E), Ran F K)
        (G: D --> E)(F: C --> E) :=
  [S in (G \o K) ==> F :-> ranU (ran F) S].
Next Obligation.
  intros S T Heq d; simpl.
  apply (ran_uniqueness (IsRan:=ran F)(e:= T)); simpl; intros c.
  now rewrite (ran_universality (IsRan:=ran F) S c), (Heq c).
Qed.

Program Definition ran_inverse_adjunction_rl
        (C D: Category)(K: C --> D)
        (E: Category)
        (ran: forall (F: C --> E), Ran F K)
        (G: D --> E)(F: C --> E) :=
  [S in G ==> ranF (ran F) :-> ranN (ran F) \o (S o> K)].
Next Obligation.
  intros S T Heq c; simpl.
  now rewrite (Heq (K c)).
Qed.

Program Definition ran_inverse_adjunction
        (C D: Category)(K: C --> D)
        (E: Category)
        (ran: forall (F: C --> E), Ran F K)
  : Inverse_functor K E -| Ran_functor ran :=
  [Adj by ran_inverse_adjunction_lr ran,
          ran_inverse_adjunction_rl ran].
Next Obligation.
  - rename c into G, d into F, f into S, X into c.
    now rewrite (ran_universality (IsRan:=ran F) S c).
  - rename c into G, d into F, g into S, X into d.
    symmetry.
    now apply (ran_uniqueness (IsRan:=ran F)(e:=ranN (ran F) \o (S o> K))).
  - rename d into F, d' into F', c into G, c' into G', f into T, g into S, h into U, X into d.
    symmetry.
    generalize (ran_uniqueness (IsRan:=ran F')); simpl; intros Huniq.
    eapply (Huniq _ (S \o U \o [c :=> T (K c) from (_ \o _) to (_ \o _)])
                  ((ranU (ran F') (S \o ranN (ran F))) \o (ranU (ran F) U) \o T)); simpl; intros c.
    rewrite <- !cat_comp_assoc.
    rewrite (ran_universality (IsRan:=ran F')(S \o ranN (ran F)) c); simpl.
    rewrite (cat_comp_assoc _ _ (S c)).
    now rewrite (ran_universality (IsRan:=ran F) U c).
Qed.

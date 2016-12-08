(** * Limit **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main COC.Cons.Terminal.

Class IsCone
      (J C: Category)
      (D: J --> C)
      (apex: C)
      (gen: forall i, C apex (D i)) :=
  {
    cone_commute:
      forall i j (u: J i j),
        fmap D u \o gen i == gen j
  }.

Structure Cone (J C: Category)(D: J --> C): Type :=
  {
    cone_apex:> C;
    cone_gen:> forall i, C cone_apex (D i);
    cone_prf:> IsCone cone_gen
  }.
Existing Instance cone_prf.

Notation "[ 'Cone' 'of' D 'by' gen 'from' apex ]" := (@Build_Cone _ _ D apex gen _).
Notation "[ 'Cone' 'by' gen 'from' apex ]" := [Cone of _ by gen from apex].
Notation "[ 'Cone' 'by' gen ]" := [Cone by gen from _].
Notation "[ 'Cone' 'by' i :-> f 'from' apex ]" := [Cone by (fun i => f) from apex].
Notation "[ 'Cone' 'by' i :-> f ]" := [Cone by i :-> f from _].

Class IsLimit (J C: Category)(D: J --> C)
      (obj: Cone D)
      (univ: forall c: Cone D, C c obj) :=
  {
    limit_universality:
      forall (c: Cone D)(i: J),
        obj i \o univ c == c i;
    
    limit_uniqueness:
      forall (c: Cone D)(u: C c obj),
        (forall i: J, obj i \o u == c i) ->
        u == univ c
  }.

Structure Limit (J C: Category)(D: J --> C) :=
  {
    limit_obj:> Cone D;
    limit_univ: forall c: Cone D, C c limit_obj;

    limit_prf:> IsLimit limit_univ
  }.
Existing Instance limit_prf.

Notation "[ 'Limit' obj 'by' univ 'of' D ]" := (@Build_Limit _ _ D obj univ _).
Notation "[ 'Limit' 'by' univ 'of' D ]" := [Limit _ by univ of D].
Notation "[ 'Limit' obj 'by' univ ]" := [Limit obj by univ of _].
Notation "[ 'Limit' 'by' univ ]" := [Limit by univ of _].

(** Isomorphic **)
Lemma limit_isomorphic:
  forall (J C: Category)(D: J --> C)
         (lim lim': Limit D),
    lim === lim' in C.
Proof.
  intros; simpl; unfold isomorphic.
  exists (limit_univ lim' lim), (limit_univ lim lim'); split.
  - rewrite (limit_uniqueness (u:=Id lim)).
    + apply limit_uniqueness; intros i.
      now rewrite <- cat_comp_assoc, !limit_universality.
    + now intros i; rewrite cat_comp_id_dom.
  - rewrite (limit_uniqueness (u:=Id lim')).
    + apply limit_uniqueness; intros i.
      now rewrite <- cat_comp_assoc, !limit_universality.
    + now intros i; rewrite cat_comp_id_dom.
Qed.

(** Terminality of Limit **)
Class IsConeMap
      (J C: Category)
      (D: J --> C)
      (c d: Cone D)
      (map: C c d) :=
  {
    cone_map_commute:
      forall i: J,
        d i \o map == c i
  }.

Structure ConeMap
          (J C: Category)
          (D: J --> C)
          (c d: Cone D) :=
  {
    cone_map_map:> C c d;
    cone_map_prf:> IsConeMap cone_map_map
  }.
Existing Instance cone_map_prf.
Notation "[ 'ConeMap' 'by' f ]" := (@Build_ConeMap _ _ _ _ _ f _).

Program Definition ConeMap_compose (J C: Category)(D: J --> C)(c d e: Cone D)(f: ConeMap c d)(g: ConeMap d e)
  : ConeMap c e :=
  [ConeMap by g \o f].
Next Obligation.
  now rewrite <- cat_comp_assoc, !cone_map_commute.
Qed.

Program Definition ConeMap_id (J C: Category)(D: J --> C)(c: Cone D): ConeMap c c :=
  [ConeMap by Id c].
Next Obligation.
  now rewrite cat_comp_id_dom.
Qed.

Program Definition ConeMap_setoid (J C: Category)(D: J --> C)(c d: Cone D): Setoid :=
  [Setoid by `(f == g) on ConeMap c d].
Next Obligation.
  now intros f g h Heqfg Heqgh; rewrite Heqfg, Heqgh.
Qed.

Program Definition Cones (J C: Category)(D: J --> C): Category :=
  [Category by @ConeMap_setoid J C D
   with @ConeMap_compose J C D,
        @ConeMap_id J C D].
Next Obligation.
  - rename X into c, Y into d, Z into e.
    intros f f' Heqf g g' Heqg; simpl in *.
    now rewrite Heqf, Heqg.
  - now rewrite cat_comp_assoc.
  - now rewrite cat_comp_id_dom.
  - now rewrite cat_comp_id_cod.
Qed.

Program Definition limit_by_terminal_of_cones
        (J C: Category)(D: J --> C)(t: Terminal (Cones D)): Limit D :=
  [Limit by terminal_univ t].
Next Obligation.
  - now apply (cone_map_commute (IsConeMap:=terminal_univ t c)).
  - now apply (terminal_uniqueness (IsTerminal:=t) (X:=c) (Build_ConeMap (Build_IsConeMap H))).
Qed.

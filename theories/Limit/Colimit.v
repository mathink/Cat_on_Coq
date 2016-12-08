(** * Colimit **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main COC.Cons.Initial.

Class IsCocone
      (J C: Category)(D: J --> C)
      (apex: C)
      (gen: forall i: J, C (D i) apex) :=
  {
    cocone_commute:
      forall (i j: J)(u: J i j),
        gen j \o fmap D u == gen i
  }.

Structure Cocone (J C: Category)(D: J --> C): Type :=
  {
    cocone_apex:> C;
    cocone_gen:> forall i: J, C (D i) cocone_apex;

    cocone_prf:> IsCocone cocone_gen
  }.
Existing Instance cocone_prf.

Notation "[ 'Cocone' 'of' D 'by' gen 'to' apex ]" := (@Build_Cocone _ _ D apex gen _).
Notation "[ 'Cocone' 'by' gen 'to' apex ]" := [Cocone of _ by gen to apex].
Notation "[ 'Cocone' 'by' gen ]" := [Cocone by gen to _].
Notation "[ 'Cocone' 'by' i :-> f 'to' apex ]" := [Cocone by (fun i => f) to apex].
Notation "[ 'Cocone' 'by' i :-> f ]" := [Cocone by i :-> f to _].


Class IsColimit (J C: Category)(D: J --> C)
      (obj: Cocone D)
      (univ: forall c: Cocone D, C obj c) :=
  {
    colimit_universality:
      forall (c: Cocone D)(i: J),
        univ c \o obj i == c i;
    
    colimit_uniqueness:
      forall (c: Cocone D)(u: C obj c),
        (forall i: J, u \o obj i == c i) ->
        u == univ c
  }.

Structure Colimit (J C: Category)(D: J --> C) :=
  {
    colimit_obj:> Cocone D;
    colimit_univ: forall c: Cocone D, C colimit_obj c;

    colimit_prf:> IsColimit colimit_univ
  }.
Existing Instance colimit_prf.

Notation "[ 'Colimit' obj 'by' univ 'of' D ]" := (@Build_Colimit _ _ D obj univ _).
Notation "[ 'Colimit' 'by' univ 'of' D ]" := [Colimit _ by univ of D].
Notation "[ 'Colimit' obj 'by' univ ]" := [Colimit obj by univ of _].
Notation "[ 'Colimit' 'by' univ ]" := [Colimit by univ of _].

(** Isomorphic **)
Lemma colimit_isomorphic:
  forall (J C: Category)(D: J --> C)
         (colim colim': Colimit D),
    colim === colim' in C.
Proof.
  intros; simpl; unfold isomorphic.
  exists (colimit_univ colim colim'), (colimit_univ colim' colim); split.
  - rewrite (colimit_uniqueness (u:=Id colim)).
    + apply colimit_uniqueness; intros i.
      now rewrite cat_comp_assoc, !colimit_universality.
    + now intros i; rewrite cat_comp_id_cod.
  - rewrite (colimit_uniqueness (u:=Id colim')).
    + apply colimit_uniqueness; intros i.
      now rewrite cat_comp_assoc, !colimit_universality.
    + now intros i; rewrite cat_comp_id_cod.
Qed.

(** Initiality of Colimit **)
Class IsCoconeMap
      (J C: Category)(D: J --> C)
      (c d: Cocone D)
      (map: C c d) :=
  {
    cocone_map_commute:
      forall i: J,
        map \o c i == d i
  }.

Structure CoconeMap (J C: Category)(D: J --> C)(c d: Cocone D) :=
  {
    cocone_map_map:> C c d;
    cocone_map_prf:> IsCoconeMap cocone_map_map
  }.
Existing Instance cocone_map_prf.

Notation "[ 'CoconeMap' 'by' f ]" :=
  (@Build_CoconeMap _ _ _ _ _ f _).

Program Definition CoconeMap_compose (J C: Category)(D: J --> C)(c d e: Cocone D)(f: CoconeMap c d)(g: CoconeMap d e)
  : CoconeMap c e :=
  [CoconeMap by g \o f].
Next Obligation.
  now rewrite cat_comp_assoc, !cocone_map_commute.
Qed.

Program Definition CoconeMap_id (J C: Category)(D: J --> C)(c: Cocone D): CoconeMap c c :=
  [CoconeMap by Id c].
Next Obligation.
  now rewrite cat_comp_id_cod.
Qed.

Program Definition CoconeMap_setoid (J C: Category)(D: J --> C)(c d: Cocone D): Setoid :=
  [Setoid by `(f == g) on CoconeMap c d].
Next Obligation.
  now intros f g h Heqfg Heqgh; rewrite Heqfg, Heqgh.
Qed.

Program Definition Cocones (J C: Category)(D: J --> C): Category :=
  [Category by @CoconeMap_setoid J C D
   with (@CoconeMap_compose J C D),
        (@CoconeMap_id J C D)].
Next Obligation.
  rename X into c, Y into d, Z into e.
  intros f f' Heqf g g' Heqg; simpl in *.
  now rewrite Heqf, Heqg.

  now rewrite cat_comp_assoc.

  now rewrite cat_comp_id_dom.

  now rewrite cat_comp_id_cod.
Qed.

Program Definition colimit_by_initial_of_cocones (J C: Category)(D: J --> C)(i: Initial (Cocones D)): Colimit D :=
  [Colimit (initial_obj i) by initial_univ i].
Next Obligation.
  - now apply cocone_map_commute.
  - apply Build_IsCoconeMap in H.
    now apply (initial_uniqueness (IsInitial:=i)(X:=c)[CoconeMap by u]).
Qed.

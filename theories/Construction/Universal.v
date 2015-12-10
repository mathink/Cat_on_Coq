Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.

Module UniversalArrow.
  Module To.
    (* 
          Sr    r
       u/  |    |
      c   Sf'   f'
       f\  V    V  
          Sd    d
     *)
    Class spec {C D: Category}(c: C)(S: Functor D C)(r: D)(u: C c (S r)): Prop :=
      proof {
          universality:
            forall (d: D)(f: C c (S d)),
              exists!_ (f': D r d), fmap S f' \o u == f
        }.

    Structure type {C D: Category}(c: C)(S: Functor D C) :=
      make {
          obj: D;
          arrow: C c (S obj);
          prf: spec arrow
        }.

    Notation build arrow := (@make _ _ _ _ _ arrow (@proof _ _ _ _ _ _ _)).

    Module Ex.
      Notation "'[UA' c ':=>' F ]" := (type c F) (no associativity).
    End Ex.
  End To.

  Module From.
    (* 
      d    Sd
      |     | \f
      f'   Sf'  c
      V     V /v
      r    Sr
     *)

    Class spec {C D: Category}(S: Functor D C)(c: C)(r: D)(v: C (S r) c): Prop :=
      proof {
          universality:
            forall (d: D)(f: C (S d) c),
              exists!_ f': D d r, v \o fmap S f' == f
        }.

    Structure type {C D: Category}(S: Functor D C)(c: C) :=
      make {
          obj: D;
          arrow: C (S obj) c;

          prf: spec arrow
        }.

    Notation build arrow := (@make _ _ _ _ _ arrow (@proof _ _ _ _ _ _ _)).

    Module Ex.
      Notation "'[UA' c '<=:' F ]" := (type F c) (no associativity).
    End Ex.
  End From.

End UniversalArrow.
Export UniversalArrow.To.Ex.
Export UniversalArrow.From.Ex.

Module UATo := UniversalArrow.To.
Module UAFrom := UniversalArrow.From.

Require Import COC.Structure.

Program Definition CommaInitUA (C D: Category)(S: Functor D C)(c: C)(i: Initial (CommaTo c S)): [UA c :=> S] :=
  let r := (Comma.cod (@Initial.obj _ i)) in
  let u := (Comma.morph (@Initial.obj _ i)) in
  UATo.build u.
Next Obligation.
  intros; simpl in *.
  set (df := (Comma.triple (T:=ConstFunctor c)(dom:=c) f)).
  set (m:=(@Initial.univ _ i df)).
  generalize (@Comma.comm _ _ _ _ _ _ _ _ _ m).
  set (f':= Comma.cmorph m).
  intros H; simpl in *.
  exists f'; split.
  - eapply transitivity; [| apply Category.comp_id_dom].
    apply symmetry, H.
  - intros g' Heq.
    assert (H': f \o Id c == fmap S g' \o Comma.morph (Initial.obj i)).
    {
      eapply transitivity; [apply Category.comp_id_dom |].
      apply symmetry, Heq.
    }
    set (spec := @Comma.proof _ _ _ (ConstFunctor c) S (Initial.obj i) df (Comma.dmorph m) g' H').
    set (dg' := Comma.make spec); simpl in *.
    apply  (@Initial.ump _ _ _ i _ dg'); simpl.
Qed.

Program Definition CommaTermUA (C D: Category)(c: C)(S: Functor D C)(t: Terminal (CommaFrom S c)): [UA c <=: S] :=
  let r := (Comma.cod (Terminal.object t)) in
  let u := (Comma.morph (Terminal.object t)) in
  UAFrom.build u.
Next Obligation.
  intros; simpl in *.
  set (df := (Comma.triple (S:=ConstFunctor c)(cod:=c) f)).
  set (m:=(@Terminal.morphism _ t df)).
  generalize (@Comma.comm _ _ _ _ _ _ _ _ _ m).
  set (f':=(Comma.dmorph m)) in *.
  intros H; simpl in *.
  exists f'; split.
  - eapply transitivity; [| apply Category.comp_id_cod].
    apply H.
  - intros g' Heq.
    assert (H': Comma.morph (Terminal.object t) \o fmap S g' == Id c \o f).
    {
      eapply transitivity; [apply Heq | apply symmetry, Category.comp_id_cod ].
    }
    set (spec := Comma.proof (T:=S)(S:=ConstFunctor c)(f:=df)(k:=g')(h:=Comma.cmorph m) H'). 
    set (dg' := Comma.make spec); simpl in *.
    apply  (@Terminal.terminality _ _ _ t _ dg'); simpl.
Qed.

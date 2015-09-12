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
              exists_ f': D r d, fmap S f' \o u == f
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
              exists_ f': D d r, v \o fmap S f' == f
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

Require Import COC.Structure.

Program Definition CommaInitUA 
        (C D: Category)(S: Functor D C)(c: C)
        (i: Initial (Comma.category (ConstFunctor c) S)): [UA c :=> S] :=
  UniversalArrow.To.build (Comma.morph (@Initial.object _ i)).
Next Obligation.
  intros; simpl.
  set (df := (Comma.triple (T:=ConstFunctor c)(dom:=c) f)).
  set (m:=(@Initial.morphism _ i df)).
  generalize (@Comma.comm _ _ _ _ _ _ _ _ _ m); intro H.
  simpl in *.
  set (f':=(Comma.cmorph m)) in *.
  exists f'; simpl in *.
  eapply transitivity; [| apply Category.comp_id_dom].
  apply symmetry, H.
Qed.

Program Definition CommaTermUA
        (C D: Category)(c: C)(S: Functor D C)
        (t: Terminal (Comma.category S (ConstFunctor c))): [UA c <=: S] :=
  UniversalArrow.From.build (Comma.morph (@Terminal.object _ t)).
Next Obligation.
  intros; simpl.
  set (df := (Comma.triple (S:=ConstFunctor c)(cod:=c) f)).
  set (m:=(@Terminal.morphism _ t df)).
  generalize (@Comma.comm _ _ _ _ _ _ _ _ _ m); intro H.
  simpl in *.
  set (f':=(Comma.dmorph m)) in *.
  exists f'; simpl in *.
  eapply transitivity; [| apply Category.comp_id_cod].
  apply H.
Qed.

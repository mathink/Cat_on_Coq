Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.

Generalizable All Variables.

Module Cocone.
  (** ** 底 J からの錐 *)
  (** J :: index category, D :: diagram in C *)
  Class spec (J C: Category)(D: Functor J C)(apex: C)(gen: forall i: J, C (D i) apex) :=
    proof {
        commute:
          forall (i j: J)(u: J i j),
            gen i == gen j \o fmap D u
      }.

  Structure type (J C: Category)(D: Functor J C) :=
    make {
        apex: C;
        gen: forall i: J, C (D i) apex;

        prf: spec (@gen)
      }.

  Module Ex.
    Notation isCocone := spec.
    Notation Cocone := type.
    
    Coercion apex: Cocone >-> Category.obj.
    Coercion prf: Cocone >-> isCocone.

    Arguments gen {J C D}(c i): rename, clear implicits.
  End Ex.
End Cocone.
Export Cocone.Ex.

Module CoconeMap.
  Class spec `(D: Functor J C)(c d: Cocone D)(f: C c d) :=
    commute:> forall i,
        Cocone.gen d i == f \o Cocone.gen c i.
  Arguments commute {J C D c d f}{spec}(i): clear implicits.

  Structure type `(D: Functor J C)(c d: Cocone D) :=
    make {
        map: C c d;

        prf: spec map
      }.

  Notation build map := (@make _ _ _ _ _ map _).

  Module Ex.
    Notation isCoconeMap := spec.
    Notation CoconeMap := type.

    Coercion map: CoconeMap >-> Setoid.carrier.
    Coercion prf: CoconeMap >-> isCoconeMap.

    Existing Instance prf.
  End Ex.

  Import Ex.

  Definition equal `(D: Functor J C)(c d: Cocone D)(f g: CoconeMap c d) := f == g.
  Arguments equal J C D c d f g /.
    
  Instance equiv`(D: Functor J C)(c d: Cocone D): Equivalence (@equal _ _ D c d).
  Proof.
    split.
    - now intros x; simpl.
    - now intros x y Heq; simpl;symmetry.
    - intros x y z Hxy Hyz; simpl in *.
      now transitivity y.
  Qed.
  Definition setoid `(D: Functor J C)(c d: Cocone D):= Setoid.make (equiv D c d).

  Program Definition compose `(D: Functor J C)(c d e: Cocone D)(f: CoconeMap c d)(g: CoconeMap d e): CoconeMap c e :=
    build (g \o f).
  Next Obligation.
    intros i.
    now rewrite catCa, <- !commute.
  Qed.
  Arguments compose J C D c d e f g/.

  Program Definition ident `(D: Functor J C)(c: Cocone D): CoconeMap c c := build (Id c).
  Next Obligation.
    now intros i; rewrite catCf1.
  Qed.
  Arguments ident J C D c /.

End CoconeMap.
Export CoconeMap.Ex.

Program Definition Cocones (J C: Category)(D: Functor J C) :=
  Category.build (@CoconeMap.setoid _ _ D)
                 (@CoconeMap.compose _ _ D) 
                 (@CoconeMap.ident _ _ D).
Next Obligation.
  intros f f' Hf g g' Hg; simpl in *.
  now rewrite Hf, Hg.
Qed.
Next Obligation.
  now rewrite catCa.
Qed.
Next Obligation.
  now rewrite catC1f.
Qed.
Next Obligation.
  now rewrite catCf1.
Qed.

Module Colimit.

  Class spec (J C: Category)(D: Functor J C)(colimD: Cocone D)(u: forall c: Cocone D, CoconeMap colimD c) :=
    proof {
        ump: forall (c: Cocone D)(f: CoconeMap colimD c), u c == f
      }.

  Structure type `(D: Functor J C) :=
    make {
        obj: Cocone D;
        univ: forall c: Cocone D, CoconeMap obj c;

        prf: spec (@univ)
      }.

  Module Ex.
    Notation isColimit := spec.
    Notation Colimit := type.

    Coercion obj: Colimit >-> Cocone.
    Coercion prf: Colimit >-> isColimit.

    Existing Instance prf.

    Notation "'colim<-' D " :=  (Colimit D) (at level 50, left associativity, format "colim<- D").
  End Ex.

End Colimit.
Export Colimit.Ex.


(* universe *)

Program Instance Cocones'_initial_is_colimit `(D: Functor J C)(t: Initial (Cocones D))
  : isColimit (Initial.univ t).
Next Obligation.
  symmetry.
  apply (Initial.ump t f).
Qed.


Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.

Generalizable All Variables.

Module Cone.
  (** ** 底 J への錐 *)
  (** J :: index category, D :: diagram in C *)
  Class spec (J C: Category)(D: Functor J C)(apex: C)(gen: forall i: J, C apex (D i)) :=
    proof {
        commute:
          forall (i j: J)(u: J i j),
            fmap D u \o gen i == gen j
      }.

  Structure type (J C: Category)(D: Functor J C) :=
    make {
        apex: C;
        gen: forall i: J, C apex (D i);

        prf: spec (@gen)
      }.

  Module Ex.
    Notation isCone := spec.
    Notation Cone := type.
    
    Coercion apex: Cone >-> Category.obj.
    Coercion prf: Cone >-> isCone.

    Arguments gen {J C D}(c i): rename, clear implicits.
  End Ex.
End Cone.
Export Cone.Ex.

Module ConeMap.
  Class spec `(D: Functor J C)(c d: Cone D)(f: C c d) :=
    commute:> forall i,
        Cone.gen d i \o f == Cone.gen c i.
  Arguments commute {J C D c d f}(spec i): clear implicits.

  Structure type `(D: Functor J C)(c d: Cone D) :=
    make {
        map: C c d;

        prf: spec map
      }.

  Notation build map := (@make _ _ _ _ _ map _).

  Module Ex.
    Notation isConeMap := spec.
    Notation ConeMap := type.

    Coercion map: ConeMap >-> Setoid.carrier.
    Coercion prf: ConeMap >-> isConeMap.

    Existing Instance prf.
  End Ex.

  Import Ex.

  Definition equal `(D: Functor J C)(c d: Cone D)(f g: ConeMap c d) := f == g.
  Arguments equal J C D c d f g /.
    
  Instance equiv`(D: Functor J C)(c d: Cone D): Equivalence (@equal _ _ D c d).
  Proof.
    split.
    - intros x; simpl; apply reflexivity.
    - intros x y Heq; simpl; apply symmetry.
      now apply Heq.
    - intros x y z Hxy Hyz; simpl in *.
      eapply transitivity.
      now apply Hxy.
      now apply Hyz.
  Qed.
  Definition setoid `(D: Functor J C)(c d: Cone D):= Setoid.make (equiv D c d).

  Program Definition compose `(D: Functor J C)(c d e: Cone D)(f: ConeMap c d)(g: ConeMap d e): ConeMap c e :=
    build (g \o f).
  Next Obligation.
    intros; intro.
    eapply transitivity.
    now apply symmetry, catCa.
    eapply transitivity.
    apply catCsc.
    now apply (commute g).
    now apply (commute f).
  Qed.
  Arguments compose J C D c d e f g/.

  Program Definition ident `(D: Functor J C)(c: Cone D): ConeMap c c := build (Id c).
  Next Obligation.
    intros; intro.
    now apply catC1f.
  Qed.
  Arguments ident J C D c /.

End ConeMap.
Export ConeMap.Ex.

Program Definition Cones (J C: Category)(D: Functor J C) :=
  Category.build (@ConeMap.setoid _ _ D)
                 (@ConeMap.compose _ _ D) 
                 (@ConeMap.ident _ _ D).
Next Obligation.
  intros; simpl.
  apply catCs; assumption.
Qed.
Next Obligation.
  intros; simpl; apply catCa.
Qed.
Next Obligation.
  intros; simpl; apply catC1f.
Qed.
Next Obligation.
  intros; simpl; apply catCf1.
Qed.

Module Limit.

  Class spec (J C: Category)(D: Functor J C)(limD: Cone D)(u: forall c: Cone D, ConeMap c limD) :=
    proof {
        ump: forall (c: Cone D)(f: ConeMap c limD), u c == f
      }.

  Structure type `(D: Functor J C) :=
    make {
        obj: Cone D;
        univ: forall c: Cone D, ConeMap c obj;

        prf: spec (@univ)
      }.

  Module Ex.
    Notation isLimit := spec.
    Notation Limit := type.

    Coercion obj: Limit >-> Cone.
    Coercion prf: Limit >-> isLimit.

    Existing Instance prf.

    Notation "'lim<-' D " :=  (Limit D) (at level 50, left associativity, format "lim<- D").
  End Ex.

End Limit.
Export Limit.Ex.


(* universe *)

Program Instance Cones'_terminal_is_limit `(D: Functor J C)(t: Terminal (Cones D))
  : isLimit (Terminal.univ t).
Next Obligation.
  intros; simpl.
  apply symmetry.
  apply (@Terminal.ump (Cones D) _ _ t c f).
Qed.


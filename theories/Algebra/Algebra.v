Set Implicit Arguments.
Unset Strict Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid.
Require Import COC.Category.Category COC.Category.Functor COC.Category.Object.

(** * F-代数
函手 #$F: C \rightarrow C$# について組 #$(X,x:F(X)\rightarrow X)$# を F-代数と呼ぶ。
 **)
Module Algebra.
  Structure type `(F: Functor C C) :=
    make {
        obj: C;
        arr: C (F obj) obj
      }.
  
  Module Ex.
    Notation Algebra := type.

    Coercion obj: Algebra >-> Category.obj.
    Coercion arr: Algebra >-> Setoid.carrier.
  End Ex.
End Algebra.  
Export Algebra.Ex.

(** ** F-代数間の射 **)
Module AlgebraMap.
  Class spec `(F: Functor C C)(x y: Algebra F)(h: C x y) :=
    proof {
        commute:
          h \o x == y \o fmap F h
      }.

  Structure type `(F: Functor C C)(x y: Algebra F) :=
    make {
        arr: C x y;

        prf: spec arr
      }.

  Notation build arr := (@make _ _ _ _ arr (@proof _ _ _ _ _ _)).

  Module Ex.
    Notation isAlgebraMap := spec.
    Notation AlgebraMap := type.

    Coercion arr: AlgebraMap >-> Setoid.carrier.
    Coercion prf: AlgebraMap >-> isAlgebraMap.

    Existing Instance prf.
  End Ex.

  Import Ex.

  Section Alg.
    Context `(F: Functor C C).

    Notation AMap := AlgebraMap.
    
    Program Definition setoid (x y: Algebra F):=
      Setoid.build (fun (f g: AMap x y) => f == g).
    Next Obligation.
      now intros f.
    Qed.
    Next Obligation.
      now intros f g.
    Qed.
    Next Obligation.
      now intros f g h; apply transitivity.
    Qed.

    Program Definition compose (x y z: Algebra F)(f: AMap x y)(g: AMap y z): AMap x z :=
      build (g \o f).
    Next Obligation.
      now rewrite catCa, commute, <- catCa, commute, catCa, Functor.fmap_comp.
    Qed.

    Program Definition id (x: Algebra F): AMap x x :=
      build (Id x).
    Next Obligation.
      now rewrite Functor.fmap_id, catCf1, catC1f.
    Qed.
  End Alg.
End AlgebraMap.
Export AlgebraMap.Ex.

(** ** F-代数の圏 **)
Program Definition Alg `(F: Functor C C): Category :=
  Category.build (@AlgebraMap.setoid _ F)
                 (@AlgebraMap.compose _ F)
                 (@AlgebraMap.id _ F).
Next Obligation.
  intros f f' Heqf g g' Heqg; simpl.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  now apply catCa.
Qed.
Next Obligation.
  now apply catC1f.
Qed.
Next Obligation.
  now apply catCf1.
Qed.

Definition InitialAlgebra `(F: Functor C C) := Initial (Alg F).

(** ** catamorphism **)
Definition catamorphism `(F: Functor C C)(init: InitialAlgebra F)(x: Algebra F):
  C (Initial.obj init) x :=
  Initial.univ init x.


(** * F-余代数
函手 #$F: C \rightarrow C$# について組 #$(X,x:X\rightarrow F(X))$# を F-代数と呼ぶ。
 **)
Module Coalgebra.
  Structure type `(F: Functor C C) :=
    make {
        obj: C;
        arr: C obj (F obj)
      }.
  
  Module Ex.
    Notation Coalgebra := type.

    Coercion obj: Coalgebra >-> Category.obj.
    Coercion arr: Coalgebra >-> Setoid.carrier.
  End Ex.
End Coalgebra.  
Export Coalgebra.Ex.

(** ** F-余代数間の射 **)
Module CoalgebraMap.
  Class spec `(F: Functor C C)(x y: Coalgebra F)(h: C x y) :=
    proof {
        commute:
          fmap F h \o x == y \o h
      }.

  Structure type `(F: Functor C C)(x y: Coalgebra F) :=
    make {
        arr: C x y;

        prf: spec arr
      }.

  Notation build arr := (@make _ _ _ _ arr (@proof _ _ _ _ _ _)).

  Module Ex.
    Notation isCoalgebraMap := spec.
    Notation CoalgebraMap := type.

    Coercion arr: CoalgebraMap >-> Setoid.carrier.
    Coercion prf: CoalgebraMap >-> isCoalgebraMap.

    Existing Instance prf.
  End Ex.

  Import Ex.

  Section Coalg.
    Context `(F: Functor C C).

    Notation CMap := CoalgebraMap.
    
    Program Definition setoid (x y: Coalgebra F):=
      Setoid.build (fun (f g: CMap x y) => f == g).
    Next Obligation.
      now intros f.
    Qed.
    Next Obligation.
      now intros f g.
    Qed.
    Next Obligation.
      now intros f g h; apply transitivity.
    Qed.

    Program Definition compose (x y z: Coalgebra F)(f: CMap x y)(g: CMap y z): CMap x z :=
      build (g \o f).
    Next Obligation.
      now rewrite Functor.fmap_comp, catCa, commute, <- !catCa, commute.
    Qed.

    Program Definition id (x: Coalgebra F): CMap x x :=
      build (Id x).
    Next Obligation.
      now rewrite Functor.fmap_id, catCf1, catC1f.
    Qed.
  End Coalg.
End CoalgebraMap.
Export CoalgebraMap.Ex.

(** ** F-余代数の圏 **)
Program Definition Coalg `(F: Functor C C): Category :=
  Category.build (@CoalgebraMap.setoid _ F)
                 (@CoalgebraMap.compose _ F)
                 (@CoalgebraMap.id _ F).
Next Obligation.
  intros f f' Heqf g g' Heqg; simpl.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  now apply catCa.
Qed.
Next Obligation.
  now apply catC1f.
Qed.
Next Obligation.
  now apply catCf1.
Qed.

Definition TerminalCoalgebra `(F: Functor C C) := Terminal (Coalg F).

(** ** anamorphism **)
Definition anamorphism `(F: Functor C C)(term: TerminalCoalgebra F)(x: Coalgebra F):
  C x (Terminal.obj term) :=
  Terminal.univ term x.

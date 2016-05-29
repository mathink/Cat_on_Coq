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

(* あとで分離 *)
(** * F-始代数の例 **)
Set Contextual Implicit.

Require Import List.
Import List.ListNotations.

Program Definition function_setoid (X Y: Type) :=
  Setoid.build (fun (f g: X -> Y) => forall x, f x = g x).
Next Obligation.
  intros f g h Heqfg Heqgh x.
  now rewrite Heqfg; apply Heqgh.
Qed.

Program Definition Types: Category :=
  Category.build (function_setoid)
                 (fun X Y Z f g x => g (f x))
                 (fun X x => x).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl.
  now rewrite Heqf, Heqg.
Qed.

Inductive listF (A X: Types) :=
| listF_nil
| listF_cons: A -> X -> listF A X.

Definition listF_map (A X Y: Types)(f: X -> Y)(l: listF A X): listF A Y :=
  match l with
  | listF_nil => listF_nil
  | listF_cons a x => listF_cons a (f x)
  end.

Program Definition listF_functor (A: Type): Functor Types Types:=
  Functor.build (listF A)
                (@listF_map A).
Next Obligation.
  intros f g Heq [|a x]; simpl; auto.
  now rewrite Heq.
Qed.
Next Obligation.
  destruct x as [| a x]; simpl; auto.
Qed.
Next Obligation.
  destruct x as [| a x]; simpl; auto.
Qed.

Program Definition listF_make_algebra (A B: Type)(f: A -> B -> B)(e: B): Algebra (listF_functor A) :=
  Algebra.make (@listF_rect _ _ _ e f).

Fixpoint foldr_algebra (A: Type)(B: Algebra (listF_functor A))(l: list A){struct l} :=
  match l with
  | [] => Algebra.arr B listF_nil
  | x::xs => Algebra.arr B (listF_cons x (foldr_algebra B xs))
  end.

Program Definition foldr_algebra_map (A: Type)(B: Algebra (listF_functor A))
  : AlgebraMap (listF_make_algebra (@cons A) nil) B :=
  AlgebraMap.build (foldr_algebra B).
Next Obligation.
  now destruct x; simpl.
Qed.

Program Instance list_is_initial (A: Type)
  : @isInitial (Alg (listF_functor A)) (listF_make_algebra (@cons A) nil)
               (@foldr_algebra_map A).
Next Obligation.
  induction x as [| x xs]; simpl.
  - now apply (AlgebraMap.commute (spec:=f) listF_nil).
  - rewrite <- IHxs.
    now apply (AlgebraMap.commute (spec:=f) (listF_cons x xs)).
Qed.

Program Definition list_initial (A: Type): Initial (Alg (listF_functor A)) :=
  Initial.make (list_is_initial A).

Fixpoint foldr (X Y: Type)(f: X -> Y -> Y)(e: Y)(l: list X): Y := 
  match l with
  | [] => e
  | x::xs => f x (foldr f e xs)
  end.

Lemma foldr_is_catamorphism:
  forall (A B: Type)(f: A -> B -> B)(e: B)(l: list A),
    foldr f e l = catamorphism (@list_initial A) (listF_make_algebra f e) l.
Proof.
  unfold listF_catamorphism, catamorphism; simpl.
  induction l as [| x xs]; simpl; auto.
  now rewrite IHxs.
Qed.
Set Implicit Arguments.
Unset Strict Implicit.

Set Contextual Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid COC.Category COC.Algebra.

Require Import List.
Import List.ListNotations.


(** * F-始代数の例 **)

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
  unfold catamorphism; simpl.
  induction l as [| x xs]; simpl; auto.
  now rewrite IHxs.
Qed.

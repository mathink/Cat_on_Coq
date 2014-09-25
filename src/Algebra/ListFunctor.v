(* -*- mode: coq -*- *)
(* Time-stamp: <2014/9/25 21:47:30> *)
(*
  ListFunctor.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Require Import Category Functor Algebra.

(** Note: 型函手による議論に一般化したいなぁと思っています。  *)
Inductive ListF (A X: Type): Type :=
| Nil: ListF A X
| Cons (a: A)(x: X): ListF A X.
Arguments Nil {A X}.
Arguments Cons {A X}(a x).

Definition equal_fun {A B: Type}(f g: A -> B) := forall a, f a = g a.
Instance equal_fun_Equiv (A B: Type): Equivalence (@equal_fun A B).
Proof.
  split.
  - now intros f x.
  - now intros f g Heq x; rewrite Heq.
  - now intros f g h Heqfg Heqgh x; rewrite Heqfg.
Qed.
Canonical Structure Setoid_fun (A B: Type) := Build_Setoid (equal_fun_Equiv A B).

Instance Compose_fun: Compose Setoid_fun :=
  { compose X Y Z f g := fun x => g (f x) }.
Proof.
  now simpl; hnf; intros X Y Z f f' Heqf g g' Heqg x; rewrite Heqf,Heqg.
Defined.

Instance Identity_fun: Identity Setoid_fun :=
  { identity X := fun x => x }.

Instance Sets_IsCategory: isCategory Compose_fun Identity_fun.
Proof.
  split; intros; simpl; intro; auto.
Qed.
Canonical Structure Sets: Category := Build_Category Sets_IsCategory.

Program Definition fmap_ListF (A: Type): Fmap Sets Sets (ListF A) :=
  fun X Y => [ f :-> fun l => match l with
                                | Nil => Nil
                                | Cons a x => Cons a (f x)
                              end ].
Next Obligation.
  intros f f' Heqf [| a l]; simpl; auto.
  now rewrite Heqf.
Qed.

Instance ListF_IsFunctor (A: Type): isFunctor (fmap_ListF A).
Proof.
  split; intros; intros [| a l]; simpl; auto. 
Qed.

Definition ListFunctor (A: Type): Functor Sets Sets := 
  Build_Functor (ListF_IsFunctor A).


(** list A is (ListFunctor A)-Algebra  *)
Definition list_alg_arr (A: Type): Sets (ListFunctor A (list A)) (list A) :=
  fun l => match l with Nil => nil | Cons a l => cons a l end.
Definition listAlg (A: Type) := Build_Alg (list_alg_arr (A:=A)).

(*
   list A -> X

   listF A (list A) -> list A

   listF A X -> X
  *)
Fixpoint in_listAlg (A: Type)(x: Alg (ListFunctor A))(l: list A): alg_obj x :=
    match l with
      | nil => alg_arr x Nil
      | cons a l => alg_arr x (Cons a (in_listAlg x l))
    end.

Instance in_listAlg_IsAlgMap (A: Type)(x: Alg (ListFunctor A))
: isAlgMap (F:=ListFunctor A) (x:=listAlg A) (y:=x) (in_listAlg x).
Proof.
  intros [|]; simpl in *; try reflexivity.
Qed.

Definition in_listAlgMap (A: Type)(x: Alg (ListFunctor A)): AlgMap (listAlg A) x :=
  Build_AlgMap (in_listAlg_IsAlgMap x).

Instance list_IsInitial (A: Type): isInitial (in_listAlgMap (A:=A)).
Proof.
  intros x f l; simpl in *.
  induction l as [| h l IHl].
  - generalize (alg_commute (isAlgMap:=prf_AlgMap f) Nil); simpl; auto.
  - generalize (alg_commute (isAlgMap:=prf_AlgMap f) (Cons h l)); simpl; auto.
    intro H; rewrite <- H, <- IHl; reflexivity.
Qed.

Definition Initial_list (A: Type): Initial (ALG (ListFunctor A)) :=
  Build_Initial (list_IsInitial (A:=A)).

Lemma list_initiality (A: Type)(In: Initial (ALG (ListFunctor A))):
  iso (listAlg A) In.
Proof.
  rewrite (Initial_unique In (Initial_list A)).
  reflexivity.
Qed.


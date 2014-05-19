Require Import 
Ssreflect.ssreflect
Ssreflect.eqtype
Ssreflect.ssrbool
COC.Setoid COC.Category COC.Functor COC.Algebra.

Set Implicit Arguments.
(* Unset Strict Implicit. *)


(* F-代数とF-代数からなる圏 ALG F を定義する *)

(* いよいよリスト *)
Section ListFunctor.
  (* 積、余積、終対象があればリスト函手は定義できるので、一般的な設定で定義してみる *)
  Variables (C: Category)
            (Hprod: hasProduct C)(Hcoprod: hasCoProduct C)
            (T: Terminal C).
  (* functoriality *)
  Definition listF_obj (A X: C): C :=
    coprod T (prod A X).

  Program Definition listF_arr (A X Y: C)
  : Map (X --> Y) (listF_obj A X --> listF_obj A Y) :=
    {| map_function f := coprod_arr (id_ T) (prod_arr id f) |}.
  Next Obligation.
    rename x into f; rename x' into f'.
    rewrite /coprod_arr /prod_arr.
    by apply coproduct_arr_subst_Y, compose_subst_fst, product_arr_subst_Y, compose_subst_snd.
  Defined.
  
  Program Definition listF (A: C): Functor C C :=
    {| fmap X Y := listF_arr A X Y |}.
  Next Obligation.
    rewrite /coprod_arr /prod_arr.
    eapply transitivity;
      [apply coproduct_arr_subst_Y, compose_subst_fst
      | apply coproduct_universality].
    apply product_arr_subst; apply id_cod.
    eapply transitivity;
      [ apply id_cod | apply symmetry, id_dom ].
    eapply transitivity;
      [ apply id_cod | apply symmetry ].
    eapply transitivity;
      [ apply compose_subst_fst, product_universality | apply id_dom];
      apply id_dom.
  Defined.
  Next Obligation.
    eapply transitivity;
    [ apply coprod_arr_compose |].
    apply coproduct_arr_subst.
    eapply transitivity; [ apply symmetry, compose_assoc | apply id_dom].
    apply compose_subst_fst.
    eapply transitivity; 
      [ apply prod_arr_compose |].
    apply product_arr_subst_X.
    rewrite /coprod_arr /prod_arr.
    apply compose_subst_snd, id_dom.
  Defined.

  (* 補助関数 *)
  Program Definition listF_alg_gen {A X: C}
             (fnil: T --> X)(fcons: prod A X --> X)
  : Algebra (listF A) :=
    {| alg_arr := coproduct_arr (coprod T (prod A X)) _ fnil fcons |}.
  
End ListFunctor.


(* これより Set からなる圏 Sets を構成する *)
(* まずは関数の等価性を定義。外延的等価性。 *)
Definition eq_function {A B: Set}(f g: A -> B) :=
  forall x, f x = g x.
Hint Unfold eq_function.

Program Definition function (A B: Set): Setoid :=
  {| equal := @eq_function A B |}.
Next Obligation.
  split; rewrite /eq_function.
  - by move=> x /=.
  - by move=> x y /=.
  - move=> x y z /= Hxy Hyz a /=.
    by rewrite -Hyz -Hxy.
Qed.

Definition compose_function
        {A B C: Set}(f: function A B)(g: function B C): function A C :=
  fun x => g (f x).
Hint Unfold compose_function.

Definition id_function (A: Set): function A A :=
  fun x => x.
Hint Unfold id_function.

(* Sets 本体の定義 *)
Program Definition Sets: Category :=
  {| arr := function;
     compose := @compose_function;
     id := id_function |}.
Next Obligation.
  by move=> x //=; rewrite /compose_function -Heq_snd Heq_fst.
Qed.

(* 以降、積やらを持つことの "証明" *)
Open Scope type_scope.
Program Definition Sets_Product (A B: Sets): Product A B :=
  {| proj_X := @fst A B: (A*B:Sets) --> A;
     proj_Y := @snd A B: (A*B:Sets) --> B;
     product_arr Q f g := fun x => (f x, g x) |}.
Next Obligation.
  move=> x //=; rewrite -H0 -H /compose_function //=.
  by destruct (h x).
Qed.

Canonical Structure Sets_hasProduct: hasProduct Sets :=
  {| prod := Sets_Product |}.
  
Program Definition Sets_CoProduct (A B: Sets): CoProduct A B :=
  {| in_X := @inl A B: A --> (A+B:Sets);
     in_Y := @inr A B: B --> (A+B:Sets);
     coproduct_arr Q f g := fun x => match x with
                                       | inl a => f a
                                       | inr b => g b
                                     end |}.
Next Obligation.
  move=> [a | b] //=.
  - rewrite -H /compose_function //=.
  - rewrite -H0 /compose_function //=.
Qed.

Canonical Structure Sets_hasCoProduct: hasCoProduct Sets :=
  {| coprod := Sets_CoProduct |}.
  
Program Definition Sets_Terminal: Terminal Sets :=
  {| terminal_arr X := (fun (x: X) => tt): X --> (unit:Sets) |}.
Next Obligation.
  by move=> x //=; destruct (f x).
Qed.

(* リスト函手の Sets 版 *)
Definition listF_Sets (A: Set) :=
  (listF Sets_hasProduct Sets_hasCoProduct Sets_Terminal A).

(* list A が listF_A 代数であることを述べて、 *)
Program Definition list_Algebra (A: Set): Algebra (listF_Sets A) :=
  {| alg_arr := fun (x: unit + (A*list A)) =>
                  match x with
                    | inl _ => nil
                    | inr (h,t) => cons h t
                  end |}.


Fixpoint listF_init_map_function (A: Set)
        (X: Algebra (listF_Sets A))(l: list A): alg_obj X :=
  match l with
    | nil => alg_arr X (inl tt)
    | cons h t => alg_arr X (inr (h,listF_init_map_function X t))
  end.

Program Definition listF_init_map (A: Set)
        (X: Algebra (listF_Sets A)): Algebra_Map (list_Algebra A) X :=
  {| alg_map := listF_init_map_function X |}.
Next Obligation.
  move=> [[] | [h t]] //=.
Qed.

(* さらに始代数であることを示す *)
Program Definition listF_init (A: Set)
: Initial (ALG (listF Sets_hasProduct Sets_hasCoProduct Sets_Terminal A)) :=
  {| initial_arr X := listF_init_map X |}.
Next Obligation.
  move: X f => [] //= X Xf [] /= f /=.
  rewrite /eq_Algebra_Map //= /eq_function /= /compose_function /= /coprod_arr /= /compose_function /prod_arr /= /compose_function /= /id_function //=.
  move=> Hf.
  elim=> [| h t /= ->];
    [apply: (Hf (inl tt)) | apply: (Hf (inr (h,t))) ].
Qed.

(* 道具が全て得られたので、 リスト函手の catamorphism を構成し、*)
Definition cata_foldr {A X: Set}(e: X)(f: A -> X -> X): list A -> X :=
  catamorphism (listF_init A)
               (listF_alg_gen Sets_hasProduct Sets_hasCoProduct
                              Sets_Terminal
                              (fun _: unit => e)
                              (fun p: A*X => f (fst p) (snd p))).

(* 一方で通常の foldr も定義し、 *)
Fixpoint foldr {A X: Set}(e: X)(f: A -> X -> X)(l: list A): X :=
  match l with
    | nil => e
    | cons h t => f h (foldr e f t)
  end.

(* 両者の等価性を証明。 *)
Theorem foldr_cata_foldr_equiv:
  forall (A X: Set)(e: X)(f: A -> X -> X)(l: list A),
    cata_foldr e f l = foldr e f l.
Proof.
  by move=> A X e f; elim=> [| h t /= <-] //=.
Qed.

(* やったね! これで foldr に関する様々な議論をする時、定理証明系の上でも圏論的な性質を参照できるようになる(予定だ)よ! *)

(* そして Haskell へ...... *)
Extraction Language Haskell.
Extract Inductive list => "([])" ["[]" "(:)"].
Extraction "ext/cata_foldr.hs" cata_foldr.

(* Coq2Haskell は改善した方がいい部分ありますな *)
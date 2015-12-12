Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Init.

(** * スコープの設定
大きなライブラリになるので、定義する記法を二つのスコープに纏める。

多少冗長な記法は [category_scope] に、通常使う記法は [cat_scope] に収める。
 **)
Delimit Scope category_scope with category.
Delimit Scope cat_scope with cat.

(** COC をインポートする場合、基本的に [cat_scope] を開くようにする。 **)
Global Open Scope cat_scope.

(** * Setoid **)
(** 要素の等価性を同値関係で以って与える構造。同値関係で型の商を取っている。 **)
Module Setoid.
  Structure type :=
    make {
        carrier: Type;
        equal: relation carrier;
        
        prf: Equivalence equal
      }.

  Notation build equal :=
    (@make _ equal (@Build_Equivalence _ equal _ _ _)).

  Module Ex.
    Notation isSetoid := Equivalence.
    Notation Setoid := type.
    Global Arguments equal {t} x y.
    Coercion carrier: Setoid >-> Sortclass.
    Coercion prf: Setoid >-> Equivalence.
    Existing Instance prf.

    Notation "(== :> A )" := (@equal A): cat_scope.
    Notation "(==)" := (==:> _): cat_scope.
  
    Notation "x == y :> X" := (@equal X x y) (at level 70, y at next level, no associativity): cat_scope.
    (* Notation "x == y" := (x == y :> _) (at level 70, no associativity): cat_scope. *)
    Notation "x == y" := ((x == y :> _)%category) (at level 70): cat_scope.

  End Ex.
End Setoid.
Export Setoid.Ex.


(** * 「一意に存在」 **)
(**
あらゆる場面に出てくる普遍性の記述には欠かせない。
uniqueness の記述には [Setoid] が必要だったため、ここで定義する。
 **)
Definition unique {X : Setoid}(P: X -> Prop)(x: X) :=
  P x /\ forall (x': X), P x' -> x == x'.

Notation "'exists!_' x .. y , p" :=
  (ex (unique (fun x => .. (ex (unique (fun y => p))) ..)))
    (at level 200, x binder, right associativity,
     format "'[' 'exists!_'  '/ ' x .. y ,  '/ ' p ']'"): cat_scope.

Ltac etrans := eapply transitivity.

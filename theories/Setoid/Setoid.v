Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Export Coq.Program.Basics Coq.Program.Tactics Coq.Setoids.Setoid Coq.Classes.Morphisms.

(** * スコープの設定
大きなライブラリになるので、定義する記法を二つのスコープに纏める。

多少冗長な記法は [category_scope] に、通常使う記法は [cat_scope] に収める。
 **)
Delimit Scope category_scope with category.
Delimit Scope cat_scope with cat.

(** COC をインポートする場合、基本的に [cat_scope] を開くようにする。 **)
Open Scope cat_scope.

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

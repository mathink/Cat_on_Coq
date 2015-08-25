Require Import COC.Init.Prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Delimit Scope cat_scope with cat.
Open Scope cat_scope.

Require Import COC.Init.Relations.

(* Setoid *)
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

    Notation "x == y :> X" := (@equal X x y)
                                (at level 70,
                                 y at next level, no associativity): cat_scope.
    (* Notation "x == y" := (x == y :> _) (at level 70, no associativity): cat_scope. *)
    Notation "x == y" := (x == y :> _) (at level 70, only parsing): cat_scope.

  End Ex.
End Setoid.
Export Setoid.Ex.
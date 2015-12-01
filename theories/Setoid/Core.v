Require Import COC.Init.Prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Delimit Scope category_scope with category.
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

    Notation "(== :> A )" := (@equal A).
    Notation "(==)" := (==:> _).
  
    Notation "x == y :> X" := (@equal X x y)
                                (at level 70,
                                 y at next level, no associativity): cat_scope.
    (* Notation "x == y" := (x == y :> _) (at level 70, no associativity): cat_scope. *)
    Notation "x == y" := ((x == y :> _)%category) (at level 70): cat_scope.

  End Ex.
End Setoid.
Export Setoid.Ex.


Definition unique {X : Setoid}(P: X -> Prop)(x: X) :=
  P x /\ forall (x': X), P x' -> x == x'.

Notation "'exists!_' x .. y , p" :=
  (ex (unique (fun x => .. (ex (unique (fun y => p))) ..)))
    (at level 200, x binder, right associativity,
     format "'[' 'exists!_' '/ ' x .. y , '/ ' p ']'").

Ltac etrans := eapply transitivity.

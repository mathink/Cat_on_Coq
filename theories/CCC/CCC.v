(** * Cartesian Closed Category **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Base.Main
        COC.Cons.Terminal
        COC.Cons.Product
        COC.Cons.Exponential.

Structure CCC :=
  {
    ccc_category:> Category;
    ccc_terminal: Terminal ccc_category;
    ccc_product: forall (X Y: ccc_category), Product _ X Y;
    ccc_exp: forall (Y Z: ccc_category), Exponential ccc_product Y Z
  }.

Notation "[ Z ^^ Y 'on' CCC ]" := (ccc_exp (c:=CCC) Y Z).
Infix "*" := (ccc_product (c:=_)).
Notation "Z ^^ Y" := [Z ^^ Y on _] (at level 40, left associativity).
Notation "T_{ CCC }" := (ccc_terminal CCC) (format "T_{ CCC }").

(* Setoids as CCC *)
Canonical Structure ccc_of_Setoids :=
  Build_CCC terminal_of_Setoids exponential_of_Setoids.

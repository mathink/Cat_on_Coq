(* Instances of Category Class  *)

Set Implicit Arguments.
Require Import Setoid Category.

(* Example *)
Definition ext_eq {X Y: Set}(f g: X -> Y): Prop :=
  forall x, f x = g x.
  
Program Instance ext_eq_Equivalence (X Y: Set)
: Equivalence (A:=X -> Y) ext_eq.
Next Obligation.
  congruence.
Qed.
Next Obligation.
  congruence.
Qed.
Next Obligation.
  congruence.
Qed.

Program Instance FunctionSetoid (X Y: Set): Setoid :=
  { carrier := X -> Y : Set;
    equal f g := forall x, f x = g x }.

Program Instance Sets: Category :=
  { obj := Set;
    arr X Y := FunctionSetoid X Y;
    compose X Y Z f g := fun x => g (f x);
    id X := fun x: X => x }.
Next Obligation.
  congruence.
Qed.


(* Sets の始対象は Empty_set です 

   以下における定義と証明は，人によってはなんか腑に落ちんなぁという人もいるかもしれない．
 *)
Definition from_Empty_set (A: Set)(f: Empty_set): A.
  elim f.
Defined.

Program Instance Empty_set_Initial
: Initial Sets Empty_set :=
  { In X := from_Empty_set X }.
Next Obligation.
  contradiction.
Qed.

(* Sets の終対象は unit です 

   こちらは大丈夫(何が?)
 *)
Definition to_unit (A: Set): A -> unit :=
  fun _ => tt.

Program Instance unit_Terminal
: Terminal Sets unit :=
  { Te X := to_unit (A:=X) }.
Next Obligation.
  compute.
  destruct (f x); simpl.
  reflexivity.
Qed.

(* 直積型は直積対象です *)
Program Instance prod_Product (X Y: Sets)
: Product Sets X Y :=
  { product := prod X Y;
    proj_X := @fst X Y;
    proj_Y := @snd X Y;
    product_arr Q f g := fun q => (f q,g q) }.
Next Obligation.
  generalize (H x) (H0 x);
  destruct (h x); simpl; congruence.
Qed.


(* 直和型は余直積対象です *)
Program Instance sum_CoProduct (X Y: Sets)
: CoProduct Sets X Y :=
  { coproduct := sum X Y;
    in_X := @inl X Y;
    in_Y := @inr X Y;
    coproduct_arr Q f g :=
      fun m => match m with inl x => f x | inr y => g y end }.
Next Obligation.
  destruct x as [x | y]; congruence.
Qed.

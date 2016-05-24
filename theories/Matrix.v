Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Set Contextual Implicit.

Generalizable All Variables.

(** * 長さ付きリスト **)
Module Vector.
  Inductive type (X: Type): nat -> Type :=
  | nil: type X 0
  | cons:forall {n: nat}, X -> type X n -> type X (S n).

  Module Ex.
    Notation Vector := type.

    Delimit Scope vector_scope with vector.
    Infix ":>" := cons (at level 60, right associativity): vector_scope.
    Notation "[|]" := nil (format "[|]"): vector_scope.
    Notation "[| x , .. , y ]" := ((x%vector) :> .. ((y%vector):>Vector.nil) .. )%vector (at level 0): vector_scope.
  End Ex.

  Import Ex.
  Open Scope vector_scope.
  
  Definition head (X: Type)(n: nat)(v: Vector X (S n)): X :=
    match v with
    | x:>_ => x
    end.

  Definition tail (X: Type)(n: nat)(v: Vector X (S n)): Vector X n :=
    match v with
    | _:>xs => xs
    end.

  Fixpoint add_with (M: Type)(op: M -> M -> M)(n: nat)(v1: Vector M n): Vector M n -> Vector M n :=
    match v1 in Vector _ n' return Vector _ n' -> Vector _ n' with
    | [|] => fun _ => [|]
    | x1:>xs1 => fun v2 => (op x1 (head v2)):>(add_with op xs1 (tail v2))
    end.

  Fixpoint mul_with (R: Type)(add mul: R -> R -> R)(e: R)(n: nat)(v1: Vector R n): Vector R n -> R :=
    match v1 in Vector _ n' return Vector _ n' -> R with
    | [|] => fun _ => e
    | cons x1 xs1 => fun v2 => (add (mul x1 (head v2)) (mul_with add mul e xs1 (tail v2)))
    end.

  Fixpoint append (X: Type)(n m: nat)(v1: Vector X n): Vector X m -> Vector X (n + m) :=
    match v1 with
    | [|] => fun v2 => v2
    | x:>xs => fun v2 => x:>(append xs v2)
    end.

  Fixpoint rep (X: Type)(n: nat)(x: X): Vector X n :=
    match n as n' return Vector X n' with
    | O => [|]
    | S p => x:>rep x
    end.

  Module Ex2.
    Infix "++" := append (at level 60, right associativity): vector_scope.
  End Ex2.
End Vector.
Export Vector.Ex.
Export Vector.Ex2.

Module Matrix.

  Definition type (X: Type)(n m: nat) := (Vector (Vector X m) n).
  Module Ex.
    Notation Matrix := type.
    Open Scope vector_scope.
  End Ex.

  Import Ex.
  Open Scope vector_scope.

  Definition add_with (M: Type)(op: M -> M -> M)(p q: nat)(m1 m2: Matrix M p q): Matrix M p q :=
    @Vector.add_with (Vector M q) (@Vector.add_with M op q) p m1 m2.
  Arguments add_with M op p q m1 m2 /.


  Fixpoint happ (X: Type)(p q r: nat)(m1: Matrix X p q): Matrix X p r -> Matrix X p (q + r) :=
    match m1 in (Vector _ p')
          return (Vector (Vector X r) p' -> Vector (Vector X (q + r)) p')
    with
    | [|] => fun _  => [|]
    | v1:>vs1 => fun m2 => (v1 ++ (Vector.head m2)) :> happ vs1 (Vector.tail m2)
    end.

  Fixpoint vector_transpose (X: Type)(n: nat)(v: Vector X n): Matrix X n 1 :=
    match v in Vector _ n'
          return Vector (Vector X 1) n'
    with
    | [|] => [|]
    | x:>xs => (x:>[|]) :> (vector_transpose xs)
    end.
  
  Fixpoint transpose_aux (X: Type)(p q r: nat)(n: Matrix X r p): Matrix X p q -> Matrix X p (r + q) :=
    match n in Vector _ r'
          return Vector (Vector _ q) p -> Vector (Vector _ (r' + q)) p
    with
    | [|] => fun m => m
    | v:>vs => fun m => happ (vector_transpose v) (transpose_aux vs m)
    end.

  Eval simpl in transpose_aux [|[|1,2,3],[|4,5,6]] [|[|],[|],[|]].
     (* = [|[|1, 4], [|2, 5], [|3, 6]] *)
     (* : Matrix BinNums.Z 3 (2 + 0) *)
  
  Definition transpose (M: Type)(p q: nat)(m: Matrix M p q): Matrix M q p.
  Proof.
    rewrite plus_n_O.
    exact (transpose_aux m (Vector.rep (n:=q) [|])).
  Defined.
  Arguments transpose M p q m /.

  Eval simpl in transpose [|[|1,2,3],[|4,5,6]].
  Goal  transpose [|[|1,2,3],[|4,5,6]] = [|[|1, 4], [|2, 5], [|3, 6]].
  Proof.
    simpl.
(* 1 subgoal, subgoal 1 (ID 484) *)
  
(*   ============================ *)
(*    eq_rect_r (Matrix BinNums.Z 3) [|[|1, 4], [|2, 5], [|3, 6]] (plus_n_O 2) = *)
(*    [|[|1, 4], [|2, 5], [|3, 6]] *)

(* (dependent evars:) *)
  Admitted.

End Matrix.
Export Matrix.Ex.


(** * 例 **)
Require Import COC.Setoid.
Require Import COC.Algebra.

Open Scope vector_scope.

Definition vadd (M: Monoid) := Vector.add_with (Monoid.op M).
Arguments vadd M n v1 v2 /.
Definition vmul (R: Ring) := Vector.mul_with (Ring.add R) (Ring.mul R) (Ring.z R).
Arguments vmul R n v1 v2 /.

Eval simpl in vadd [|1,2,3] [|4,5,6].
     (* = [|5, 7, 9] *)
     (* : Vector Zplus_monoid 3 *)
Eval simpl in vadd (M:=Zmult_monoid) [|1,2,3] [|4,5,6].
     (* = [|4, 10, 18] *)
     (* : Vector Zmult_monoid 3 *)
Eval simpl in vmul [|1,2,3] [|4,5,6].
     (* = 32 *)
     (* : Z_ring *)

Definition madd (M: Monoid) := Matrix.add_with (Monoid.op M).
Arguments madd M p q m1 m2 /.

Eval simpl in madd
                [|[|1,2,3],
                  [|4,5,6]]
                [|[|1,2,3],
                  [|4,5,6]].
     (* = [|[|2, 4, 6], [|8, 10, 12]] *)
     (* : Matrix Zplus_monoid 2 3 *)




Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Set Contextual Implicit.

Generalizable All Variables.

(** * 長さ付きリスト **)
Require Import ProofIrrelevance.
Require Import Arith.
Require Import COC.Setoid COC.AlgebraicStructures.

Module Vector.
  Structure type (X: Type)(n: nat) :=
    make {
        get: forall {p: nat}(H: p < n), X
      }.

  Module Ex.
    Notation Vector := type.
    Coercion get: Vector >-> Funclass.

    Delimit Scope vector_scope with vector.
    Notation "( x ; H :-> y )" := (make (fun x H  => y)) (H at next level): vector_scope.
  End Ex.

  Import Ex.
  Open Scope vector_scope.

  Definition equal (X: Setoid)(n: nat): relation (Vector X n) :=
    fun v1 v2 => forall (p: nat)(H: p < n), v1 _ H == v2 _ H.
  Arguments equal X n v1 v2 /.
  
  Program Canonical Structure setoid (X: Setoid)(n: nat) :=
    Setoid.build (@equal _ n).
  Next Obligation.
    intros v p H.
    reflexivity.
  Qed.
  Next Obligation.
    intros v1 v2 Heq p H; simpl in *.
    now symmetry; apply Heq.
  Qed.
  Next Obligation.
    intros v1 v2 v3 Heq12 Heq23 p H; simpl in *.
    transitivity (v2 _ H).
    - now apply Heq12.
    - now apply Heq23.
  Qed.

  Open Scope field_scope.
  Definition add_with (X Y Z: Type)(op: X -> Y -> Z)(n: nat)(v1: Vector X n)(v2: Vector Y n): Vector Z n :=
    (p;H :-> op (v1 _ H) (v2 _ H)).
  Definition add (K: Field) := @add_with _ _ _ (Field.add K).
  
  Definition tail (X: Type)(n: nat)(v: Vector X (S n)): Vector X n :=
    (p;H :-> v _ (Lt.lt_n_S p n H)).
  Arguments tail X n v /.
    
  Fixpoint mul_with (X Y Z W: Type)(add: Z -> W -> W)(mul: X -> Y -> Z)(e: W)(n: nat): Vector X n -> Vector Y n -> W :=
    match n with
    | O => fun _ _ => e
    | S p => fun v1 v2 =>
               (add (mul (get v1 (PeanoNat.Nat.lt_0_succ p))
                         (get v2 (PeanoNat.Nat.lt_0_succ p)))
                    (mul_with add mul e (tail v1) (tail v2)))
    end.

  Definition mul (K: Field)(n: nat)(v1 v2: Vector K n): K :=
    mul_with (Field.add K) (Field.mul K) (Field.z K) v1 v2.

  Program Instance mul_proper (K: Field)(n: nat):
    Proper ((==) ==> (==) ==> (==)) (@mul K n).
  Next Obligation.
    intros v v' Heqv u u' Hequ; simpl in *; intros.
    induction n; simpl.
    - reflexivity.
    - unfold mul in *; simpl.
      rewrite Heqv, Hequ, IHn.
      + reflexivity.
      + now simpl; intros; apply Heqv.
      + now simpl; intros; apply Hequ.
  Qed.

  Definition map (X Y: Type)(f: X -> Y)(n: nat)(v: Vector X n) :=
    (p;H :-> f (v _ H)).
  
  Lemma scalar_mul_l:
    forall (K: Field)(n: nat)(x: K)(v u: Vector K n),
      (x * mul v u) == mul (map (`(x * y)) v) u.
  Proof.
    induction n; simpl.
    - unfold mul; simpl.
      now intros; rewrite (Field.mul_0_r x).
    - intros.
      unfold mul; simpl.
      rewrite !distributive_l.
      rewrite <- associative.
      rewrite (IHn x (tail v) (tail u)); simpl.
      unfold mul.
      reflexivity.
  Qed.
      
  Lemma distributive_l:
    forall (K: Field)(n: nat)(v u w: Vector K n),
      (mul v u + mul v w) == mul v (add u w).
  Proof.
    induction n; simpl.
    - unfold add, mul; simpl.
      now intros; rewrite left_identical.
    - intros.
      generalize (IHn (tail v) (tail u) (tail w)); simpl.
      unfold add, mul; simpl.
      rewrite !distributive_l.
      intros H.
      rewrite (Monoid.commute_l (M:=Ring.g K)); simpl.
      rewrite <-associative.
      rewrite H.
      rewrite (Monoid.commute_l (M:=Ring.g K)); simpl.
      rewrite !associative.
      reflexivity.
  Qed.
  
  Lemma distributive_r:
    forall (K: Field)(n: nat)(v u w: Vector K n),
      (mul v w + mul u w) == mul (add v u) w.
  Proof.
    induction n; simpl.
    - unfold add, mul; simpl.
      now intros; rewrite left_identical.
    - intros.
      generalize (IHn (tail v) (tail u) (tail w)); simpl.
      unfold add, mul; simpl.
      rewrite !distributive_r.
      intros H.
      rewrite (Monoid.commute_l (M:=Ring.g K)); simpl.
      rewrite <-associative.
      rewrite H.
      rewrite (Monoid.commute_l (M:=Ring.g K)); simpl.
      rewrite !associative.
      reflexivity.
  Qed.
  
Module Ex2.
    Infix "*" := mul: vector_scope.
  End Ex2.
End Vector.
Export Vector.Ex.
Export Vector.Ex2.

(** * 行列 **)
Module Matrix.

  Definition type (X: Type)(n m: nat) :=
    Vector (Vector X m) n.

  Module Ex.
    Notation Matrix := type.
  End Ex.

  Import Ex.
  Open Scope vector_scope.
  Open Scope field_scope.

  Definition equal (X: Setoid)(n m: nat): relation (Matrix X n m) :=
    fun M N =>
      forall p (Hr: p < n) q (Hc: q < m),
        M _ Hr _ Hc == N _ Hr _ Hc.
  Arguments equal X n m M N /.

  Program Instance equiv (X: Setoid)(n m: nat): Equivalence (@equal X n m).
  Next Obligation.
    intros M p Hr q Hc.
    reflexivity.
  Qed.
  Next Obligation.
    intros M N Heq p Hr q Hc; simpl in *.
    now symmetry; apply Heq.
  Qed.
  Next Obligation.
    intros M N K HeqMN HeqNK p Hr q Hc; simpl in *.
    transitivity (N _ Hr _ Hc).
    - now apply HeqMN.
    - now apply HeqNK.
  Qed.

  Canonical Structure setoid (X: Setoid)(n m: nat) := Setoid.make (@equiv X n m).

  (** ** 体上の行列は群や環を構成する **)
  Definition add_with (X Y Z: Type)(op: X -> Y -> Z)(n m: nat)(M: Matrix X n m)(N: Matrix Y n m): Matrix Z n m :=
    (p;Hrow :-> (q;Hcolumn :-> op (M _ Hrow _ Hcolumn) (N _ Hrow _ Hcolumn))).

  Definition transpose (X: Type)(n m: nat)(M: Matrix X n m): Matrix X m n :=
    (p;Hrow :-> (q;Hcolumn :-> M _ Hcolumn _ Hrow)).

  Lemma transpose_idempotent:
    forall (X: Setoid)(n m: nat)(M: Matrix X n m),
      transpose (transpose M) == M.
  Proof.
    unfold transpose; simpl.
    reflexivity.
  Qed.
  
  Definition rest (X: Type)(n m: nat)(M: Matrix X n (S m)): Matrix X n m :=
    transpose (Vector.tail (transpose M)).
  

  (* add group *)
  Definition add (X: Ring)(n m: nat) :=
    @add_with _ _ _ (Ring.add X) n m.
  Arguments add X n m _ _ /.

  Program Instance add_is_binop (X: Ring)(n m: nat): isBinop (@add X n m).
  Next Obligation.
    intros M M' HeqM N N' HeqN; simpl in *; intros.
    now rewrite HeqM, HeqN.
  Qed.
  Canonical Structure add_binop (X: Ring)(n m: nat) :=
    Binop.make (add_is_binop X n m).

  Definition zero (X: Ring)(n m: nat): Matrix X n m :=
    (p;Hrow :-> (q;Hcolumn :-> Ring.z X)).

  Program Instance add_is_monoid (X: Ring)(n m: nat):
    isMonoid (@add_binop X n m) (@zero X n m).
  Next Obligation.
    intros M N K; simpl in *; intros.
    now rewrite associative.
  Qed.
  Next Obligation.
    split; intros M; simpl in *; intros.
    - now rewrite left_identical.
    - now rewrite right_identical.
  Qed.
  Canonical Structure add_monoid (X: Ring)(n m: nat) :=
    Monoid.make (add_is_monoid X n m).
  
  Definition minus (X: Ring)(n m: nat)(M: Matrix X n m): Matrix X n m :=
    (p;Hr :-> (q;Hc :-> - M _ Hr _ Hc))%rng.
  Arguments minus X n m M /.

  Program Instance minus_is_map (X: Ring)(n m: nat): isMap (@minus X n m).
  Next Obligation.
    intros M M' HeqM; simpl in *; intros.
    now rewrite HeqM.
  Qed.
  Canonical Structure minus_map (X: Ring)(n m: nat) := Map.make (minus_is_map X n m).

  Program Instance add_is_group (X: Ring)(n m: nat):
    isGroup (@add_binop X n m) (@zero X n m) (@minus_map X n m).
  Next Obligation.    
    split; intros M; simpl; intros.
    - now rewrite left_invertible.
    - now rewrite right_invertible.
  Qed.
  Canonical Structure add_group (X: Ring)(n m: nat) :=
    Group.make (add_is_group X n m).

  (* add mul Ring *)
  Definition mul_with (X Y Z W: Type)(add: Z -> W -> W)(mul: X -> Y -> Z)(e: W)(n m k: nat)(M: Matrix X n m)(N: Matrix Y m k): Matrix W n k :=
    (p;Hrow :-> (q;Hcolumn :-> Vector.mul_with add mul e (M _ Hrow) (transpose N _ Hcolumn))).

  Definition mul (X: Field)(n m k: nat)(M: Matrix X n m)(N: Matrix X m k): Matrix X n k :=
    (p;Hrow :-> (q;Hcolumn :-> (M _ Hrow * transpose N _ Hcolumn)%vector)).
  Arguments mul X n m k _ _ /.

  Lemma mul_assoc:
    forall (X: Field)(n m k l: nat)(M: Matrix X n m)(N: Matrix X m k)(K: Matrix X k l),
      mul M (mul N K) == mul (mul M N) K.
  Proof.
    simpl.
    intros X n m; revert n.
    induction m; simpl.
    - unfold Vector.mul; simpl.
      intros _ k l _ _ K _ _.
      induction k; simpl.
      + reflexivity.
      + intros.
        rewrite Field.mul_0_l, left_identical; simpl.
        rewrite <- (IHk (Vector.tail K) _ Hc).
        reflexivity.
    - intros.
      unfold Vector.mul; simpl.
      rewrite (IHm _ _ _ (rest M) (Vector.tail N) K _ Hr _ Hc); simpl.
      clear IHm.
      generalize (@Vector.scalar_mul_l _ k ((M p Hr) 0%nat (PeanoNat.Nat.lt_0_succ m)) (N 0%nat (PeanoNat.Nat.lt_0_succ m)) (q0; (Hcolumn) :-> (K q0 Hcolumn) q Hc)).
      unfold Vector.map; simpl.
      intro H; rewrite H; clear H; simpl.
      rewrite Vector.distributive_r; simpl.
      unfold Vector.add, Vector.add_with, Vector.mul; simpl.
      reflexivity.
  Qed.

  Program Instance mul_is_binop (X: Field)(n: nat): isBinop (@mul X n n n).
  Next Obligation.
    intros M M' HeqM N N' HeqN; simpl in *; intros.
    apply Vector.mul_proper.
    - simpl; intros.
      now apply HeqM.
    - simpl; intros.
      now apply HeqN.
  Qed.
  Canonical Structure mul_binop (X: Field)(n: nat) :=
    Binop.make (mul_is_binop X n).
  
  Definition unit (X: Field)(n: nat): Matrix X n n :=
    (p;Hrow :-> (q;Hcolumn :->
                           if Nat.eqb p q then Ring.e X else Ring.z X)).

  Lemma unit_identical_l:
    forall (X: Field)(n m: nat)(M: Matrix X n m),
      mul (@unit _ n) M == M.
  Proof.
    simpl.
    induction n as [| n].
    - simpl.
      intros.
      unfold lt in Hr.
      inversion Hr.
    - simpl.
      destruct p; simpl.
      + intros.
        unfold Vector.mul; simpl.
        rewrite left_identical.

        assert (H: (PeanoNat.Nat.lt_0_succ n) = Hr).
        {
          now apply proof_irrelevance.
        }
        rewrite H; clear H.

        assert (H: Vector.mul_with (Field.add X) (Field.mul X) 0 (p; (_) :-> 0) (p; (H) :-> (M (S p) (Lt.lt_n_S p n H)) q Hc) == 0).
        {
          clear IHn.
          induction n; simpl.
          - reflexivity.
          - rewrite Field.mul_0_l, left_identical.
            now rewrite (IHn (Vector.tail M) (PeanoNat.Nat.lt_0_succ n)).
        }
        rewrite H; clear H.
        now rewrite right_identical.
      + intros.
        unfold Vector.mul; simpl.
        generalize (IHn m (Vector.tail M) p (Lt.lt_S_n _ _ Hr) q Hc).
        intros H; rewrite H; clear H.
        rewrite Field.mul_0_l, left_identical; simpl.
        assert (H: (Lt.lt_n_S p n (Lt.lt_S_n p n Hr)) = Hr).
        {
          now apply proof_irrelevance.
        }
        now rewrite H.
  Qed.

  Lemma unit_identical_r:
    forall (X: Field)(n m: nat)(M: Matrix X n m),
      mul M (@unit _ m) == M.
  Proof.
    simpl.
    intros X n m M p Hr q Hc.
    revert m n M q Hc p Hr.
    induction m as [| m]; simpl.
    - intros; inversion Hc.
    - destruct q; simpl.
      + intros.
        unfold Vector.mul; simpl.
        rewrite right_identical.
        assert (H: (Vector.mul_with (Field.add X) (Field.mul X) 0
                                    (p0; (H) :-> (M p Hr) (S p0) (Lt.lt_n_S p0 m H)) 
                                    (p0; (_) :-> 0) == 0)).
        {
          clear IHm.
          induction m as [| m]; simpl.
          - reflexivity.
          - rewrite Field.mul_0_r, left_identical; simpl.
            now rewrite (IHm (rest M) (PeanoNat.Nat.lt_0_succ m)).
        }
        rewrite H; clear H.
        rewrite right_identical.
        assert (H: PeanoNat.Nat.lt_0_succ m = Hc).
        {
          now apply proof_irrelevance.
        }
        now rewrite H.
      + intros.
        unfold Vector.mul; simpl.
        rewrite Field.mul_0_r, left_identical.
        rewrite (IHm _ (rest M) _ (Lt.lt_S_n _ _ Hc) _ Hr); simpl.
        assert (H: (Lt.lt_n_S q m (Lt.lt_S_n q m Hc)) = Hc).
        {
          now apply proof_irrelevance.
        }
        now rewrite H.
  Qed.

  Program Instance mul_is_monoid (X: Field)(n: nat):
    isMonoid (@mul_binop X n) (@unit X n).
  Next Obligation.
    intros M N K; simpl; intros.
    apply mul_assoc.
  Qed.
  Next Obligation.
    split; intros M; simpl; intros.
    - now apply unit_identical_l.
    - now apply unit_identical_r.
  Qed.
  Canonical Structure mul_monoid (X: Field)(n: nat) :=
    Monoid.make (mul_is_monoid X n).

  Program Instance is_rng (X: Field)(n: nat):
    isRing (@add_binop X n n) (@zero X n n) (@minus_map X n n)
            (@mul_binop X n) (@unit X n).
  Next Obligation.
    intros M N; simpl; intros.
    now rewrite commute.
  Qed.
  Next Obligation.
    split; simpl; intros.
    - now rewrite Vector.distributive_l.
    - now rewrite Vector.distributive_r.
  Qed.
  Canonical Structure rng (X: Field)(n: nat) :=
    Ring.make (@is_rng X n).
End Matrix.
Export Matrix.Ex.

(** * 行列と加群
M(m,n) は (M(m),M(n))-双加群
 **)
Section MatrixModule.
  Context (X: Field)(m n: nat).
  Program Instance Matrix_is_abelian :
    isAbelian (Matrix.add_group X m n).
  Next Obligation.
    intros M N; simpl; intros.
    now rewrite commute.
  Qed.
  Canonical Structure Matrix_abelian := Abelian.make Matrix_is_abelian.


  Let lsm (M: Matrix X m m)(N: Matrix X m n): Matrix X m n := Matrix.mul M N.
  Let rsm (N: Matrix X m n)(M: Matrix X n n): Matrix X m n := Matrix.mul N M.

  (* W.I.P *)
  Program Instance MatrixOnField_is_lmod: isLMod (A:=Matrix.rng X m)(M:=Matrix_abelian) lsm.
  Next Obligation.
    intros M M' HeqM N N' HeqN; simpl; intros.
    simpl in HeqM, HeqN.
    apply Vector.mul_proper; simpl; intros.
    - now apply HeqM.
    - now apply HeqN.
  Qed.
  Next Obligation.
    rewrite Vector.distributive_l; simpl.
    apply Vector.mul_proper; simpl; intros; reflexivity.
  Qed.
  Next Obligation.
    rewrite Vector.distributive_r; simpl.
    apply Vector.mul_proper; simpl; intros; reflexivity.
  Qed.
  Next Obligation.
    symmetry.
    now apply Matrix.mul_assoc.
  Qed.
  Next Obligation.
    now apply Matrix.unit_identical_l.
  Qed.

  Program Instance MatrixOnField_is_rmod: isRMod (A:=Matrix.rng X n)(M:=Matrix_abelian) (rsm).
  Next Obligation.
    intros M M' HeqM N N' HeqN; simpl; intros.
    simpl in HeqM, HeqN.
    apply Vector.mul_proper; simpl; intros.
    - now apply HeqM.
    - now apply HeqN.
  Qed.
  Next Obligation.
    rewrite Vector.distributive_r; simpl.
    apply Vector.mul_proper; simpl; intros; reflexivity.
  Qed.
  Next Obligation.
    rewrite Vector.distributive_l; simpl.
    apply Vector.mul_proper; simpl; intros; reflexivity.
  Qed.
  Next Obligation.
    now apply Matrix.mul_assoc.
  Qed.
  Next Obligation.
    now apply Matrix.unit_identical_r.
  Qed.

  Program Instance MatrixOnField_is_bimod: isBiMod (A:=Matrix.rng X m) (B:=Matrix.rng X n)(M:=Matrix_abelian) lsm rsm.
  Next Obligation.
    symmetry.
    now apply Matrix.mul_assoc.
  Qed.
  
End MatrixModule.

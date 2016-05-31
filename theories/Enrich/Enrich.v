Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Setoid
        COC.Category
        Construction
        Monoidal.

Structure Enriched (V: Monoidal) :=
  {
    obj: Type;
    hom: forall (X Y: obj), V;
    comp: forall X Y Z, V ((hom X Y) • (hom Y Z)) (hom X Z);
    id: forall X, V (Monoidal.unit V) (hom X X);
    (** 
#\[
\xymatrix{
Hom(X,Y)\otimes(Hom(Y,Z)\otimes Hom(Z,W)) \ar[rr]^{\alpha} \ar[d]_{Id \otimes \circ_{Y,Z,W}}& & (Hom(X,Y)\otimes Hom(Y,Z))\otimes Hom(Z,W) \ar[d]^{\circ_{X,Y,Z} \circ Id}\\
Hom(X,Y)\otimes Hom(Y,W) \ar[r]_{\circ_{X,Y,W}}& Hom(X,W) & Hom(X,Z)\otimes Hom(Z,W) \ar[l]^{\circ_{X,Z,W}}
}
\]#
     **)
    comp_assoc:
      forall (X Y Z W: obj),
        comp X Z W \o (comp X Y Z [] Id (hom Z W))\o Monoidal.assoc (hom X Y) (hom Y Z) (hom Z W)
        ==
        comp X Y W \o (Id (hom X Y) [] comp Y Z W );

    id_lambda:
      forall (X Y: obj),
        Monoidal.lambda (hom X Y) ==  comp X X Y \o (id X [] Id (hom X Y));

    id_rho:
      forall (X Y: obj),
        Monoidal.rho (hom X Y) ==  comp X Y Y \o (Id (hom X Y) [] id Y)
  }.

Section Setoids_as_Monoidal.
  Program Definition Prod_Bifunctor: Bifunctor Setoids Setoids Setoids.
  eapply
    (Functor.make (C:=Setoids[x]Setoids)(D:=Setoids)
                  (fobj := fun P => let (X,Y) := P in X [*] Y)
                  (fmap := fun P Q fg => let (X,Y) := P in
                                         let (Z,W) := Q in
                                         let (f, g) := fg in Prod.map f g)).
  split; simpl; intros.
  - split; simpl.
    + destruct x as [f f'], y as [g g'], H as [H H']; simpl in *.
      now apply H.
    + destruct x as [f f'], y as [g g'], H as [H H']; simpl in *.
      now apply H'.
  - destruct x as [x x'], X as [X X'], Y as [Y Y'], Z as [Z Z'], f as [f f'], g as [g g']; simpl in *.
    split; apply reflexivity.
  - destruct x as [x x'], X as [X X']; simpl; split; apply reflexivity.
  Defined.

  Inductive unit := tt.
  Program Definition unit_setoid: Setoid := Setoid.build (@eq unit).

  Program Definition Setoids_Monoidal: Monoidal :=
    {|
      Monoidal.cat := Setoids;
      Monoidal.mult := Prod_Bifunctor;
      Monoidal.unit := unit_setoid;
      Monoidal.assoc X Y Z := [:x_yz:-> ((x_yz.1, x_yz.2.1), x_yz.2.2)];
      Monoidal.assoc_inv X Y Z := [:xy_z:-> (xy_z.1.1, (xy_z.1.2, xy_z.2))];
      Monoidal.lambda X := [:p :-> p.2];
      Monoidal.lambda_inv X := [:x :-> (tt,x)];
      Monoidal.rho X := [:p :-> p.1];
      Monoidal.rho_inv X := [:x :-> (x,tt)]
    |}.
  Next Obligation.
    simpl; intros x x' H. 
    destruct x as [x [y z]], x' as [x' [y' z']], H as [Hx [Hy Hz]]; simpl in *.
    repeat split; auto.
  Qed.
  Next Obligation.
    intros x x' H. 
    destruct x as [[x y] z], x' as [[x' y'] z'], H as [[Hx Hy] Hz]; simpl in *.
    repeat split; auto.
  Qed.
  Next Obligation.
    simpl; intros [t x] [t' y] [Ht Hxy]; simpl in *; auto.
  Qed.
  Next Obligation.
    simpl; intros x y Hxy; simpl; split; auto.
  Qed.
  Next Obligation.
    simpl; intros [x t] [y t'] [Hxy Ht]; simpl in *; auto.
  Qed.
  Next Obligation.
    simpl; intros x y Hxy; simpl; split; auto.
  Qed.
  Next Obligation.
    split; simpl.
    - intros; destruct x as [x [y z]]; simpl.
      repeat split; apply reflexivity.
    - intros a b c [x [y z]]; simpl.
      repeat split; apply reflexivity.
    - intros a b c [[x y] z]; simpl.
      repeat split; apply reflexivity.
    - intros a b c d [x [y [z w]]]; simpl.
      repeat split; apply reflexivity.
    - intros a a' f [t x]; simpl; apply reflexivity.
    - intros a [t x]; simpl; split; auto.
      + destruct t; auto.
      + apply reflexivity.
    - intros a x; simpl; apply reflexivity.
    - intros a a' f [x t]; simpl; apply reflexivity.
    - intros a [x t]; simpl; split; auto.
      + apply reflexivity.
      + destruct t; auto.
    - intros a x; simpl; apply reflexivity.
    - intros a c [x [t z]]; simpl; repeat split; apply reflexivity.
  Qed.
End Setoids_as_Monoidal.

Program Definition Setoids_Enriched (C: Category): Enriched Setoids_Monoidal :=
  {|
    obj := Category.obj C;
    hom X Y := C X Y;
    comp X Y Z := [: fg :-> let (f,g) := fg in g \o f];
    id X := [: U :-> Id X]
  |}.
Next Obligation.
  intros [f g] [f' g'] [Hf Hg]; simpl in *.
  now rewrite Hf, Hg.
Qed.
Next Obligation.
  intros f g H; reflexivity.
Qed.
Next Obligation.
  destruct x as [f [g h]]; simpl.
  now rewrite catCa.
Qed.
Next Obligation.
  destruct x as [u f]; simpl.
  now rewrite catC1f.
Qed.
Next Obligation.
  destruct x as [f u]; simpl.
  now rewrite catCf1.
Qed.


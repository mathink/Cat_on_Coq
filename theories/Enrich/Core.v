Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Monoid.

Structure Enriched (V: Monoidal) :=
  {
    obj: Type;
    hom: forall (X Y: obj), V;
    comp: forall X Y Z, V ((hom X Y) • (hom Y Z)) (hom X Z);
    id: forall X, V (Monoidal.unit V) (hom X X);

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
  Program Definition Product_Bifunctor: Bifunctor Setoids Setoids Setoids.
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
  - intros [x x']; destruct X as [X X'], Y as [Y Y'], Z as [Z Z'], f as [f f'], g as [g g']; simpl in *.
    split; apply reflexivity.
  - intros [x x']; destruct X as [X X']; simpl; split; apply reflexivity.
  Defined.

  Inductive unit := tt.
  Program Definition unit_setoid: Setoid := Setoid.build (@eq unit).
  Next Obligation.
    intros x; auto.
  Qed.
  Next Obligation.
    intros x; auto.
  Qed.
  Next Obligation.
    intros x y z; intros; subst; auto.
  Qed.

  Program Definition Setoids_Monoidal: Monoidal :=
    {|
      Monoidal.cat := Setoids;
      Monoidal.mult := Product_Bifunctor;
      Monoidal.unit := unit_setoid;
      Monoidal.assoc X Y Z := [P:-> ((Prod.fst P, Prod.fst (Prod.snd P)), Prod.snd (Prod.snd P))];
      Monoidal.assoc_inv X Y Z := [P:-> (Prod.fst (Prod.fst P), ((Prod.snd (Prod.fst P)), Prod.snd P))];
      Monoidal.lambda X := [P :-> Prod.snd P];
      Monoidal.lambda_inv X := [x :-> (tt,x)];
      Monoidal.rho X := [P :-> Prod.fst P];
      Monoidal.rho_inv X := [x :-> (x,tt)]
    |}.
  Next Obligation.
    intros X Y Z; simpl; intros x x' H. 
    destruct x as [x [y z]], x' as [x' [y' z']], H as [Hx [Hy Hz]]; simpl in *.
    repeat split; auto.
  Qed.
  Next Obligation.
    intros X Y Z; simpl; intros x x' H. 
    destruct x as [[x y] z], x' as [[x' y'] z'], H as [[Hx Hy] Hz]; simpl in *.
    repeat split; auto.
  Qed.
  Next Obligation.
    simpl; intros X [t x] [t' y] [Ht Hxy]; simpl in *; auto.
  Qed.
  Next Obligation.
    simpl; intros X x y Hxy; simpl; split; auto.
  Qed.
  Next Obligation.
    simpl; intros X [x t] [y t'] [Hxy Ht]; simpl in *; auto.
  Qed.
  Next Obligation.
    simpl; intros X x y Hxy; simpl; split; auto.
  Qed.
  Next Obligation.
    split; simpl.
    - intros.
      intros [x [y z]]; simpl.
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
    comp X Y Z := [fg :-> let (f,g) := fg in g \o f];
    id X := [U :-> Id X]
  |}.
Next Obligation.
  intros C X Y Z [f g] [f' g'] [Hf Hg]; simpl in *.
  apply catCs; auto.
Qed.
Next Obligation.
  intros C X f g H; apply reflexivity.
Qed.
Next Obligation.
  simpl.
  intros C X Y Z W [f [g h]]; simpl.
  apply symmetry, catCa.
Qed.
Next Obligation.
  simpl.
  intros C X Y [u f]; simpl.
  apply symmetry, catC1f.
Qed.
Next Obligation.
  simpl.
  intros C X Y [f u]; simpl.
  apply symmetry, catCf1.
Qed.

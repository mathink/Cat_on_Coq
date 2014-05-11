
Require Import
(* Utf8 *)
Coq.Classes.Init
Coq.Program.Basics Coq.Program.Tactics
Coq.Classes.RelationClasses
Setoid
.

Set Implicit Arguments.
Unset Strict Implicit.
Reserved Notation "X --> Y" (at level 60, right associativity).
Reserved Notation "g • f" (at level 60, right associativity).


Structure Category :=
  { obj:> Type;
    arr (X Y: obj): Setoid where "X --> Y" := (arr X Y);

    compose {X Y Z: obj}:
      (X --> Y) -> (Y --> Z) -> (X --> Z) where "g • f" := (compose f g);

    id {X: obj}: X --> X;

    compose_assoc:
      forall (X Y Z W: obj)(f: X --> Y)(g: Y --> Z)(h: Z --> W),
        (h•g)•f == h•(g•f);
    compose_subst:
      forall (X Y Z: obj)(f f': X --> Y)(g g': Y --> Z)
         (Heq_fst: f == f')(Heq_snd: g == g'),
        g•f == g'•f';

    id_dom: (* renamed from id_left *)
      forall (X Y: obj)(f: X --> Y), compose id f == f;
    id_cod: (* renamed from id_rigth *)
      forall (X Y: obj)(f: X --> Y), compose f id == f }.
Arguments arr {category}(X Y): rename.
Arguments compose {category}{X Y Z}(f g): rename.
Arguments id {category}{X}: rename.
Notation "X --> Y" := (arr X Y) (at level 60, right associativity).
Notation "g • f" := (compose f g) (at level 60, right associativity).
Definition id_ {C: Category}(X: C) := @id C X.

Lemma compose_subst_fst:
  forall (C: Category)(X Y Z: C)(f f': X --> Y)(g: Y --> Z),
    f == f' -> g•f == g•f'.
Proof.
  intros.
  apply compose_subst; [ apply H | equiv_refl ].
Qed.

Lemma compose_subst_snd:
  forall (C: Category)(X Y Z: C)(f: X --> Y)(g g': Y --> Z),
    g == g' -> g•f == g'•f.
Proof.
  intros.
  apply compose_subst; [ equiv_refl | apply H ].
Qed.


Program Definition op_Category (C: Category): Category :=
  {| obj := obj C;
     arr X Y := arr Y X;
     compose X Y Z f g := f • g;
     id X := id |}.
Next Obligation.
  equiv_symm; apply compose_assoc.
Qed.
Next Obligation.
  apply compose_subst; auto.
Qed.
Next Obligation.
  apply id_cod.
Qed.
Next Obligation.
  apply id_dom.
Qed.
Notation "C ^^op" := (op_Category C) (at level 5, left associativity).


Section CategoryProperties.
  Context (C: Category).

  Definition mono {X Y: C}(f: X --> Y) :=
    forall (Z: C)(g h: Y --> Z),
      g•f == h•f -> g == h.
  
  Definition epi {X Y: C}(f: X --> Y) :=
    forall (U: C)(g h: U --> X),
      f•g == f•h -> g == h.
  
  Definition iso {X Y: C}(f: X --> Y)(g: Y --> X) :=
    g•f == id /\ f•g == id.

  Definition Iso (X Y: C) :=
    exists (f: X --> Y)(g: Y --> X), iso f g.
  Notation "X ≃ Y" := (Iso X Y) (at level 70, no associativity).
  

  Class Initial (I: C) :=
    { initial_arr: forall (X: C), I --> X;
      initiality:
        forall (X: C)(f: I --> X), initial_arr X == f }.

  Class Terminal (T: C) :=
    { terminal_arr: forall (X: C), X --> T;
      terminality:
        forall (X: C)(f: X --> T), terminal_arr X == f }.

  Structure InitialObj :=
    make_Initial
    { init_obj:> C;
      init_initiality:> Initial init_obj }.

  Structure TerminalObj :=
    make_Terminal
    { term_obj:> C;
      term_terminality:> Terminal term_obj }.

  Structure NullObj :=
    make_Null
    { null_obj:> C;
      null_initiality:> Initial null_obj;
      null_terminality:> Terminal null_obj }.
  
  Class Product (X Y XY: C) :=
    { proj_X: XY --> X;
      proj_Y: XY --> Y;
      
      product_arr (Q: C)(f: Q --> X)(g: Q --> Y): Q --> XY;
      
      product_arr_property_X:
        forall (Q: C)(f: Q --> X)(g: Q --> Y),
          proj_X • (product_arr f g) == f;

      product_arr_property_Y:
        forall (Q: C)(f: Q --> X)(g: Q --> Y),
          proj_Y • (product_arr f g) == g;

      product_arr_universality:
        forall (Q: C)(f: Q --> X)(g: Q --> Y)(h: Q --> XY),
          proj_X • h == f -> proj_Y • h == g ->
          product_arr f g == h }.

  Structure ProductObj (X Y: C) :=
    make_Product
    { product:> C;
      product_spec:> Product X Y product }.

  Class CoProduct (X Y XY: C) :=
    { in_X: X --> XY;
      in_Y: Y --> XY;
      
      coproduct_arr (Q: C)(f: X --> Q)(g: Y --> Q): XY --> Q;
      
      coproduct_arr_property_X:
        forall (Q: C)(f: X --> Q)(g: Y --> Q),
          (coproduct_arr f g) • in_X == f;

      coproduct_arr_property_Y:
        forall (Q: C)(f: X --> Q)(g: Y --> Q),
          (coproduct_arr f g) • in_Y == g;

      coproduct_arr_universality:
        forall (Q: C)(f: X --> Q)(g: Y --> Q)(h: XY --> Q),
          h • in_X == f -> h • in_Y == g ->
          coproduct_arr f g == h }.

  Structure CoProductObj (X Y: C) :=
    make_CoProduct
    { coproduct:> C;
      coproduct_spec:> CoProduct X Y coproduct }.

End CategoryProperties.


Lemma Initial_unique_up_to_iso:
  forall (C: Category)(I I': C),
    Initial I -> Initial I' ->
    Iso I I'.
Proof.
  intros C I I' HInit HInit'.
  unfold Iso, iso.
  exists (initial_arr I'), (initial_arr I).
  split.
  - apply transitivity with (initial_arr I); auto.
    + apply symmetry.
      apply initiality.
    + apply initiality.
  - apply transitivity with (initial_arr I'); auto.
    + apply symmetry.
      apply initiality.
    + apply initiality.
Qed.

Lemma Terminal_unique_up_to_iso:
  forall (C: Category)(T T': C),
    Terminal T -> Terminal T' ->
    Iso T T'.
Proof.
  intros C T T' Hterm Hterm'.
  unfold Iso, iso.
  exists (terminal_arr T). 
  exists (terminal_arr T').
  split.
  - apply transitivity with (terminal_arr T).
    + apply symmetry.
      apply terminality.
    + apply terminality.
  - apply transitivity with (terminal_arr T').
    + apply symmetry.
      apply terminality.
    + apply terminality.
Qed.

Program Canonical Structure Initial_to_Terminal
        {C: Category}(I: InitialObj C): TerminalObj (C ^^op) :=
  make_Terminal
    {| terminal_arr := initial_arr (Initial:=I) |}.
Next Obligation.
  apply initiality.
Qed.

(*
Program Instance Initial_as_Terminal
        {C: Category}(I:C)(Init: Initial I): Terminal (C:=C ^^op) I :=
  { terminal_arr X := initial_arr (C:=C) X }.
Next Obligation.
  apply initiality.
Qed.

Program Canonical Structure Initial_to_Terminal
        {C: Category}(I: InitialObj C): TerminalObj (C ^^op) :=
  {| term_obj := I |}.
Next Obligation.
  apply Initial_as_Terminal, init_initiality.
Qed.

*)


Program Canonical Structure Terminal_to_Initial
        {C: Category}(T: TerminalObj C): InitialObj (C ^^op) :=
  make_Initial
    {| initial_arr := terminal_arr (Terminal:=T) |}.
Next Obligation.
  apply terminality.
Qed.

(*
Program Instance  Terminal_as_Initial
        {C: Category}{T: C}(Term: Terminal T): Initial (C:=C ^^op) T :=
  { initial_arr X := terminal_arr (C:=C) X }.
Next Obligation.
  apply terminality.
Qed.

Program Canonical Structure Terminal_to_Initial
        {C: Category}(T: TerminalObj C): InitialObj (C ^^op) :=
  {| init_obj := T |}.
Next Obligation.
  apply Terminal_as_Initial, term_terminality.
Qed.
*)

Program Canonical Structure Product_to_CoProduct
        {C: Category}{X Y: C}(prod: ProductObj X Y)
: CoProductObj (C:=C^^op) X Y :=
  make_CoProduct
    {| in_X := proj_X (C:=C) (Product:=prod);
       in_Y := proj_Y (C:=C) (Product:=prod);
       coproduct_arr := product_arr (C:=C) (Product:=prod) |}.
Next Obligation.
  apply product_arr_property_X.
Qed.
Next Obligation.
  apply product_arr_property_Y.
Qed.
Next Obligation.
  apply product_arr_universality; auto.
Qed.


(*
Program Instance Product_as_CoProduct
        {C: Category}{X Y XY: C}(prod: Product X Y XY)
: CoProduct (C:=C ^^op) X Y XY :=
  { in_X := proj_X (C:=C) (Product:=prod);
    in_Y := proj_Y (C:=C) (Product:=prod);
    coproduct_arr := product_arr (C:=C) (Product:=prod) }.
Next Obligation.
  apply product_arr_property_X.
Qed.
Next Obligation.
  apply product_arr_property_Y.
Qed.
Next Obligation.
  apply product_arr_universality; auto.
Qed.

Program Canonical Structure Product_to_CoProduct
        {C: Category}{X Y: C}(XY: ProductObj X Y)
: @CoProductObj (C^^op) X Y :=
  {| coproduct := product (C:=C) XY |}.
Next Obligation.
  apply Product_as_CoProduct, product_spec.
Qed.
*)

Program Canonical Structure CoProduct_to_Product
        {C: Category}{X Y: C}(coprod: CoProductObj X Y)
: ProductObj (C:=C^^op) X Y :=
  make_Product
    {| proj_X := in_X (C:=C) (CoProduct:=coprod);
       proj_Y := in_Y (C:=C) (CoProduct:=coprod);
       product_arr := coproduct_arr (C:=C) (CoProduct:=coprod) |}.
Next Obligation.
  apply coproduct_arr_property_X.
Qed.
Next Obligation.
  apply coproduct_arr_property_Y.
Qed.
Next Obligation.
  apply coproduct_arr_universality; auto.
Qed.


(*
Program Instance CoProduct_as_Product
        {C: Category}{X Y XY: C}(coprod: CoProduct X Y XY)
: @Product (C ^^op) X Y XY :=
  { proj_X := in_X (C:=C) (CoProduct:=coprod);
    proj_Y := in_Y (C:=C) (CoProduct:=coprod);
    product_arr := coproduct_arr (CoProduct:=coprod) }.
Next Obligation.
  apply coproduct_arr_property_X.
Qed.
Next Obligation.
  apply coproduct_arr_property_Y.
Qed.
Next Obligation.
  apply coproduct_arr_universality; auto.
Qed.

Program Canonical Structure CoProduct_to_Product
        {C: Category}{X Y: C}(XY: CoProductObj X Y)
: @ProductObj (C^^op) X Y :=
  {| product := coproduct (C:=C) XY |}.
Next Obligation.
  apply CoProduct_as_Product, coproduct_spec.
Qed.
*)
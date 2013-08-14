
(*  *)
Require Import Utf8.

Set Implicit Arguments.

Module Equivalence.

  Definition relation (X: Type) := X -> X -> Prop.
  
  Section RelationProperties.
    Context {X: Type}(R: relation X).

    Class Reflexive: Prop :=
      { reflexive:
          forall x, R x x }.

    Class Symmetric: Prop :=
      { symmetric:
          forall x y, R x y -> R y x }.

    Class Transitive: Prop :=
      { transitive:
          forall x y z, R x y -> R y z -> R x z }.

    Class Equivalence: Prop :=
      { eq_refl:> Reflexive;
        eq_symm:> Symmetric;
        eq_trns:> Transitive }.

  End RelationProperties.

  Hint Unfold reflexive symmetric transitive.
  Hint Unfold eq_refl eq_symm eq_trns.
  Hint Resolve eq_refl eq_symm eq_trns.

  Section EquivalenceInstances.

    Program Instance eqEquiv (A: Type): Equivalence (@eq A).
    Next Obligation.
      - split; congruence.
    Qed.  
    Next Obligation.
      - split; congruence.
    Qed.  
    Next Obligation.
      - split; congruence.
    Qed.  

    Program Instance iffEquiv: Equivalence iff.
    Next Obligation.
      - split; tauto.
    Qed.
    Next Obligation.
      - split; tauto.
    Qed.
    Next Obligation.
      - split; tauto.
    Qed.

  End EquivalenceInstances.

End Equivalence.

Module Setoid.

  Import Equivalence.

  (* Definition of Setoid *)
  Class Setoid: Type :=
    { carrier: Type;
      equal: carrier -> carrier -> Prop;
      
      prf_equal_equiv: Equivalence equal }.
  Coercion carrier: Setoid >-> Sortclass.
  Notation "x == y" := (equal x y) (at level 80, no associativity).
  Hint Resolve prf_equal_equiv.

  Section SetoidInstances.

    Program Instance SetSetoid:Setoid :=
      { carrier := Set; equal := eq }.
    Next Obligation.
      apply eqEquiv.
    Qed.

    Program Instance FunctionSetoid (X Y: Set): Setoid :=
      { carrier := X -> Y;
        equal f g := forall x, f x = g x }.
    Next Obligation.
      split; split; congruence.
    Qed.
 
    Program Instance PropSetoid: Setoid :=
      { carrier := Prop; equal := iff }.
    Next Obligation.
      apply iffEquiv.
    Qed.

    Program Instance DataTypeSetoid (X: Set): Setoid :=
      { carrier := X; equal := eq }.
    Next Obligation.
      intro X; apply eqEquiv.
    Qed.

  End SetoidInstances.

  (* Morphism *)
  Class Morphism (S: Type) :=
    { fun_type (X Y: S): Setoid }.
  Notation "X ⟶ Y" := (fun_type X Y) (at level 60, right associativity).
  Class Composable {S: Type}(m: Morphism S) :=
    { compose {X Y Z: S}: (X ⟶ Y) -> (Y ⟶ Z) -> (X ⟶ Z) }.
  Notation "g ◦ f" := (compose f g) (at level 60, right associativity).
  Class Associative {S: Type}{m: Morphism S}(composable: Composable m) :=
    { compose_assoc:
        forall (X Y Z W: S)(f: X ⟶ Y)(g: Y ⟶ Z)(h: Z ⟶ W),
          (h◦g)◦f == h◦(g◦f) }.
  Class HasLeftId {S: Type}{m: Morphism S}(composable: Composable m) :=
    { lid {X: S}: X ⟶ X;
      left_lid_id:
        forall (X Y: S)(f: X ⟶ Y), f ◦ lid == f }.
  Class HasRightId {S: Type}{m: Morphism S}(composable: Composable m) :=
    { rid {X: S}: X ⟶ X;
      right_rid_id:
        forall (X Y: S)(f: X ⟶ Y), rid ◦ f == f }.
  Class HasId {S: Type}{m: Morphism S}(composable: Composable m) :=
    { id {X: S}: X ⟶ X;
      has_left_id :> HasLeftId composable;
      has_right_id :> HasRightId composable;

      eq_id_lid: forall (X: S), id (X:=X) == lid;
      eq_id_rid: forall (X: S), id (X:=X) == rid }.

  (* Definition of Map *)
  Class Map (X Y: Setoid): Type :=
    { ap: X -> Y;

      ap_preserve_eq:
        forall (x x': X), x == x' -> ap x == ap x' }.
  Coercion ap: Map >-> Funclass.
  Definition Map_eq {X Y: Setoid}(f g: Map X Y) := forall x: X, f x == g x.

  Program Instance MapSetoid (X Y: Setoid): Setoid :=
    { carrier := Map X Y; equal := Map_eq }.
  Next Obligation.
    intros X Y; split; split.
    - intros f x; apply eq_refl; auto.
    - intros f g Heq x; apply eq_symm; auto.
    - intros f g h Heq Heq' x; apply eq_trns with (g x); auto.
  Qed.

  Program Instance MapMorphism: Morphism Setoid :=
    { fun_type X Y := MapSetoid X Y }.
  
  Program Instance ComposeMap {X Y Z: Setoid}(f: X⟶Y)(g: Y⟶Z): Map X Z :=
    { ap := fun x => g (f x) }.
  Next Obligation.
    intros.
    repeat apply ap_preserve_eq; auto.
  Qed.

  Hint Unfold Map_eq.

  Program Instance ComposableMapMorphism: Composable MapMorphism :=
    { compose X Y Z f g := ComposeMap f g }.
  Program Instance AssociativeMapMorphism
  : Associative ComposableMapMorphism.
  Next Obligation.
    simpl; intros.
    unfold Map_eq; simpl.
    intro; apply eq_refl; auto.
  Qed.

  Program Instance IdMap (X: Setoid): Map X X :=
    { ap := fun x => x }.
  Next Obligation.
    auto.
  Qed.

  Program Instance MapHasLeftId: HasLeftId ComposableMapMorphism :=
    { lid X := IdMap X }.
  Next Obligation.
    simpl; unfold Map_eq; simpl.
    intros; apply eq_refl; auto.
  Qed.
  Program Instance MapHasRightId: HasRightId ComposableMapMorphism :=
    { rid X := IdMap X }.
  Next Obligation.
    simpl; unfold Map_eq; simpl.
    intros; apply eq_refl; auto.
  Qed.
  Program Instance MapHasId: HasId ComposableMapMorphism :=
    { id X := IdMap X }.
  Next Obligation.
    simpl; unfold Map_eq; simpl.
    intros; apply eq_refl; auto.
  Qed.
  Next Obligation.
    simpl; unfold Map_eq; simpl.
    intros; apply eq_refl; auto.
  Qed.

End Setoid.

Module Category.
  
  Import Equivalence Setoid.

  Class Category :=
    { obj: Type;
      arr:> Morphism obj;

      arr_composable:> Composable arr;
      arr_has_id:> HasId arr_composable;
      arr_associative:> Associative arr_composable }.
  Coercion obj: Category >-> Sortclass.
  
  Program Instance FunctionMorphism: Morphism Set :=
    { fun_type X Y := FunctionSetoid X Y }.
  Program Instance ComposableFunctionMorphism: Composable FunctionMorphism :=
    { compose X Y Z f g := fun x => g (f x) }.
  Program Instance: Associative ComposableFunctionMorphism.
  Next Obligation.
    simpl; auto.
  Qed.
  Program Instance: HasLeftId ComposableFunctionMorphism :=
    { lid X := fun x: X => x }.
  Next Obligation.
    simpl; auto.
  Qed.
  Program Instance: HasRightId ComposableFunctionMorphism :=
    { rid X := fun x: X => x }.
  Next Obligation.
    simpl; auto.
  Qed.
  Program Instance: HasId ComposableFunctionMorphism :=
    { id X := fun x: X => x }.
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    simpl; auto.
  Qed.

  Program Instance Sets: Category :=
    { obj := Set;
      arr := FunctionMorphism }.

  Program Instance op_Morphism {S: Type}(m: Morphism S): Morphism S :=
    { fun_type X Y := Y ⟶ X }.
  Program Instance op_Composable 
          {S: Type}{m: Morphism S}(composable: Composable m)
  : Composable (op_Morphism m) :=
    { compose X Y Z := fun (f: Y ⟶ X)(g: Z ⟶ Y) => (compose (m:=m) g f) }.
  Program Instance op_Associative
          {S: Type}{m: Morphism S}{composable: Composable m}
          (associative: Associative composable)
  : Associative (op_Composable composable).
  Next Obligation.
    intros S m Hcomposable Hassociative X Y Z W f g h.
    simpl.
    apply eq_symm; auto.
    apply compose_assoc.
  Qed.
  Program Instance op_HasLeftId
          S (m: Morphism S)(c: Composable m)(hasrid: HasRightId c)
  : HasLeftId (op_Composable c) :=
    { lid X := rid (m:=m) (X:=X) }.
  Next Obligation.
    intros S m c hasrid X Y f.
    simpl in *.
    apply right_rid_id.
  Qed.
  Program Instance op_HasRightId
          S (m: Morphism S)(c: Composable m)(haslid: HasLeftId c)
  : HasRightId (op_Composable c) :=
    { rid X := lid (m:=m) (X:=X) }.
  Next Obligation.
    intros S m c haslid X Y f.
    simpl in *.
    apply left_lid_id.
  Qed.
  Program Instance op_HasId
          S (m: Morphism S)(c: Composable m)(hasid: HasId c)
  : HasId (op_Composable c) :=
    { id X := id (m:=m) (X:=X) }.
  Next Obligation.
    intros; simpl.
    apply eq_id_rid.
  Qed.
  Next Obligation.
    intros; simpl.
    apply eq_id_lid.
  Qed.
  
  Program Instance op_Category (C: Category): Category :=
    { obj := obj ; arr := op_Morphism arr }.
  Notation "C ^^op" := (op_Category C) (at level 5, left associativity).

  Section CategoryProperties.
    Variables (C: Category).

    Definition mono {X Y: C}(f: X ⟶ Y) :=
      forall (Z: C)(g h: Y ⟶ Z),
        g◦f == h◦f -> g == h.
    
    Definition epi {X Y: C}(f: X ⟶ Y) :=
      forall (U: C)(g h: U ⟶ X),
        f◦g == f◦h -> g == h.
    
    Definition iso {X Y: C}(f: X ⟶ Y)(g: Y ⟶ X) :=
      g◦f == id ∧ f◦g == id.

    Definition Iso (X Y: C) :=
      exists (f: X ⟶ Y)(g: Y ⟶ X), iso f g.
    Notation "X ≃ Y" := (Iso X Y) (at level 70, no associativity).
    
    Definition initial (I: C)(In: forall X:C, I ⟶ X) :=
      forall (X: C)(f: I ⟶ X), In X == f.

    Definition terminal (T: C)(Te: forall X: C, X ⟶ T) :=
      forall (X: C)(f: X ⟶ T), Te X == f.

    Definition null (Z: C) ZIn ZTe := initial Z ZIn ∧ terminal Z ZTe.

  End CategoryProperties.

  Lemma initial_unique_up_to_iso:
    forall C I In I' In', 
      initial C I In -> initial C I' In' -> Iso C I I'.
  Proof.
    intros C I In I' In' Hinit Hinit'.
    unfold Iso, iso.
    unfold initial in *.
    generalize (Hinit I id) (Hinit' I' id);
      intros Hin Hin'.
    exists (In I'), (In' I).
    split.
    - apply eq_trns with (In I); auto.
      apply eq_symm; auto.
    - apply eq_trns with (In' I'); auto.
      apply eq_symm; auto.
  Qed.

  Lemma terminal_unique_up_to_iso:
    forall C T Te T' Te',
      terminal C T Te -> terminal C T' Te' -> Iso C T T'.
  Proof.
    intros C T Te T' Te' Hterm Hterm'.
    unfold Iso, iso, terminal in *.
    generalize (Hterm T id) (Hterm' T' id);
      intros Hte Hte'.
    exists (Te' T), (Te T'); split.
    - apply eq_trns with (Te T); auto.
      apply eq_symm; auto.
    - apply eq_trns with (Te' T'); auto.
      apply eq_symm; auto.
  Qed.

  Lemma initial_dual_terminal:
    forall (C: Category) I In,
      initial C I In -> terminal C ^^op I In.
  Proof.
    unfold initial, terminal.
    intros C I In Hinit X f.
    apply Hinit.
  Qed.

  Lemma terminal_dual_initial:
    forall (C: Category) T Te,
      terminal C T Te -> initial C ^^op T Te.
  Proof.
    unfold initial, terminal.
    intros C T Te Hterm X f.
    apply Hterm.
  Qed.

  
  Program Instance SetoidCategory: Category :=
    { obj := Setoid;
      arr := MapMorphism }.

  Print arr.
  Class Functor (C D: Category): Type :=
    { fobj: C -> D;
      fmap {X Y: C}(f: X ⟶ Y): fobj X ⟶ fobj Y;
      
      fmap_id:
        forall (X: C), fmap id == id (X:=fobj X);

      fmap_compose:
        forall (X Y Z: C)(f: X ⟶ Y)(g: Y ⟶ Z),
          fmap g◦fmap f == fmap (g◦f) }.
  Coercion fobj: Functor >-> Funclass.
  Notation "F .[ f ]" := (@fmap _ _ F _ _ f) (at level 55, left associativity).

  Class Natrans {C D: Category}(F G: Functor C D) :=
    { natrans {X: C}: F X ⟶ G X;
      naturality:
        forall (X Y: C)(f: X ⟶ Y),
          natrans ◦ fmap f == fmap f ◦ natrans }.


  Require Import List.
  Program Instance ListFunctor: Functor Sets Sets :=
    { fobj X := list X;
      fmap X Y f := map f }.
  Next Obligation.
    apply map_id.
  Qed.
  Next Obligation.
    apply map_map.
  Qed.
    

  Inductive tree (A: Set) :=
  | leaf (a: A) | node (l r: tree A).
  Fixpoint map_tree {A B: Set}(f: A -> B)(t: tree A): tree B :=
    match t with 
      | leaf a => leaf (f a)
      | node l r => node (map_tree f l) (map_tree f r)
    end.

  Lemma map_tree_id:
    forall (A: Set)(t: tree A), map_tree id t = t.
  Proof.
    induction t as [ a | l IHl r IHr ];
    simpl in *; congruence.
  Qed.
  
  Lemma map_tree_map_tree:
    forall (A B C: Set)(f: A -> B)(g: B -> C)(t: tree A),
      map_tree g (map_tree f t) = map_tree (fun x => g (f x)) t.
  Proof.
    induction t as [ a | l IHl r IHr]; simpl in *;
    congruence.
  Qed.


  Program Instance TreeFunctor: Functor Sets Sets :=
    { fobj X := tree X;
      fmap X Y f := map_tree f }.
  Next Obligation.
    apply map_tree_id.
  Qed.
  Next Obligation.
    apply map_tree_map_tree.
  Qed.

  
  Fixpoint flatten {A: Set}(t: tree A): list A :=
    match t with
      | leaf a => cons a nil
      | node l r => app (flatten l) (flatten r)
    end.

  Program Instance flatten_natrans: Natrans TreeFunctor ListFunctor :=
    { natrans X := flatten (A:=X) }.
  Next Obligation.
    induction x as [a | l IHl r IHr]; simpl; auto.
    rewrite map_app.
    congruence.
  Qed.


End Category.
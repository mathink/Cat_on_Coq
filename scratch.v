
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
      
      prf_equal_equiv:> Equivalence equal }.
  Coercion carrier: Setoid >-> Sortclass.
  Notation "x == y" := (equal x y) (at level 80, no associativity).
  Hint Unfold prf_equal_equiv.
  Hint Resolve prf_equal_equiv.

  Section SetoidInstances.

    Program Instance SetSetoid:Setoid :=
      { carrier := Set; equal := eq }.
    Next Obligation.
      apply eqEquiv.
    Qed.

    Program Instance FunctionSetoid (X Y: Set): Setoid :=
      { carrier := X -> Y : Set;
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
    { fun_type (X Y: S):> Setoid }.
  Notation "X ⟶ Y" := (fun_type X Y) (at level 60, right associativity).
  Class Composable {S: Type}(m: Morphism S) :=
    { compose {X Y Z: S}: (X ⟶ Y) -> (Y ⟶ Z) -> (X ⟶ Z);
      compose_subst:
        forall {X Y Z: S}(f f': X ⟶ Y)(g g': Y ⟶ Z),
          f == f' -> g == g' -> compose f g == compose f' g' }.
  Notation "g ◦ f" := (compose f g) (at level 60, right associativity).
  Lemma compose_subst_fst:
    forall (S: Type)(m: Morphism S)(c: Composable m)
       {X Y Z: S}(f f': X ⟶ Y)(g: Y ⟶ Z),
      f == f' -> compose f g == compose f' g.
  Proof.
    intros; apply compose_subst; [ assumption | apply eq_refl; auto ].
  Qed.
  Lemma compose_subst_snd:
    forall (S: Type)(m: Morphism S)(c: Composable m)
       {X Y Z: S}(f: X ⟶ Y)(g g': Y ⟶ Z),
      g == g' -> compose f g == compose f g'.
  Proof.
    intros; apply compose_subst; [ apply eq_refl; auto | assumption ].
  Qed.

  Class Associative {S: Type}{m: Morphism S}(composable: Composable m) :=
    { compose_assoc:
        forall (X Y Z W: S)(f: X ⟶ Y)(g: Y ⟶ Z)(h: Z ⟶ W),
          (h◦g)◦f == h◦(g◦f) }.
  Class HasLeftId {S: Type}{m: Morphism S}(composable: Composable m) :=
    { lid {X: S}: X ⟶ X;
      lid_left_id:
        forall (X Y: S)(f: X ⟶ Y), f ◦ lid == f }.
  Class HasRightId {S: Type}{m: Morphism S}(composable: Composable m) :=
    { rid {X: S}: X ⟶ X;
      rid_right_id:
        forall (X Y: S)(f: X ⟶ Y), rid ◦ f == f }.
  Class HasId {S: Type}{m: Morphism S}(composable: Composable m) :=
    { id {X: S}: X ⟶ X;
      has_left_id :> HasLeftId composable;
      has_right_id :> HasRightId composable;

      eq_id_lid: forall (X: S), id (X:=X) == lid;
      eq_id_rid: forall (X: S), id (X:=X) == rid }.
  Lemma id_left:
    forall {S: Type}{m: Morphism S}{c: Composable m}(hasId: HasId c)
       (X Y: S)(f: X ⟶ Y),
      f ◦ id == f.
  Proof.
    intros.
    apply eq_trns with (f◦lid);
      [ auto | apply compose_subst_fst; apply eq_id_lid | apply lid_left_id ].
  Qed.
  Lemma id_right:
    forall {S: Type}{m: Morphism S}{c: Composable m}(hasId: HasId c)
       (X Y: S)(f: X ⟶ Y),
      id ◦ f == f.
  Proof.
    intros.
    apply eq_trns with (rid ◦ f);
      [ auto | apply compose_subst_snd; apply eq_id_rid | apply rid_right_id ].
  Qed.

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
  Next Obligation.
    simpl; unfold Map_eq; simpl; auto.
    intros.
    apply eq_trns with (g (f' x)); auto.
    apply ap_preserve_eq.
    apply H.
  Qed.

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
  Next Obligation.
    simpl.
    congruence.
  Qed.
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

  Program Instance Setoids: Category :=
    { obj := Setoid;
      arr := MapMorphism }.
  

  Program Instance op_Morphism {S: Type}(m: Morphism S): Morphism S :=
    { fun_type X Y := Y ⟶ X }.
  Program Instance op_Composable 
          {S: Type}{m: Morphism S}(composable: Composable m)
  : Composable (op_Morphism m) :=
    { compose X Y Z := fun (f: Y ⟶ X)(g: Z ⟶ Y) => (compose (m:=m) g f) }.
  Next Obligation.
    simpl.
    intros.
    apply compose_subst; assumption.
  Qed.
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
    apply rid_right_id.
  Qed.
  Program Instance op_HasRightId
          S (m: Morphism S)(c: Composable m)(haslid: HasLeftId c)
  : HasRightId (op_Composable c) :=
    { rid X := lid (m:=m) (X:=X) }.
  Next Obligation.
    intros S m c haslid X Y f.
    simpl in *.
    apply lid_left_id.
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

End Category.

Module Functor.

  Import Equivalence Setoid Category.

  Class Functor (C D: Category): Type :=
    { fobj: C -> D;
      fmap {X Y: C}: (X ⟶ Y) ⟶ (fobj X ⟶ fobj Y);
      
      fmap_id:
        forall (X: C), fmap id == id (X:=fobj X);

      fmap_compose:
        forall (X Y Z: C)(f: X ⟶ Y)(g: Y ⟶ Z),
          fmap g◦fmap f == fmap (g◦f) }.
  Coercion fobj: Functor >-> Funclass.

  Class contravariantFunctor (C D: Category): Type :=
    { op_fobj: C -> D;
      op_fmap {X Y: C}: (X ⟶ Y) ⟶ (op_fobj Y ⟶ op_fobj X);
      
      op_fmap_id:
        forall (X: C), op_fmap id == id (X:=op_fobj X);

      op_fmap_compose:
        forall (X Y Z: C)(f: X ⟶ Y)(g: Y ⟶ Z),
          op_fmap f◦op_fmap g == op_fmap (g◦f) }.
  Coercion op_fobj: contravariantFunctor >-> Funclass.

  Program Instance contFunctor_Functor {C D: Category}(opF: contravariantFunctor C D)
  : Functor (op_Category C) D :=
    { fobj X := op_fobj (contravariantFunctor:=opF) X;
      fmap X Y := op_fmap (contravariantFunctor:=opF) }.
  Next Obligation.
    intros.
    apply (op_fmap_id (C:=C)).
  Qed.
  Next Obligation.
    intros.
    apply (op_fmap_compose (C:=C)).
  Qed.

  Program Instance IdFunctor (C: Category): Functor C C :=
    { fobj X := X;
      fmap X Y := IdMap (X ⟶ Y) }.
  Next Obligation.
    simpl; intros; apply eq_refl; auto.
  Qed.
  Next Obligation.
    simpl; intros; apply eq_refl; auto.
  Qed.
  
  Program Instance ComposeFunctor {C D E: Category}
          (F: Functor C D)(G: Functor D E): Functor C E :=
    { fobj X := G (F X);
      fmap X Y := (fmap ◦ fmap) }.
  Next Obligation.
    intros.
    simpl.
    apply eq_trns with (fmap id); auto.
    - apply ap_preserve_eq; apply fmap_id.
    - apply fmap_id.
  Qed.
  Next Obligation.
    intros.
    simpl.
    eapply eq_trns; [ auto | apply fmap_compose | ].
    apply ap_preserve_eq; apply fmap_compose.
  Qed.

  Program Instance op_Functor C D (F: Functor C D)
  : Functor C ^^op D ^^op :=
    { fobj X := F X ; fmap X Y := fmap (Functor:=F) }.
  Next Obligation.
    intros.
    apply (fmap_id (Functor:=F)).
  Qed.
  Next Obligation.
    intros.
    apply (fmap_compose (Functor:=F)).
  Qed.


  Program Instance HomFunctor_fmap
          (C: Category)(X: C){Y Y': C}(g: Y ⟶ Y')
  : Map (X ⟶ Y) (X ⟶ Y') :=
    { ap f := compose f g }.
  Next Obligation.
    intros.
    apply compose_subst_fst; auto.
  Qed.

  Program Instance HomFunctor_fmap_Map
          (C: Category)(X: C){Y Y': C}
  : Map (Y ⟶ Y') (MapSetoid (X ⟶ Y) (X ⟶ Y')) :=
    { ap := HomFunctor_fmap C X }.
  Next Obligation.
    simpl; intros C X Y Y' g g' Heq f.
    unfold Map_eq; simpl.
    apply compose_subst_snd; auto.
  Qed.

  Program Instance opHomFunctor_fmap
          (C: Category)(Y: C){X X': C}(f: X ⟶ X')
  : Map (X' ⟶ Y) (X ⟶ Y) :=
    { ap := compose f }.
  Next Obligation.
    intros.
    apply compose_subst_snd; auto.
  Qed.

  Program Instance opHomFunctor_fmap_Map
          (C: Category)(Y: C){X X': C}
  : Map (X ⟶ X') (MapSetoid (X' ⟶ Y) (X ⟶ Y)) :=
    { ap := opHomFunctor_fmap C Y }.
  Next Obligation.
    simpl; intros C Y X X' f f' Heq g.
    unfold Map_eq; simpl.
    apply compose_subst_fst; auto.
  Qed.

  Program Instance HomFunctor
          (C: Category)(X: C): Functor C Setoids :=
    { fobj Y := X ⟶ Y ; fmap Y Z := HomFunctor_fmap_Map C X }.
  Next Obligation.
    intros C X Y f.
    simpl.
    apply id_right.
  Qed.
  Next Obligation.
    intros C X X' Y Z f g h.
    simpl; unfold Map_eq.
    apply eq_symm; auto; apply compose_assoc.
  Qed.

  Program Instance contravariantHomFunctor
          (C: Category)(Y: C): contravariantFunctor C Setoids :=
    { op_fobj X := X ⟶ Y ; op_fmap X X' := opHomFunctor_fmap_Map C Y }.
  Next Obligation.
    intros C Y X f.
    simpl.
    apply id_left.
  Qed.
  Next Obligation.
    intros C X Y Y' Z f g h.
    simpl; unfold Map_eq.
    apply compose_assoc.
  Qed.
  
  Program Instance opHomFunctor
          (C: Category)(Y: C): Functor (op_Category C) Setoids :=
    contFunctor_Functor (contravariantHomFunctor C Y).

End Functor.

Module Natrans.

  Import Equivalence Setoid Category Functor.

  Class Natrans {C D: Category}(F G: Functor C D) :=
    { natrans (X: C): F X ⟶ G X ;
      naturality:
        forall (X Y: C)(f: X ⟶ Y),
          (natrans Y) ◦ fmap f == fmap f ◦ (natrans X) }.
  Coercion natrans: Natrans >-> Funclass.


  Program Instance vCompose_Natrans
          {C D: Category}{F G H: Functor C D}
          (S: Natrans F G)(T: Natrans G H)
  : Natrans F H :=
    { natrans X := natrans X ◦ natrans X }.
  Next Obligation.
    intros.
    apply eq_trns with (T Y ◦ (S Y◦fmap f));
      [auto | apply compose_assoc | ].
    apply eq_trns with (T Y ◦ (fmap f ◦ S X));
      [auto | | ].
    - apply compose_subst_fst; apply naturality.
    - apply eq_trns with ((T Y ◦ fmap f) ◦ S X);
      [auto | apply eq_symm; auto; apply compose_assoc | ].
      apply eq_trns with ((fmap f ◦ T X) ◦ S X);
        [auto | | apply compose_assoc ].
      apply compose_subst_snd; apply naturality.
  Qed.

  Program Instance hCompose_Natrans
          {C D E: Category}{F G: Functor C D}{F' G': Functor D E}
          (S: Natrans F G)(T: Natrans F' G')
  : Natrans (ComposeFunctor F F') (ComposeFunctor G G') :=
    { natrans X := fmap (natrans X) ◦ natrans (fobj X) }.
  Next Obligation.
    intros.
    eapply eq_trns; [ auto | apply compose_subst_snd | ].
    apply eq_symm; auto.
    apply (naturality (Natrans:=T)).
    eapply eq_trns; [ auto | apply compose_assoc | ].
    apply eq_trns with (fmap f ◦ (T (G X) ◦ fmap (S X)));
      [ auto | | apply compose_subst_fst; apply (naturality (Natrans:=T)) ].
    eapply eq_trns; [ auto | | apply compose_assoc ].
    apply eq_symm; auto.
    eapply eq_trns; [ auto | apply compose_subst_snd | ].
    apply eq_symm; auto.
    apply (naturality (Natrans:=T)).
    eapply eq_trns; [ auto | apply compose_assoc | ].
    apply compose_subst_fst.
    eapply eq_trns; [ auto | apply (fmap_compose (Functor := F')) | ].
    apply eq_symm; auto.
    eapply eq_trns; [ auto | apply (fmap_compose (Functor := F')) | ].
    apply ap_preserve_eq.
    apply naturality.
  Qed.
  
End Natrans.

Module Adjunction.

  Import Equivalence Setoid Category Functor Natrans.

  Section AdjunctionDef.
    Context (C D: Category)(F: Functor C D)(G: Functor D C).
    
    (* Homset-Definition *)
    Class Adjunction_Hom :=
      { adj_phi (X: C)(Y: D): (F X ⟶ Y) -> (X ⟶ G Y);
        adj_phi_inv (X: C)(Y: D): (X ⟶ G Y) -> (F X ⟶ Y);

        adj_phi_subst:
          forall (X: C)(Y: D)(f f': F X ⟶ Y),
            f == f' -> adj_phi X Y f == adj_phi X Y f';
        adj_phi_inv_subst:
          forall (X: C)(Y: D)(g g': X ⟶ G Y),
            g == g' -> adj_phi_inv X Y g == adj_phi_inv X Y g';

        adj_phi_iso:
          forall (X: C)(Y: D)(f: F X ⟶ Y),
            adj_phi_inv X Y (adj_phi X Y f) == f;
        adj_phi_inv_iso:
          forall (X: C)(Y: D)(g: X ⟶ G Y),
            adj_phi X Y (adj_phi_inv X Y g) == g;
        
        adj_phi_naturality:
          forall (X Y: C)(Z W: D)(f: X ⟶ Y)(g: F Y ⟶ Z)(h: Z ⟶ W),
            adj_phi X W (h◦g◦fmap f) == fmap h ◦ adj_phi Y Z g ◦ f }.

    Lemma adj_phi_inv_naturality:
      forall (adj_h: Adjunction_Hom)
         (X Y: C)(Z W: D)(f: X ⟶ Y)(g: Y ⟶ G Z)(h: Z ⟶ W),
        adj_phi_inv X W (fmap h◦g◦ f) == h ◦ adj_phi_inv Y Z g ◦ fmap f.
    Proof.
      intros.
      apply eq_trns with
      (adj_phi_inv X W (fmap h ◦ (adj_phi Y Z (adj_phi_inv Y Z g)) ◦ f));
        [ auto | apply adj_phi_inv_subst | ].
      - apply compose_subst_fst;
        apply compose_subst_snd;
        apply eq_symm; auto; apply adj_phi_inv_iso.
      - eapply eq_trns; [ auto | | apply adj_phi_iso ].
        apply adj_phi_inv_subst.
        apply eq_symm; auto; apply adj_phi_naturality.
    Qed.
    

    (* Unit definition *)
    Class Adjunction_Unit :=
      { adj_unit:> Natrans (IdFunctor C) (ComposeFunctor F G);

        adj_dc {X: C}{Y: D}(f: X ⟶ G Y): F X ⟶ Y;
        adj_dc_property:
          forall (X: C)(Y: D)(f: X ⟶ G Y),
            fmap (adj_dc f) ◦ adj_unit X == f;
        adj_dc_uniqueness:
          forall (X: C)(Y: D)(f: X ⟶ G Y)(h: F X ⟶ Y),
            fmap h ◦ adj_unit X == f -> adj_dc f == h }.
    Lemma adj_dc_subst:
      forall (adj_u: Adjunction_Unit)(X: C)(Y: D)(f f': X ⟶ G Y),
        f == f' -> adj_dc f == adj_dc f'.
    Proof.
      intros.
      apply adj_dc_uniqueness.
      apply eq_trns with f';
        [ auto | apply adj_dc_property | apply eq_symm; auto; assumption ].
    Qed.
    
    (* Counit definition *)
    Class Adjunction_Counit :=
      { adj_counit:> Natrans (ComposeFunctor G F) (IdFunctor D);

        adj_cd {X: C}{Y: D}(f: F X ⟶ Y): X ⟶ G Y;
        adj_cd_property:
          forall (X: C)(Y: D)(f: F X ⟶ Y),
            adj_counit Y ◦ fmap (adj_cd f) == f;
        adj_cd_uniqueness:
          forall (X: C)(Y: D)(f: F X ⟶ Y)(h: X ⟶ G Y),
            adj_counit Y ◦ fmap h == f -> adj_cd f == h }.
    Lemma adj_cd_subst:
      forall (adj_c: Adjunction_Counit)(X: C)(Y: D)(f f': F X ⟶ Y),
        f == f' -> adj_cd f == adj_cd f'.
    Proof.
      intros.
      apply adj_cd_uniqueness.
      apply eq_trns with f';
        [ auto | apply adj_cd_property | apply eq_symm; auto; assumption ].
    Qed.

    
    (* Equivalency of Definitions *)
    (* 1. Unit -> Hom *)
    Program Instance Adj_Unit_Hom (adj_u: Adjunction_Unit): Adjunction_Hom :=
      { adj_phi X Y f := fmap f ◦ adj_unit X;
        adj_phi_inv X Y f := adj_dc f }.
    Next Obligation.
      intros.
      apply compose_subst_snd; apply ap_preserve_eq; assumption.
    Qed.  
    Next Obligation.
      apply adj_dc_subst.
    Qed.  
    Next Obligation.
      intros.
      apply adj_dc_uniqueness.
      apply eq_refl; auto.
    Qed.
    Next Obligation.
      intros.
      apply adj_dc_property.
    Qed.
    Next Obligation.
      intros.
      apply eq_trns with ((fmap h◦fmap g◦fmap (fmap f))◦adj_unit X);
        [ auto | apply compose_subst_snd | ].
      - apply eq_trns with (fmap h ◦ fmap (g ◦ fmap f));
          [ auto | apply eq_symm; auto; apply (fmap_compose (Functor:=G)) | ].
        apply compose_subst_fst;
          apply eq_symm; auto;
          apply (fmap_compose (Functor:=G)).
      - apply eq_symm; auto.
        apply eq_trns with (fmap h◦(fmap g◦fmap (fmap f))◦adj_unit X);
          [ auto 
          | apply compose_subst_fst
          | apply eq_symm; auto; apply compose_assoc ].
        eapply eq_trns; [ auto | apply compose_assoc | ].
        eapply eq_trns; [ auto | | apply eq_symm; auto; apply compose_assoc ].
        apply compose_subst_fst; apply (naturality (Natrans:=adj_unit)).
    Qed.


    (* 2. Hom -> Unit *)
    (* First, make Unit *)
    Program Instance Adj_Hom_Unit_Natrans (adj_h: Adjunction_Hom)
    : Natrans (IdFunctor C) (ComposeFunctor F G) :=
      { natrans X := adj_phi X (F X) id }.
    Next Obligation.
      intros.
      simpl.
      eapply eq_trns; [ auto | | apply id_left ].
      apply eq_trns with
      (fmap (Functor:=ComposeFunctor F G) f ◦ adj_phi X (F X) id ◦ id);
        [ auto | | apply eq_symm; auto; apply compose_assoc ].
      eapply eq_trns; [ auto | | apply adj_phi_naturality ].
      apply eq_symm; auto.
      eapply eq_trns; [ auto | apply adj_phi_subst | ].
      - apply eq_trns with (fmap f◦fmap id); [ auto | | ].
        + apply compose_subst_fst; apply id_right.
        + apply eq_trns with (fmap (f◦id));
          [ auto | apply fmap_compose | apply ap_preserve_eq; apply id_left ].
      - eapply eq_trns;
        [ auto | | apply id_right ].
        eapply eq_trns;
        [ auto | | apply compose_subst_snd; apply fmap_id ].
        eapply eq_trns;
        [ auto | | apply adj_phi_naturality ].
        apply adj_phi_subst.
        apply eq_symm; auto.
        apply eq_trns with (id◦fmap f);
          [ auto | apply id_right | apply id_right ].
    Qed.

    (* Then, prove. *)
    Program Instance Adj_Hom_Unit (adj_h: Adjunction_Hom): Adjunction_Unit :=
      { adj_unit := Adj_Hom_Unit_Natrans adj_h; 
        adj_dc := adj_phi_inv }.
    Next Obligation.
      intros.
      simpl in * .
      apply eq_symm; auto.
      eapply eq_trns;
        [ auto | | apply id_left ].
      eapply eq_trns;
        [ auto | | apply eq_symm; auto; apply compose_assoc ].
      eapply eq_trns;
        [ auto | | apply adj_phi_naturality  ].
      apply eq_symm; auto.
      eapply eq_trns;
        [ auto | apply adj_phi_subst | ].
      eapply eq_trns;
        [ auto | apply compose_subst_fst; apply id_right | ].
      eapply eq_trns;
        [ auto | apply compose_subst_fst; apply fmap_id | ].
      apply id_left.
      apply adj_phi_inv_iso.
    Qed.
    Next Obligation.
      intros; simpl in *.
      eapply eq_trns;
        [ auto | apply adj_phi_inv_subst; apply eq_symm; auto; apply H | ].
      eapply eq_trns;
        [ auto | apply adj_phi_inv_subst; apply eq_symm; auto; apply id_left | ].
      eapply eq_trns;
        [ auto | apply adj_phi_inv_subst; apply compose_assoc | ].
      eapply eq_trns;
        [ auto | apply adj_phi_inv_naturality | ].
      eapply eq_trns;
        [ auto | repeat apply compose_subst_fst; apply fmap_id | ].
      eapply eq_trns;
        [ auto | apply compose_subst_fst; apply id_left | ].
      eapply eq_trns;
        [ auto | apply compose_subst_fst; apply adj_phi_iso | ].
      apply id_left.
    Qed.
             
    
    (* 3. Counit -> Hom *)
    Program Instance Adj_Counit_Hom (adj_c: Adjunction_Counit): Adjunction_Hom :=
      { adj_phi X Y f := adj_cd f;
        adj_phi_inv X Y f := adj_counit Y ◦ fmap f }.
    Next Obligation.
      apply adj_cd_subst.
    Qed.
    Next Obligation.
      intros.
      apply compose_subst_fst; apply ap_preserve_eq; assumption.
    Qed.
    Next Obligation.
      intros.
      apply adj_cd_property.
    Qed.
    Next Obligation.
      intros.
      apply adj_cd_uniqueness.
      apply eq_refl; auto.
    Qed.
    Next Obligation.
      simpl.
      intros.
      eapply eq_trns;
        [ auto | apply adj_cd_uniqueness | apply compose_assoc ].
      eapply eq_trns;
        [ auto 
        | apply compose_subst_fst; apply eq_symm; auto;
          apply fmap_compose
        | ].
      eapply eq_trns;
        [ auto | | apply compose_assoc ].
      eapply eq_trns;
        [ auto | apply eq_symm; auto; apply compose_assoc | ].
      apply compose_subst_snd.
      eapply eq_trns;
        [ auto | apply compose_subst_fst;
                 apply eq_symm; auto; apply fmap_compose | ].
      eapply eq_trns;
        [ auto | apply eq_symm; auto; apply compose_assoc | ].
      eapply eq_trns;
        [ auto | apply compose_subst_snd | ].
      apply (naturality (Natrans:=adj_counit)).
      simpl.
      eapply eq_trns;
        [ auto | apply compose_assoc | ].
      apply compose_subst_fst; apply adj_cd_property.
    Qed.
      
    
    (* 4. Hom -> Counit *)
    (* First, make Counit *)
    Program Instance Adj_Hom_Counit_Natrans (adj_h: Adjunction_Hom)
    : Natrans (ComposeFunctor G F) (IdFunctor D) :=
      { natrans X := adj_phi_inv (G X) X id }.
    Next Obligation.
      simpl; intros.
      eapply eq_trns;
        [ auto | | apply id_left ].
      eapply eq_trns;
        [ auto | | apply compose_subst_fst; apply fmap_id ].
      eapply eq_trns;
        [ auto | | apply eq_symm; auto; apply compose_assoc ].
      eapply eq_trns;
        [ auto | | apply adj_phi_inv_naturality ].
      apply eq_symm; auto.
      eapply eq_trns;
        [ auto | | apply id_right ].
      eapply eq_trns;
        [ auto | | apply adj_phi_inv_naturality ].
      apply adj_phi_inv_subst.
      eapply eq_trns;
        [ auto | apply eq_symm; auto; apply compose_assoc | ].
      eapply eq_trns; [ auto | apply id_left | ].
      eapply eq_trns; [ auto | apply id_left | ].
      apply eq_symm; auto.
      eapply eq_trns; [ auto | apply compose_subst_snd; apply fmap_id | ].
      eapply eq_trns; [ auto | apply id_right | ].
      eapply eq_trns; [ auto | apply id_right | ].
      apply eq_refl; auto.
    Qed.
      
    (* Then, prove. *)
    Program Instance Adj_Hom_Counit (adj_h: Adjunction_Hom): Adjunction_Counit :=
      { adj_counit := Adj_Hom_Counit_Natrans adj_h; 
        adj_cd := adj_phi }.
    Next Obligation.
      simpl in *; intros.
      eapply eq_trns;
        [ auto | apply eq_symm; auto; apply id_right | ].
      eapply eq_trns;
        [ auto | apply eq_symm; auto; apply adj_phi_inv_naturality | ].
      eapply eq_trns;
        [ auto | | apply adj_phi_iso ].
      apply adj_phi_inv_subst.
      eapply eq_trns;
        [ auto | apply compose_subst_snd; apply fmap_id | ].
      eapply eq_trns; [ auto | apply id_right | ].
      eapply eq_trns; [ auto | apply id_right | ].
      apply eq_refl; auto.
    Qed.
    Next Obligation.
      simpl; intros.
      eapply eq_trns;
        [ auto | apply adj_phi_subst; apply eq_symm; auto; apply H | ].
      eapply eq_trns;
        [ auto | apply adj_phi_subst; apply eq_symm; auto; apply id_right | ].
      eapply eq_trns;
        [ auto | apply adj_phi_naturality | ].
      eapply eq_trns;
        [ auto | apply eq_symm; auto; apply compose_assoc | ].
      eapply eq_trns;
        [ auto | apply compose_subst_snd | apply id_right ].
      eapply eq_trns;
        [ auto | apply compose_subst_snd; apply fmap_id | ].
      eapply eq_trns;
        [ auto | apply id_right | ].
      apply adj_phi_inv_iso.
    Qed.
      
    
    (*
       以下，直接構成しようと試みるもうまく行かなかったため，
       とっても妥協しての定義である．
     *)
    (* 5. Unit -> Counit *)
    Program Instance Adj_Unit_Counit (adj_u: Adjunction_Unit)
    : Adjunction_Counit := Adj_Hom_Counit (Adj_Unit_Hom adj_u).

    (* 6. Counit -> Unit *)
    Program Instance Adj_Counit_Unit (adj_c: Adjunction_Counit)
    : Adjunction_Unit := Adj_Hom_Unit (Adj_Counit_Hom adj_c).

  End AdjunctionDef.


  Program Instance ADJ_phi_Setoid
          (C D: Category)(F: Functor C D)(G: Functor D C)
          (adj: Adjunction_Hom F G)(X: C)(Y: D)
  : Map (F X ⟶ Y) (X ⟶ G Y) :=
    { ap f := adj_phi X Y f }.
  Next Obligation.
    intros.
    apply adj_phi_subst; assumption.
  Qed.

End Adjunction.


Module Monad.

  Import Equivalence Setoid Category Functor Natrans.

  Class Monad {C: Category}(T: Functor C C) :=
    { m_unit:> Natrans (IdFunctor C) T;
      m_join:> Natrans (ComposeFunctor T T) T;

      m_join_unit_T:
        forall (X: C),
          (m_join X) ◦ (m_unit (T X)) == id;
      m_join_T_unit:
        forall (X: C),
          (m_join X) ◦ fmap (m_unit X) == id;
      m_join_join:
        forall (X: C),
          (m_join X) ◦ (m_join (T X)) == (m_join X) ◦ fmap (m_join X) }.

  Class KT {C: Category}(T: C -> C) :=
    { ret {X: C}: X ⟶ T X;
      bind {X Y: C}: (X ⟶ T Y) -> (T X ⟶ T Y);
      
      bind_subst:
        forall {X Y: C}(f f': X ⟶ T Y),
          f == f' -> bind f == bind f';

      ret_left:
        forall (X: C),
          bind (ret (X:=X)) == id;
      ret_right:
        forall (X Y: C)(f: X ⟶ T Y),
          bind f ◦ ret == f;
      bind_assoc:
        forall (X Y Z: C)(f: X ⟶ T Y)(g: Y ⟶ T Z),
          bind g◦bind f == bind (bind g◦f) }.


  Program Instance MonadKT `(monad: Monad): KT fobj :=
    { ret X := m_unit X;
      bind X Y f := m_join Y ◦ fmap f }.
  Next Obligation.
    intros.
    apply compose_subst; [ | apply eq_refl; auto ].
    apply ap_preserve_eq.
    apply H.
  Qed.
  Next Obligation.
    intros.
    apply m_join_T_unit.
  Qed.
  Next Obligation.
    intros.
    apply eq_trns
    with (m_join Y ◦ fmap f ◦ m_unit X);
      [ auto | apply compose_assoc | ].
    apply eq_trns
    with (m_join Y ◦ (m_unit (T Y)) ◦ fmap f);
      [ auto | apply compose_subst | ].
    - apply eq_symm; auto. 
      apply naturality.
    - apply eq_refl; auto.
    - apply eq_trns
      with ((m_join Y ◦ m_unit (T Y)) ◦ fmap f);
      [ auto | apply eq_symm; auto;  apply compose_assoc | ].
      simpl.
      apply eq_trns 
      with (id ◦ f); [auto | apply compose_subst | ].
      + apply eq_refl; auto.
      + apply m_join_unit_T.
      + apply eq_trns with (rid ◦ f); auto.
        apply compose_subst; [ apply eq_refl; auto | apply eq_id_rid ].
        apply rid_right_id.
  Qed.
  Next Obligation.
    intros.
    apply eq_symm; auto.
    apply eq_trns
    with ((m_join Z ◦ m_join (T Z)) ◦ (fmap (fmap g) ◦ fmap f)); auto.
    - apply eq_symm; auto.
      eapply eq_trns; [ auto | apply compose_subst | ].
      + apply fmap_compose.
      + apply m_join_join.
      + apply eq_trns
        with ((m_join Z ◦ fmap (m_join Z)) ◦ fmap (fmap g) ◦ fmap f); auto.
        * apply compose_subst;
          [ apply eq_symm; auto; apply fmap_compose | apply eq_refl; auto ].
        * eapply eq_trns; [ auto | apply compose_assoc | ].
          apply compose_subst; [ | apply eq_refl; auto ].
          apply eq_symm; auto.
          eapply eq_trns; [ auto | apply eq_symm; auto; apply fmap_compose | ].
          eapply eq_trns; [ auto | | apply compose_assoc ].
          apply compose_subst;
            [ apply eq_refl; auto | apply eq_symm; auto; apply fmap_compose ].
    - apply eq_trns
      with (m_join Z ◦ (m_join (T Z)) ◦ fmap (fmap g) ◦ fmap f); auto.
      + eapply eq_trns; [ auto | apply compose_assoc | ].
        apply eq_refl; auto.
      + eapply eq_trns; [ auto | | apply eq_symm; auto; apply compose_assoc ].
        apply compose_subst; [ | apply eq_refl; auto ].
        eapply eq_trns; [ auto | | apply compose_assoc ].
        eapply eq_trns; [ auto | apply eq_symm; auto; apply compose_assoc | ].
        apply compose_subst; [ apply eq_refl; auto | ].
        change (m_join (T Z) ◦ fmap (Functor:=(ComposeFunctor T T)) g == fmap g ◦ m_join Y).
        eapply eq_trns; [ auto | apply naturality | ].
        apply eq_refl; auto.
  Qed.

  Program Instance KT_fmap_Map
          (C: Category)(T: C -> C)(kt: KT T)(X Y: C)
  : Map (X ⟶ Y)
        (T X ⟶ T Y) :=
    { ap f := bind (ret ◦ f) }.
  Next Obligation.
    intros.
    apply bind_subst.
    apply compose_subst; [ apply H | apply eq_refl; auto ].
  Qed.

  Program Instance KTFunctor {C: Category}{T: C -> C}(kt: KT T): Functor C C :=
    { fobj := T;
      fmap X Y := KT_fmap_Map C T kt X Y}.
  Next Obligation.
    intros.
    apply eq_trns with (bind ret); auto.
    - apply bind_subst.
      apply eq_trns with (ret ◦ lid); auto.
      + apply compose_subst; [ apply eq_id_lid | apply eq_refl; auto ].
      + apply lid_left_id.
    - apply ret_left.
  Qed.
  Next Obligation.
    intros.
    eapply eq_trns; [ auto | apply bind_assoc | ].
    apply bind_subst.
    eapply eq_trns; [ auto | | apply compose_assoc ].
    eapply eq_trns; [ auto | apply eq_symm; auto; apply compose_assoc | ].
    apply compose_subst; [ apply eq_refl; auto | apply ret_right ].
  Qed.

  Program Instance KTNatrans_unit
          {C: Category}{T: C -> C}(kt: KT T)
  : Natrans (IdFunctor C) (KTFunctor kt) :=
    { natrans X := ret }.
  Next Obligation.
    intros.
    apply eq_symm; auto; apply ret_right.
  Qed.

  Program Instance KTNatrans_join
          {C: Category}{T: C -> C}(kt: KT T)
  : Natrans (ComposeFunctor (KTFunctor kt) (KTFunctor kt)) (KTFunctor kt):=
    { natrans X := bind id }.
  Next Obligation.
    intros.
    eapply eq_trns; [ auto | apply (bind_assoc (KT:=kt))| ].
    eapply eq_trns;
      [ auto | | apply eq_symm; auto; apply (bind_assoc (KT:=kt)) ].
    apply (bind_subst (KT:=kt)).
    eapply eq_trns; [ auto | apply eq_symm; auto; apply compose_assoc | ].
    eapply eq_trns; [ auto | apply compose_subst | ].
    - apply eq_refl; auto.
    - apply ret_right.
    - apply eq_trns with (rid ◦ bind (ret ◦ f)); auto.
      + apply compose_subst; [ apply eq_refl; auto | ].
        apply eq_id_rid.
      + eapply eq_trns; [ auto | apply rid_right_id | ].
        apply eq_trns with (bind (ret ◦ f) ◦ lid); auto.
        * apply eq_symm; auto; apply lid_left_id.
        * apply compose_subst; [ | apply eq_refl; auto ].
          apply eq_symm; auto; apply eq_id_lid.
  Qed.

  Program Instance KTMonad
          {C: Category}{T: C -> C}(kt: KT T)
  : Monad (KTFunctor kt).
  Next Obligation.
    intros.
    apply ret_right.
  Qed.
  Next Obligation.
    intros.
    eapply eq_trns; [ auto | apply bind_assoc | ].
    eapply eq_trns; [ auto | apply bind_subst | ].
    apply eq_symm; auto; apply compose_assoc.
    eapply eq_trns; [ auto | apply bind_subst | ].
    apply compose_subst; [ apply eq_refl; auto | apply ret_right ].
    eapply eq_trns; [ auto | apply bind_subst | ].
    apply compose_subst; [ apply eq_refl; auto | apply eq_id_rid ].
    eapply eq_trns; [ auto | apply bind_subst | ].
    apply rid_right_id.
    apply ret_left.
  Qed.
  Next Obligation.
    intros.
    eapply eq_trns; [ auto | apply (bind_assoc (KT:=kt))| ].
    eapply eq_trns; [ auto | | apply eq_symm; auto; apply (bind_assoc (KT:=kt))].
    apply (bind_subst (KT:=kt)).
    eapply eq_trns; [ auto | apply compose_subst | ].
    apply eq_id_lid.
    apply eq_refl; auto.
    eapply eq_trns; [ auto | apply lid_left_id | ].
    eapply eq_trns; [ auto | | apply compose_assoc ].
    eapply eq_trns; [ auto | | apply compose_subst ].
    apply eq_symm; auto; apply rid_right_id.
    apply eq_refl; auto.
    apply eq_symm; auto.
    apply eq_trns with id; [auto | apply ret_right | apply eq_id_rid].
  Qed.

  
  Definition KTCompose {C: Category}{T: C -> C}(kt: KT T)
             (X Y Z: C)(f: X ⟶ T Y)(g: Y ⟶ T Z): X ⟶ T Z :=
    bind g ◦ f.
  Hint Unfold KTCompose.

  Program Instance KTMorphism
          {C: Category}{T: C -> C}(kt: KT T)
  : Morphism C :=
    { fun_type X Y := X ⟶ T Y }.

  Program Instance ComposableKTMorphism
          {C: Category}{T: C -> C}(kt: KT T)
  : Composable (KTMorphism kt) :=
    { compose X Y Z f g := KTCompose kt X Y Z f g }.
  Next Obligation.
    unfold KTCompose.
    intros.
    apply (compose_subst (Z:=T Z));
      [ assumption | apply bind_subst ; assumption ].
  Qed.
  Program Instance AssociativeKTMorphism
          {C: Category}{T: C -> C}(kt: KT T)
  : Associative (ComposableKTMorphism kt).
  Next Obligation.
    unfold KTCompose.
    intros.
    eapply eq_trns;
      [ auto | | apply (compose_assoc (Associative:=arr_associative))].
    apply (compose_subst (Z:=T W)); [ apply eq_refl; auto | ].
    apply eq_symm; auto.
    apply bind_assoc.
  Qed.
  Program Instance KTMorphismHasLeftId
          {C: Category}{T: C -> C}(kt: KT T)
  : HasLeftId (ComposableKTMorphism kt) :=
    { lid X := ret }.
  Next Obligation.
    unfold KTCompose.
    intros.
    apply ret_right.
  Qed.
  Program Instance KTMorphismHasRightId
          {C: Category}{T: C -> C}(kt: KT T)
  : HasRightId (ComposableKTMorphism kt) :=
    { rid X := ret }.
  Next Obligation.
    intros.
    unfold KTCompose.
    eapply eq_trns;
      [ auto | apply (compose_subst (Composable:=@arr_composable C))| ].
    - apply eq_refl; auto.
    - apply ret_left.
    - eapply eq_trns; auto; [ apply (compose_subst (Composable:=@arr_composable C))| ]. 
      + apply eq_refl; auto.
      + apply eq_id_rid.
      + apply (@rid_right_id _ (@arr C)).
  Qed.
  Program Instance KTMorphismHasId
          {C: Category}{T: C -> C}(kt: KT T)
  : HasId (ComposableKTMorphism kt) :=
    { id X := ret }.
  Next Obligation.
    intros.
    apply eq_refl; auto.
  Qed.
  Next Obligation.
    intros.
    apply eq_refl; auto.
  Qed.

  Program Instance KT_KleisliCategory
          {C: Category}{T: C -> C}(kt: KT T)
  : Category :=
    { obj := obj ; arr := KTMorphism kt }.

  Program Instance KleisliCategory
          {C: Category}{T: Functor C C}(m: Monad T)
  : Category := KT_KleisliCategory (MonadKT m).


End Monad.


Module Example.

  Import Equivalence Setoid Category Functor Natrans Adjunction Monad.

  Require Import List.

  Program Instance map_Map {X Y: Set}
  : Map (FunctionSetoid X Y)
        (FunctionSetoid (list X) (list Y)) :=
    { ap := @map X Y }.
  Next Obligation.
    induction x0 as [ | h t]; simpl in *; congruence.
  Qed.

  Program Instance ListFunctor: Functor Sets Sets :=
    { fobj X := list X;
      fmap X Y := map_Map }.
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
    induction t as [ a | l IHl r IHr ]; simpl in *; congruence.
  Qed.

  Lemma map_tree_map_tree:
    forall (A B C: Set)(f: A -> B)(g: B -> C)(t: tree A),
      map_tree g (map_tree f t) = map_tree (fun x => g (f x)) t.
  Proof.
    induction t as [ a | l IHl r IHr]; simpl in *; congruence.
  Qed.

  Program Instance map_tree_Map {X Y: Set}
  : Map (FunctionSetoid X Y)
        (FunctionSetoid (tree X) (tree Y)) :=
    { ap := @map_tree X Y }.
  Next Obligation.
    induction x0 as [ a | l IHl r IHr ]; simpl in *; congruence.
  Qed.

  Program Instance TreeFunctor: Functor Sets Sets :=
    { fobj X := tree X;
      fmap X Y := map_tree_Map }.
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




  Program Instance cons_a_nil_Natrans: Natrans (IdFunctor Sets) ListFunctor :=
    { natrans X := fun x => cons x nil }.

  Fixpoint concat {X: Set}(ll: list (list X)) :=
    match ll with
      | nil => nil
      | cons hl tll => app hl (concat tll)
    end.
  Program Instance concat_Natrans
  : Natrans (ComposeFunctor ListFunctor ListFunctor) ListFunctor :=
    { natrans X := fun ll => concat ll }.
  Next Obligation.
    induction x as [ | hl tll ]; simpl in *; auto.
    rewrite map_app.
    congruence.
  Qed.

  Lemma concat_app:
    forall {X: Set}(ll1 ll2: list (list X)),
      concat (ll1 ++ ll2) = concat ll1 ++ concat ll2.
  Proof.
    induction ll1 as [ | hl tll ]; simpl in *; auto.
    intros.
    rewrite <- app_assoc.
    rewrite IHtll.
    reflexivity.
  Qed.

  Program Instance ListMonad: Monad ListFunctor.
  Next Obligation.
    apply app_nil_r.
  Qed.
  Next Obligation.
    induction x as [ | h t ]; simpl in *; congruence.
  Qed.
  Next Obligation.
    induction x as [ | hll tlll ]; simpl in *; auto.
    rewrite concat_app.
    rewrite IHtlll.
    reflexivity.
  Qed.




  Lemma flat_map_app:
    forall (X Y: Set)(f: X -> list Y)(l1 l2: list X),
      flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
  Proof.
    induction l1 as [ | h t ]; simpl in *; auto.
    intros.
    rewrite <- app_assoc; congruence.
  Qed.

  Program Instance ListKT: KT (fun X: Sets => list X) :=
    { ret X a := cons a nil;
      bind X Y f := flat_map f }.
  Next Obligation.
    induction x as [ | h t ]; simpl in *; auto; congruence.
  Qed.
  Next Obligation.
    induction x as [ | h t ]; simpl in *; auto; congruence.
  Qed.
  Next Obligation.
    apply app_nil_r.
  Qed.
  Next Obligation.
    induction x as [ | h t ]; simpl in *; auto.
    rewrite flat_map_app.
    rewrite IHt.
    reflexivity.
  Qed.






  Class Monoid :=
    { mon : Set;
      mon_binop: mon -> mon -> mon;
      mon_unit: mon;

      monoid_unit_left:
        forall x: mon,
          mon_binop mon_unit x = x;
      monoid_unit_right:
        forall x: mon,
          mon_binop x mon_unit = x;
      monoid_assoc:
        forall x y z: mon,
          mon_binop x (mon_binop y z) =mon_binop (mon_binop x y) z }.
  Notation "X ⊕ Y" := (mon_binop X Y) (at level 60, right associativity).
  Coercion mon: Monoid >-> Sortclass.

  Class MonoidHom (M N: Monoid) :=
    { mon_map : M -> N;

      mon_map_unit:
        mon_map mon_unit = mon_unit;

      mon_map_binop:
        forall x y: M,
          mon_map (x⊕y) = mon_map x⊕mon_map y }.
  Coercion mon_map: MonoidHom >-> Funclass.
  Program Instance ComposeMH{M N L: Monoid}(f: MonoidHom M N)(g: MonoidHom N L)
  : MonoidHom M L :=
    { mon_map x := mon_map (mon_map x) }. 
  Next Obligation.
    repeat rewrite mon_map_unit; auto.
  Qed.
  Next Obligation.
    repeat rewrite mon_map_binop; auto.
  Qed.
  Program Instance IdMH {M: Monoid}: MonoidHom M M :=
    { mon_map x := x }. 

  Program Instance MonoidHomSetoid (X Y: Monoid): Setoid :=
    { carrier := MonoidHom X Y; equal f g := forall x, f x = g x }. 
  Next Obligation.
    split; split; auto; congruence.
  Qed.

  Program Instance MonoidHomMorphism: Morphism Monoid :=
    { fun_type X Y := MonoidHomSetoid X Y }.
  Program Instance CMHM: Composable MonoidHomMorphism :=
    { compose X Y Z f g := ComposeMH f g }.
  Next Obligation.
    congruence.
  Qed.
  Program Instance: Associative CMHM.
  Program Instance: HasLeftId CMHM :=
    { lid X := IdMH }.
  Program Instance: HasRightId CMHM :=
    { rid X := IdMH }.
  Program Instance MHhasId: HasId CMHM :=
    { id X := IdMH }.
  Program Instance Mon: Category :=
    { obj := Monoid ; arr := MonoidHomMorphism }.


  Program Instance ForgetMon_fmap (X Y: Monoid)
  : Map (MonoidHomSetoid X Y) (FunctionSetoid X Y) :=
    { ap f := f }.
  Program Instance ForgetMon: Functor Mon Sets :=
    { fobj X := (@mon X) ; fmap X Y := ForgetMon_fmap X Y }.

  Program Instance ListMonoid (X: Set): Monoid :=
    { mon := list X;
      mon_binop x y := app x y;
      mon_unit := nil }.
  Next Obligation.
    apply app_nil_r.
  Qed.
  Next Obligation.
    apply app_assoc.
  Qed.

  Program Instance map_MonoidHom {X Y: Set}(f: X -> Y)
  : MonoidHom (ListMonoid X) (ListMonoid Y) :=
    { mon_map := map f }.
  Next Obligation.
    apply map_app.
  Qed.

  Program Instance map_MonoidHomMap (X Y: Set)
  : Map (X ⟶ Y) (ListMonoid X ⟶ ListMonoid Y) :=
    { ap := map_MonoidHom }.
  Next Obligation.
    induction x0 as [ | h t ]; auto.
    simpl.
    rewrite H.
    rewrite IHt.
    reflexivity.
  Qed.

  Program Instance ListFunctorMon: Functor Sets Mon :=
    { fobj X := ListMonoid X ; fmap X Y := map_MonoidHomMap X Y }.
  Next Obligation.
    induction x as [ | h t ]; simpl; congruence.
  Qed.
  Next Obligation.
    induction x as [ | h t ]; simpl; congruence.
  Qed.

  Check terminal.

  Program Instance RADJ (X: Sets)(Y: Mon)(g: X -> ForgetMon Y)
  : MonoidHom (ListFunctorMon X) Y.
  Next Obligation.
    induction H as [ | h t ].
    - exact mon_unit.
    - exact (g h⊕IHt).
  Defined.
  Next Obligation.
    unfold RADJ_obligation_1; simpl.
    generalize dependent y.
    induction x as [ | h t ].
    - simpl.
      intro.
      rewrite monoid_unit_left; auto.
    - simpl.
      intro.
      rewrite IHt.
      rewrite monoid_assoc.
      auto.
  Qed.

  Program Instance ListAdjunction
  : Adjunction_Hom ListFunctorMon ForgetMon :=
    { adj_phi X Y f := fun x => f (cons x nil);
      adj_phi_inv X Y g := RADJ _ _ g
    }.
  Next Obligation.
    unfold RADJ_obligation_1; simpl.
    induction x as [ | h t ]; simpl; congruence.
  Qed.
  Next Obligation.
    unfold RADJ_obligation_1; simpl.
    induction x as [ | h t ]; simpl.
    - change (mon_unit = f mon_unit).
      rewrite mon_map_unit; auto.
    - rewrite IHt.
      rewrite <- mon_map_binop.
      simpl.
      auto.
  Qed.
  Next Obligation.
    rewrite monoid_unit_right.
    auto.
  Qed.

End Example.
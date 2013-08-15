
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
    { fun_type (X Y: S): Setoid }.
  Notation "X ⟶ Y" := (fun_type X Y) (at level 60, right associativity).
  Class Composable {S: Type}(m: Morphism S) :=
    { compose {X Y Z: S}: (X ⟶ Y) -> (Y ⟶ Z) -> (X ⟶ Z);
      compose_subst:
        forall {X Y Z: S}(f f': X ⟶ Y)(g g': Y ⟶ Z),
          f == f' -> g == g' -> compose f g == compose f' g' }.
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
  (* Notation "F .[ f ]" := (@fmap _ _ F _ _ f) (at level 55, left associativity). *)

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

  Class Natrans {C D: Category}(F G: Functor C D) :=
    { natrans (X: C): (@fun_type _ (@arr D) (F X) (G X));
      naturality:
        forall (X Y: C)(f: X ⟶ Y),
          (natrans Y) ◦ fmap f == fmap f ◦ (natrans X) }.
  Coercion natrans: Natrans >-> Funclass.
  
  Require Import List.
  (*
  Inductive list (A: Set) :=
  | nil | cons (h: A)(t: list A).
  Arguments nil {A}.
  Arguments cons {A}(h)(t).
  Fixpoint map {X Y: Set}(f: X -> Y)(l: list X): list Y :=
    match l with
      | nil => nil
      | cons h t => cons (f h) (map f t)
    end.
  Fixpoint app {X: Set}(l1 l2: list X): list X :=
    match l1 with
      | nil => l2
      | cons h t => cons h (app t l2)
    end.
  Lemma map_id:
    forall {X: Set}(l: list X), map id l = l.
  Proof.
    induction l as [ | h t ]; simpl in *; congruence.
  Qed.
  Lemma map_map:
    forall {X Y Z: Set}(f: X -> Y)(g: Y -> Z)(l: list X),
      map g (map f l) = map (fun x => g (f x)) l.
  Proof.
    induction l as [ | h t ]; simpl in *; congruence.
  Qed.
  Lemma map_app:
    forall (X Y: Set)(f: X -> Y)(l1 l2: list X),
      map f (app l1 l2) = app (map f l1) (map f l2).
  Proof.
    induction l1 as [ | h t ]; simpl in *; congruence.
  Qed. *)

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



  Program Instance MonadKT `(monad: Monad): KT fobj :=
    { ret X := m_unit X;
      bind X Y f := m_join Y ◦ fmap f }.
  Next Obligation.
    apply compose_subst; [ | apply eq_refl; auto ].
    apply ap_preserve_eq.
    apply H.
  Qed.
  Next Obligation.
    apply m_join_T_unit.
  Qed.
  Next Obligation.
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
        apply right_rid_id.
  Qed.
  Next Obligation.
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
    apply bind_subst.
    apply compose_subst; [ apply H | apply eq_refl; auto ].
  Qed.

  Program Instance KTFunctor {C: Category}{T: C -> C}(kt: KT T): Functor C C :=
    { fobj := T;
      fmap X Y := KT_fmap_Map C T kt X Y}.
  Next Obligation.
    apply eq_trns with (bind ret); auto.
    - apply bind_subst.
      apply eq_trns with (ret ◦ lid); auto.
      + apply compose_subst; [ apply eq_id_lid | apply eq_refl; auto ].
      + apply left_lid_id.
    - apply ret_left.
  Qed.
  Next Obligation.
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
    apply eq_symm; auto; apply ret_right.
  Qed.

  Program Instance KTNatrans_join
          {C: Category}{T: C -> C}(kt: KT T)
  : Natrans (ComposeFunctor (KTFunctor kt) (KTFunctor kt)) (KTFunctor kt):=
    { natrans X := bind id }.
  Next Obligation.
    eapply eq_trns; [ auto | apply bind_assoc | ].
    eapply eq_trns; [ auto | | apply eq_symm; auto; apply bind_assoc ].
    apply bind_subst.
    eapply eq_trns; [ auto | apply eq_symm; auto; apply compose_assoc | ].
    eapply eq_trns; [ auto | apply compose_subst | ].
    - apply eq_refl; auto.
    - apply ret_right.
    - apply eq_trns with (rid ◦ bind (ret ◦ f)); auto.
      + apply compose_subst; [ apply eq_refl; auto | ].
        apply eq_id_rid.
      + eapply eq_trns; [ auto | apply right_rid_id | ].
        apply eq_trns with (bind (ret ◦ f) ◦ lid); auto.
        * apply eq_symm; auto; apply left_lid_id.
        * apply compose_subst; [ | apply eq_refl; auto ].
          apply eq_symm; auto; apply eq_id_lid.
  Qed.

  Program Instance KTMonad
          {C: Category}{T: C -> C}(kt: KT T)
  : Monad (KTFunctor kt).
  Next Obligation.
    apply ret_right.
  Qed.
  Next Obligation.
    eapply eq_trns; [ auto | apply bind_assoc | ].
    eapply eq_trns; [ auto | apply bind_subst | ].
    apply eq_symm; auto; apply compose_assoc.
    eapply eq_trns; [ auto | apply bind_subst | ].
    apply compose_subst; [ apply eq_refl; auto | apply ret_right ].
    eapply eq_trns; [ auto | apply bind_subst | ].
    apply compose_subst; [ apply eq_refl; auto | apply eq_id_rid ].
    eapply eq_trns; [ auto | apply bind_subst | ].
    apply right_rid_id.
    apply ret_left.
  Qed.
  Next Obligation.
    eapply eq_trns; [ auto | apply bind_assoc | ].
    eapply eq_trns; [ auto | | apply eq_symm; auto; apply bind_assoc ].
    apply bind_subst.
    eapply eq_trns; [ auto | apply compose_subst | ].
    apply eq_id_lid.
    apply eq_refl; auto.
    eapply eq_trns; [ auto | apply left_lid_id | ].
    eapply eq_trns; [ auto | | apply compose_assoc ].
    eapply eq_trns; [ auto | | apply compose_subst ].
    apply eq_symm; auto; apply right_rid_id.
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
    apply compose_subst; [ assumption | apply bind_subst ; assumption ].
  Qed.
  Program Instance AssociativeKTMorphism
          {C: Category}{T: C -> C}(kt: KT T)
  : Associative (ComposableKTMorphism kt).
  Next Obligation.
    unfold KTCompose.
    eapply eq_trns; [ auto | | apply compose_assoc ].
    apply compose_subst; [ apply eq_refl; auto | ].
    apply eq_symm; auto.
    apply bind_assoc.
  Qed.
  Program Instance KTMorphismHasLeftId
          {C: Category}{T: C -> C}(kt: KT T)
  : HasLeftId (ComposableKTMorphism kt) :=
    { lid X := ret }.
  Next Obligation.
    unfold KTCompose.
    apply ret_right.
  Qed.
  Program Instance KTMorphismHasRightId
          {C: Category}{T: C -> C}(kt: KT T)
  : HasRightId (ComposableKTMorphism kt) :=
    { rid X := ret }.
  Next Obligation.
    unfold KTCompose.
    eapply eq_trns; [ auto | apply compose_subst | ].
    - apply eq_refl; auto.
    - apply ret_left.
    - apply eq_trns with (rid ◦ f); auto; [ apply compose_subst | ]. 
      + apply eq_refl; auto.
      + apply eq_id_rid.
      + apply right_rid_id.
  Qed.
  Program Instance KTMorphismHasId
          {C: Category}{T: C -> C}(kt: KT T)
  : HasId (ComposableKTMorphism kt) :=
    { id X := ret }.
  Next Obligation.
    apply eq_refl; auto.
  Qed.
  Next Obligation.
    apply eq_refl; auto.
  Qed.

  Program Instance KT_KleisliCategory
          {C: Category}{T: C -> C}(kt: KT T)
  : Category :=
    { obj := obj ; arr := KTMorphism kt }.

  Program Instance KleisliCategory
          {C: Category}{T: Functor C C}(m: Monad T)
  : Category := KT_KleisliCategory (MonadKT m).



  Class Adjunction {C D: Category}
        (F: Functor C D)(G: Functor D C) :=
    { adj_phi (X: C)(Y: D): (F X ⟶ Y) -> (X ⟶ G Y);
      adj_phi_inv (X: C)(Y: D): (X ⟶ G Y) -> (F X ⟶ Y);

      adj_phi_iso:
        forall (X: C)(Y: D)(f: F X ⟶ Y),
          adj_phi_inv X Y (adj_phi X Y f) == f;
      adj_phi_inv_iso:
        forall (X: C)(Y: D)(g: X ⟶ G Y),
          adj_phi X Y (adj_phi_inv X Y g) == g;
  
      adj_naturality:
        forall (X Y: C)(Z W: D)(f: X ⟶ Y)(g: F Y ⟶ Z)(h: Z ⟶ W),
          adj_phi X W (h◦g◦fmap f) == fmap h ◦ adj_phi Y Z g ◦ f }.
  

  
  Class Monoid :=
    { mon :> Setoid;
      mon_binop: mon -> mon -> mon;
      mon_unit: mon;

      monoid_unit_left:
        forall x: mon,
          mon_binop mon_unit x == x;
      monoid_unit_right:
        forall x: mon,
          mon_binop mon_unit x == x;
      monoid_assoc:
        forall x y z: mon,
          mon_binop x (mon_binop y z) == mon_binop (mon_binop x y) z }.
  Notation "X ⊕ Y" := (mon_binop X Y) (at level 60, right associativity).
  Coercion mon: Monoid >-> Setoid.

  Class MonoidHom (M N: Monoid) :=
    { mon_map :> Map M N;

      mon_map_unit:
        mon_map mon_unit == mon_unit;

      mon_map_binop:
        forall x y: M,
          mon_map (x⊕y) == mon_map x⊕mon_map y }.
  Coercion mon_map: MonoidHom >-> Map.
  
  
End Functor.
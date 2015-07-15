(* Cat_on_Coq: redefine *)
Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Reversible Pattern Implicit.

Generalizable All Variables.

Set Universe Polymorphism.

(**
 * 基本となる道具
Setoid や Setoid 間の写像など、圏を定義する上で必要となる道具を定義する。
 **)
(** 
Coq が通常提供する記法も、後々一般化する。
そのため、開発においては [-nois] オプションを施している。

とはいえ何も使えないと不便なので、スコープを定め、 Local に利用する。
 **)
Delimit Scope base_scope with base.
Open Scope base_scope.

Local Notation "X -> Y" :=
  (forall (_: X), Y) (at level 99, right associativity, Y at level 200): base_scope.

(**
 ** 関係と性質
 **)

Definition relation (X: Type) := X -> X -> Prop.

(** 
同値関係の定義に向けて、性質を表わすクラスを定義していく
 **)

Class Reflexive `(R: relation X): Prop :=
  reflexivity:
    forall x: X, R x x.

Class Symmetric `(R: relation X): Prop :=
  symmetry:
    forall x y: X, R x y -> R y x.

Class Transitive `(R: relation X): Prop :=
  transitivity:
    forall x y z: X, R x y -> R y z -> R x z.

Class Equivalence `(R: relation X): Prop :=
  {
    equiv_Reflexive:> Reflexive R;
    equiv_Symmetric:> Symmetric R;
    equiv_Transitive:> Transitive R
  }.
Existing Instance equiv_Reflexive.
Existing Instance equiv_Symmetric.
Existing Instance equiv_Transitive.


(** 
 ** Setoid
同値関係を伴う型。
 **)
Module Setoid.
  Structure t :=
    {
      carrier: Type;
      equal: relation carrier;

      prf: Equivalence equal
    }.

  Module Notations.
    Notation Setoid := t.
    Coercion carrier: Setoid >-> Sortclass.
    Coercion prf: Setoid >-> Equivalence.
    Existing Instance prf.

    (** [=] の使い道を Setoid に一般化。 **)
    Notation "x = y :> X" := (@equal X x y)
                               (at level 70,
                                y at next level, no associativity).
    Notation "x = y" := (x = y :> _) (at level 70, no associativity).

    Notation mkSetoid equiv := (Build_t equiv).
  End Notations.
End Setoid.
Export Setoid.Notations.


(* eq and example of Equivalence *)
Module Eq.
  Variant eq (X: Type): relation X :=
  | eq_refl: forall x: X, eq x x.

  Lemma eq_ind:
    forall (X: Type)(P: relation X),
      (forall x: X, P x x) ->
      (forall x y: X, eq x y -> P x y).
  Proof.
    intros X P IH x y Heq.
    destruct Heq.
    exact (IH x).
  Qed.

  Instance eq_Reflexive (X: Type): Reflexive (@eq X).
  Proof.
    intro x.
    exact eq_refl.
  Qed.

  Instance eq_Symmetric (X: Type): Symmetric (@eq X).
  Proof.
    intros x y Heq.
    destruct Heq.
    exact eq_refl.
  Qed.

  Instance eq_Transitive (X: Type): Transitive (@eq X).
  Proof.
    intros x y z Heqxy Heqyz.
    destruct Heqxy.
    exact Heqyz.
  Qed.

  Instance eq_Equivalence (X: Type): Equivalence (@eq X) := {}.

  Definition setoid (X: Type): Setoid :=
    mkSetoid (@Eq.eq_Equivalence X).
End Eq.

(**
 ** Map
Setoid 間の写像
 **)

Module Map.
  Class spec {X Y: Setoid}(f: X -> Y): Prop :=
    substitute:
      forall (x y: X), x = y -> f x = f y.

  Structure t (X Y: Setoid) :=
    {
      f: X -> Y;
      prf: spec f
    }.

  Definition dom {X Y}(m: t X Y): Setoid := X.
  Definition cod {X Y}(m: t X Y): Setoid := Y.

  Module Notations.
    Notation isMap := spec.
    Notation Map := t.
    Coercion f: Map >-> Funclass.
    Coercion prf: Map >-> isMap.
    Existing Instance prf.

    Notation "X --> Y" := (Map X Y)
                           (at level 99, right associativity): base_scope.
    Notation mkMap prf := (@Build_t _ _ _ prf).
    Notation Map_frame f := (@Build_t _ _ f _).
    Notation "[ x .. y :-> p ]" := 
      (Map_frame (fun x => .. (Map_frame (fun y => p)) ..))
        (at level 200, x binder, right associativity,
         format "'[' [ x .. y :-> '/ ' p ] ']'").
  End Notations.
End Map.
Export Map.Notations.

Module Fun.
  Instance isMap {X Y: Type}(f: X -> Y)
  : @isMap (Eq.setoid X) (Eq.setoid Y) f.
  Proof.
    intros x y Heq; destruct Heq.
    exact Eq.eq_refl.
  Qed.

  Definition map {X Y: Type}(f: X -> Y): Map _ _
    := mkMap (isMap f).
End Fun.

Canonical Structure Eq.setoid.
Check (forall (X Y: Type)(f: X -> Y), forall x, f x = f x).

Module MapSetoid.
  Definition equal {X Y: Setoid}: relation (X --> Y) :=
    fun f g => forall x: X, f x = g x.

  Instance equiv (X Y: Setoid): Equivalence (@equal X Y).
  Proof.
    apply Build_Equivalence.
    - intros f x; exact reflexivity.
    - intros f g Heq x.
      generalize (Heq x).
      apply symmetry.
    - intros f g h Heqfg Heqgh x.
      apply transitivity with (g x).
      + exact (Heqfg x).
      + exact (Heqgh x).
  Qed.

  Definition setoid (X Y: Setoid): Setoid := mkSetoid (@equiv X Y).
End MapSetoid.
Notation "X --> Y" := (MapSetoid.setoid X Y)
                        (at level 99, right associativity).

Module Category.
  Class spec
        (obj: Type)
        (arr: obj -> obj -> Setoid)
        (comp: forall {X Y Z: obj}, arr X Y -> arr Y Z -> arr X Z)
        (id: forall X: obj, arr X X) :=
    {
      comp_subst:
        forall (X Y Z: obj)(f f': arr X Y)(g g': arr Y Z),
          f = f' -> g = g' -> comp f g = comp f' g';
          
      comp_assoc:
        forall (X Y Z W: obj)
               (f: arr X Y)(g: arr Y Z)(h: arr Z W),
          comp f (comp g h) = comp (comp f g) h;

      comp_id_dom:
        forall (X Y: obj)(f: arr X Y), comp (id X) f = f;

      comp_id_cod:
        forall (X Y: obj)(f: arr X Y), comp f (id Y) = f
    }.

  Structure t :=
    {
      obj: Type;
      arr: obj -> obj -> Setoid;
      comp: forall {X Y Z: obj}, arr X Y -> arr Y Z -> arr X Z;
      id: forall X: obj, arr X X;

      prf: spec (@comp) (@id)
    }.

  Module Notations.
    Notation Category := t.
    Notation isCategory := spec.
    Coercion obj: Category >-> Sortclass.
    Coercion arr: Category >-> Funclass.
    Existing Instance prf.
    Notation "g \o{ C } f" := (@comp C _ _ _ f g)
                                (at level 60, right associativity).
    Notation "g \o f" := (g \o{_} f)
                           (at level 60, right associativity).
    Notation "'Id' X" := (@id _ X) (at level 30, right associativity).
  End Notations.
End Category.
Export Category.Notations.



Require Coq.Init.Datatypes Coq.Init.Specif Coq.Program.Tactics.
Program Definition Map_compose
        {X Y Z: Setoid}(f: X --> Y)(g: Y --> Z): X --> Z :=
  [ x :-> g (f x)].
Next Obligation.
  intros x x' Heq.
  do 2 apply Map.substitute.
  exact Heq.
Qed.

Program Definition Map_id (X: Setoid): X --> X :=
  [ x :-> x ].
Next Obligation.
  intros x y Heq; exact Heq.
Qed.


Program Instance Setoids_isCategory
  : isCategory
      (@Map_compose)
      (@Map_id).
Next Obligation.
  intros x; simpl.
  apply transitivity with (g (f' x)).
  - apply Map.substitute, H.
  - apply H0.
Qed.
Next Obligation.
  intros x; simpl.
  apply reflexivity.
Qed.
Next Obligation.
  intros x; simpl.
  apply reflexivity.
Qed.
Next Obligation.
  intros x; simpl.
  apply reflexivity.
Qed.

Definition Setoids: Category := Category.Build_t Setoids_isCategory.


(** 
 ** 函手
 **)
Module Functor.
  Class spec (C D: Category)
        (fobj: C -> D)
        (fmap: forall {X Y: C}, C X Y -> D (fobj X) (fobj Y)) :=
    {
      fmap_isMap: forall (X Y: C), isMap (@fmap X Y);

      fmap_comp:
        forall (X Y Z: C)(f: C X Y)(g: C Y Z),
          fmap (g \o f) = fmap g \o fmap f;

      fmap_id:
        forall (X: C), fmap (Id X) = Id (fobj X)
    }.

  Structure t (C D: Category) :=
    {
      fobj: C -> D;
      fmap: forall X Y: C, C X Y -> D (fobj X) (fobj Y);

      prf: spec (@fmap)
    }.

  Module Notations.
    Notation Functor := t.
    Notation isFunctor := spec.
    Coercion fobj: Functor >-> Funclass.
    Existing Instance fmap_isMap.
    Existing Instance prf.

  End Notations.
End Functor.
Export Functor.Notations.

Definition fmap {C D: Category}(F: Functor C D){X Y: C}(f: C X Y)
  : D (F X) (F Y) :=
  (@Functor.fmap _ _ F _ _ f).
Arguments fmap {C D}(F){X Y}(f).

Program Instance Functor_compose_prf (C D E: Category)
        (F: Functor C D)(G: Functor D E)
  : isFunctor (fun X Y f => fmap G (fmap F f)).
Next Obligation.
  intros f g Heq; simpl.
  do 2 apply (Map.substitute).
  exact Heq.
Qed.
Next Obligation.
  eapply transitivity.
  - apply Functor.fmap_isMap.
    apply Functor.fmap_comp.
  - apply Functor.fmap_comp.
Qed.
Next Obligation.
  eapply transitivity.
  - apply Functor.fmap_isMap.
    apply Functor.fmap_id.
  - apply Functor.fmap_id.
Qed.  

Definition Functor_compose (C D E: Category)
        (F: Functor C D)(G: Functor D E): Functor C E :=
  {|
    Functor.prf := Functor_compose_prf C D E F G
  |}.

Program Instance Functor_id_prf (C: Category)
  : isFunctor (D:=C)(fun X Y f => f).
Next Obligation.
  exact Map_id.
Qed.
Next Obligation.
  apply reflexivity.
Qed.
Next Obligation.
  apply reflexivity.
Qed.

(*
Module FunctorEq.
  Unset Elimination Schemes.

  Inductive jmeq {X: Setoid}(x: X)
  : forall (Y: Setoid), Y -> Prop := 
  | jmeq_def: forall (y: X), x = y -> jmeq x y.

  Set Elimination Schemes.

  Lemma jmeq_refl:
    forall (X: Setoid)(x: X), jmeq x x.
  Proof.
    intros; apply jmeq_def, reflexivity.
  Qed.

  Lemma eq_arr_symm:
    forall (X Y: Setoid)
           (x: X)(y: Y),
      jmeq x y -> jmeq y x.
  Proof.
    intros X Y x y [x' Heq].
    trivial.
    apply jmeq_def.
    apply symmetry.
    exact Heq.
*)
(* Toplevel input, characters 0-4: *)
(* > Qed. *)
(* > ^^^^ *)
(* Error: *)
(* Incorrect elimination of "H" in the inductive type "@jmeq": *)
(* ill-formed elimination predicate. *)
(*  Qed.

  Lemma eq_arr_refl:
    forall (C: Category)
           (df cf: C)(f: C df cf)
           (dg cg: C)(g: C dg cg),
      eq_arr f g -> eq_arr g f.
  Proof.
    intros; apply eq_arr_def.
  Qed.

  Definition equal {C D: Category}: relation (Functor C D) :=
    fun F G => forall (X Y: C)(f: C X Y), fmap F f = fmap G f.
 *)

Definition Functor_id (C: Category): Functor C C :=
  {|
    Functor.prf := Functor_id_prf C
  |}.

Require Import Coq.Logic.JMeq.

Variant arrow (C: Category) :=
| arrow_triple (dom cod: C)(f: C dom cod).

Definition eq_Functor (C D: Category): relation (Functor C D) :=
  fun F G =>
    forall (X Y: C)(f: C X Y),
      JMeq (fmap F f) (fmap G f).

Instance equiv_Functor (C D: Category): Equivalence (@eq_Functor C D).
Proof.
  split.
  - intros F X Y f; apply JMeq_refl.
  - intros F G Heq X Y f.
    apply JMeq_sym.
    apply Heq.
  - intros F G H HeqFG HeqGH X Y f.
    apply (JMeq_trans (y:=fmap G f)).
    + apply HeqFG.
    + apply HeqGH.
Qed.

Definition Functor_setoid (C D: Category) :=
  mkSetoid (@equiv_Functor C D).

Instance Cat_isCategory
  : isCategory
      (arr:=Functor_setoid)
      (@Functor_compose)
      (@Functor_id).
Proof.
  split.
  - intros C D E F F' G G'.
    intros HeqF HeqG X Y f; simpl.
    apply (JMeq_trans (y:= fmap G' (fmap F f))).
    + simpl.
      apply (HeqG _ _ (fmap F f)).
    + simpl.
      pattern (fmap F f).
      eapply JMeq_ind. [| apply HeqF].
      * apply JMeq_refl.
      generalize (HeqF _ _ f); intro H.
      
    Next Obligation.
  intros .

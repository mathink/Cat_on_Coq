(* Cat_on_Coq: redefine *)
Require Import Coq.Init.Prelude.
Require Coq.Program.Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Reversible Pattern Implicit.
Set Primitive Projections.

Set Universe Polymorphism.

(*  *)
Unset Nonrecursive Elimination Schemes.
Obligation Tactic := idtac.

Generalizable All Variables.
(**
 * 基本となる道具
Setoid や Setoid 間の写像など、圏を定義する上で必要となる道具を定義する。
 **)
(** 
Coq が通常提供する記法も、後々一般化する。
そのため、開発においては [-nois] オプションを施している。

とはいえ何も使えないと不便なので、スコープを定め、 Local に利用する。
 **)
(* Delimit Scope base_scope with base. *)
(* Open Scope base_scope. *)

(* Local Notation "X -> Y" := *)
(*   (forall (_: X), Y) (at level 99, right associativity, Y at level 200): base_scope. *)

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
  Structure type :=
    make {
        carrier: Type;
        equal: relation carrier;
        
        prf: Equivalence equal
      }.

  Notation build equal :=
    (@make _ equal (@Build_Equivalence _ equal _ _ _)).

  Module Notations.
    Notation Setoid := type.
    Coercion carrier: Setoid >-> Sortclass.
    Coercion prf: Setoid >-> Equivalence.
    Existing Instance prf.

    Notation "x == y :> X" := (@equal X x y)
                               (at level 70,
                                y at next level, no associativity).
    Notation "x == y" := (x == y :> _) (at level 70, no associativity).

    Notation mkSetoid equiv := (make equiv).
  End Notations.
End Setoid.
Export Setoid.Notations.

(**
 ** Map
Setoid 間の "写像"
 **)
Module Map.
  Class spec {X Y: Setoid}(f: X -> Y): Prop :=
    substitute:
      forall (x y: X), x == y -> f x == f y.

  Structure type (X Y: Setoid) :=
    make {
        f: X -> Y;
        prf: spec f
      }.

  Notation build f := (@make _ _ f _).

  Module Notations.
    Notation isMap := spec.
    Notation Map := type.
    Coercion f: Map >-> Funclass.
    Coercion prf: Map >-> isMap.
    Existing Instance prf.

    Notation "[ x .. y :-> p ]" := 
      (build (fun x => .. (build (fun y => p)) ..))
        (at level 200, x binder, right associativity,
         format "'[' [ x .. y :-> '/ ' p ] ']'").
  End Notations.
  Import Notations.

  Definition dom {X Y}(m: Map X Y): Setoid := X.
  Definition cod {X Y}(m: Map X Y): Setoid := Y.

  Program Definition compose
          {X Y Z: Setoid}(f: Map X Y)(g: Map Y Z): Map X Z :=
    [ x :-> g (f x)].
  Next Obligation.
    intros X Y Z f g x x' Heq.
    do 2 apply Map.substitute.
    exact Heq.
  Qed.

  Program Definition id (X: Setoid): Map X X := [ x :-> x ].
  Next Obligation.
    intros X x y Heq; exact Heq.
  Qed.

  Definition equal {X Y: Setoid}: relation (Map X Y) :=
    fun f g => forall x: X, f x == g x.

  Program Definition setoid (X Y: Setoid): Setoid :=
    Setoid.build (@equal X Y).
  Next Obligation.
    intros X Y f x; exact reflexivity.
  Qed.
  Next Obligation.
    intros X Y f g Heq x.
    generalize (Heq x).
    apply symmetry.
  Qed.
  Next Obligation.
    intros X Y f g h Heqfg Heqgh x.
    apply transitivity with (g x).
    - exact (Heqfg x).
    - exact (Heqgh x).
  Qed.
End Map.
Export Map.Notations.

(** 
 ** (Coq 上の)圏
対象間の等価性は気にしないため、対象の型は [Type]

射は、各 Hom が Setoid になる
 **)
Module Category.
  Class spec
        (obj: Type)
        (arr: obj -> obj -> Setoid)
        (comp: forall {X Y Z: obj}, arr X Y -> arr Y Z -> arr X Z)
        (id: forall X: obj, arr X X) :=
    proof {
        comp_subst:
          forall (X Y Z: obj)(f f': arr X Y)(g g': arr Y Z),
            f == f' -> g == g' -> comp f g == comp f' g';
        
        comp_assoc:
          forall (X Y Z W: obj)
                 (f: arr X Y)(g: arr Y Z)(h: arr Z W),
            comp f (comp g h) == comp (comp f g) h;

        comp_id_dom:
          forall (X Y: obj)(f: arr X Y), comp (id X) f == f;

        comp_id_cod:
          forall (X Y: obj)(f: arr X Y), comp f (id Y) == f
      }.

  Structure type :=
    make {
        obj: Type;
        arr: obj -> obj -> Setoid;
        comp: forall {X Y Z: obj}, arr X Y -> arr Y Z -> arr X Z;
        id: forall X: obj, arr X X;

        prf: spec (@comp) (@id)
      }.

  Notation build arr comp id :=
    (@make _ arr comp id (@proof _ _ _ _ _ _ _ _)).

  Module Notations.
    Notation Category := type.
    Notation isCategory := spec.
    Coercion obj: Category >-> Sortclass.
    Coercion arr: Category >-> Funclass.
    Coercion prf: Category >-> isCategory.
    Existing Instance prf.

    Notation "g \o{ C } f" := (@comp C _ _ _ f g)
                                (at level 60, right associativity).
    Notation "g \o f" := (g \o{_} f)
                           (at level 60, right associativity).
    Notation "'Id' X" := (@id _ X) (at level 30, right associativity).
  End Notations.

  Import Notations.

  (**
   *** 圏の双対
build のおかげで定義しやすい気がする。
   **)
  Program Definition op (C: Category): Category :=
    build (fun X Y: C => C Y X)
          (fun X Y Z f g => f \o g)
          (fun X => Id X).
  Next Obligation.
    intros; simpl in *.
    apply comp_subst; assumption.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply symmetry, comp_assoc.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply comp_id_cod.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply comp_id_dom.
  Qed.
End Category.
Export Category.Notations.

(** 
 ** Setoid の圏: Setoids
例にちょうどよい。
あと、 Hom 函手を定義する時とかに使うのでここで作っておこう。
 **)
Program Definition Setoids: Category :=
  Category.build (@Map.setoid) (@Map.compose) (@Map.id).
Next Obligation.
  intros X Y Z f f' g g' Heqf Heqg x; simpl.
  apply transitivity with (g (f' x)).
  - apply Map.substitute, Heqf.
  - apply Heqg.
Qed.
Next Obligation.
  intros; simpl.
  intros x; simpl.
  apply reflexivity.
Qed.
Next Obligation.
  intros; simpl; intro x; simpl.
  apply reflexivity.
Qed.
Next Obligation.
  intros; simpl; intro x; simpl.
  apply reflexivity.
Qed.

(** 
 ** 函手
 **)
Module Functor.
  Class spec (C D: Category)
        (fobj: C -> D)
        (fmap: forall {X Y: C}, Setoids (C X Y) (D (fobj X) (fobj Y))) :=
    proof {
        fmap_comp:
          forall (X Y Z: C)(f: C X Y)(g: C Y Z),
            fmap (g \o f) == fmap g \o fmap f;

        fmap_id:
          forall (X: C), fmap (Id X) == Id (fobj X)
      }.

  Structure type (C D: Category) :=
    make {
        fobj: C -> D;
        fmap: forall X Y: C, Setoids (C X Y) (D (fobj X) (fobj Y));

        prf: spec (@fmap)
      }.

  Notation build fobj fmap :=
    (@make _ _ fobj (fun _ _ => fmap) (@proof _ _ _ _ _ _))
      (only parsing).

  Module Notations.
    Notation Functor := type.
    Notation isFunctor := spec.
    Coercion fobj: Functor >-> Funclass.
    Coercion prf: Functor >-> isFunctor.
    (* Existing Instance fmap_isMap. *)
    Existing Instance prf.

    Notation fmap F f := (@fmap _ _ F _ _ f).
   (* Definition fmap {C D: Category}(F: Functor C D){X Y: C}(f: C X Y) *)
   (*    : D (F X) (F Y) := *)
   (*    (@fmap _ _ F _ _ f). *)
   (*  Arguments fmap {C D}(F){X Y}(f). *)
  End Notations.

  Import Notations.

  Program Definition compose (C D E: Category)
          (F: Functor C D)(G: Functor D E): Functor C E :=
    build _ ([ f :-> fmap G (fmap F f)]).
  Next Obligation.
    intros; intros f g Heq; simpl.
    do 2 apply (Map.substitute).
    exact Heq.
  Qed.
  Next Obligation.
    intros; simpl.
    eapply transitivity.
    - apply Map.substitute.
      apply Functor.fmap_comp.
    - apply Functor.fmap_comp.
  Qed.
  Next Obligation.
    intros; simpl.
    eapply transitivity.
    - apply Map.substitute.
      apply Functor.fmap_id.
    - apply Functor.fmap_id.
  Qed.

  Program Definition id (C: Category): Functor C C :=
    build _ ([ f :-> f ]) .
  Next Obligation.
    intros; exact Map.id.
  Qed.
  Next Obligation.
    intros; apply reflexivity.
  Qed.
  Next Obligation.
    intros; apply reflexivity.
  Qed.


  (** 
   *** 函手の等価性
いわゆる heterogeneous equality とかいうやつらしい。
JMeq の仲間(だろう、多分)。

ちなみに、 [eq_Hom] ではなく [JMeq] を使うと、後々示したいものが示せなくなるので注意。
   **)
  Inductive eq_Hom (C : Category)(X Y: C)(f: C X Y):
    forall (Z W: C), C Z W -> Prop :=
  | eq_Hom_def:
      forall (g: C X Y), f == g -> eq_Hom f g.
  Infix "=H" := eq_Hom (at level 70).

  Lemma eq_Hom_refl:
    forall (C: Category)(df cf: C)(bf: C df cf),
      bf =H bf.
  Proof.
    intros C df cf bf; apply eq_Hom_def, reflexivity.
  Qed.

  Lemma eq_Hom_symm:
    forall (C: Category)
           (df cf: C)(bf: C df cf)
           (dg cg: C)(bg: C dg cg),
      bf =H bg -> bg =H bf.
  Proof.
    intros C df cf bf dg cg bg [g Heq].
    apply eq_Hom_def; apply symmetry; assumption.
  Qed.

  Lemma eq_Hom_trans:
    forall (C : Category)
           (df cf: C)(bf: C df cf)
           (dg cg: C)(bg: C dg cg)
           (dh ch: C)(bh: C dh ch),
      bf =H bg -> bg =H bh -> bf =H bh.
  Proof.
    intros C df cf bf dg cg bg dh ch bh [g Heqg] [h Heqh].
    apply eq_Hom_def.
    apply transitivity with g; assumption.
  Qed.

  Definition equal {C D: Category}(F G : Functor C D) :=
    forall (X Y: C)(f: C X Y),
      fmap F f =H fmap G f.
  Arguments equal {C D} / F G.

  Program Definition setoid (C D: Category) :=
    Setoid.build (@equal C D).
  Next Obligation.
    intros C D F X Y f; simpl; apply eq_Hom_refl.
  Qed.
  Next Obligation.
    intros C D F G Heq X Y f; simpl; apply eq_Hom_symm; apply Heq.
  Qed.
  Next Obligation.
    intros C D F G H HeqFG HeqGH X Y f; simpl.
    generalize (HeqGH _ _ f); simpl.
    apply eq_Hom_trans, HeqFG.
  Qed.
End Functor.
Export Functor.Notations.

(** 
 *** 圏の圏：Cat
Universe Polymorphism のおかげで定義できる。
 **)
Program Definition Cat: Category :=
  Category.build
    (Functor.setoid)
    (@Functor.compose)
    (@Functor.id).
Next Obligation.
  intros C D E F F' G G' HeqF HeqG X Y f; simpl.
  destruct (HeqF _ _ f); simpl.
  eapply Functor.eq_Hom_trans.
  - apply Functor.eq_Hom_def.
    apply Map.substitute, H.
  - apply HeqG.
Qed.
Next Obligation.
  intros C D K L F G H X Y f; simpl in *.
  apply Functor.eq_Hom_refl.
Qed.
Next Obligation.
  intros C D F X Y f; simpl in *.
  apply Functor.eq_Hom_refl.
Qed.
Next Obligation.
  intros C D F X Y f; simpl in *.
  apply Functor.eq_Hom_refl.
Qed.


(** 
 ** Hom 函手たち
[Hom(X,-)] と [Hom(-,Y)] を作るよ。
[build] 使うと定義書くのすごく楽。嬉しい。
 **)

(**
 *** 共変な方の [Hom]
 **)
Program Definition HomFunctor (C: Category)(X: C)
  : Functor C Setoids :=
  Functor.build (C X) ([ g f :-> g \o{C} f]).
Next Obligation.
  intros C X Y Z g f f' Heq.
  apply Category.comp_subst; try assumption.
  apply reflexivity.
Qed.
Next Obligation.
  intros C X Y Z g g' Heq f; simpl.
  apply Category.comp_subst; try assumption.
  apply reflexivity.
Qed.
Next Obligation.
  intros C X Y Z W g h f; simpl.
  apply Category.comp_assoc.
Qed.
Next Obligation.
  intros C X Y f; simpl.
  apply Category.comp_id_cod.
Qed.


(**
 *** 反変な方の [Hom]
 **)
Program Definition OpHomFunctor (C: Category)(Y: C)
  : Functor (Category.op C) Setoids :=
  Functor.build (Category.op C Y) ([ f g :-> g \o{C} f]).
Next Obligation.
  intros C Z Y X f g g' Heq; simpl in *.
  apply Category.comp_subst; try assumption.
  apply reflexivity.
Qed.
Next Obligation.
  intros C Z Y X f g g' Heq; simpl in *.
  apply Category.comp_subst; try assumption.
  apply reflexivity.
Qed.
Next Obligation.
  intros C W Z Y X g f h; simpl in *.
  apply symmetry, Category.comp_assoc.
Qed.
Next Obligation.
  intros C Y X f; simpl in *.
  apply Category.comp_id_dom.
Qed.

(**
 *** 記法の定義
 **)
Notation "'Hom' ( X , - )" := (HomFunctor X).
Notation "'Hom' ( - , Y )" := (OpHomFunctor Y).

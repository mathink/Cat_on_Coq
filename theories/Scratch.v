(* Cat_on_Coq: redefine *)
Require Coq.Init.Prelude.
Require Coq.Program.Tactics.

Require Import Coq.Init.Notations Coq.Init.Logic.
Print LoadPath.
Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
(* Set Reversible Pattern Implicit. *)
Set Primitive Projections.

Set Universe Polymorphism.

(*  *)
Unset Nonrecursive Elimination Schemes.
Obligation Tactic := idtac.

Generalizable All Variables.
Delimit Scope cat_scope with cat.
Open Scope cat_scope.

(**
 * 基本となる道具
Setoid や Setoid 間の写像である Map など、圏を定義する上で必要となる道具を定義する。
 **)

(**
 ** 関係と性質
同値関係の定義に向けて、性質を表すクラスを定義していく
 **)
Notation predicate X := (X -> Prop).
Notation relation X := (X -> predicate X).

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

Variant and (A B: Prop): Prop :=
| conj: A -> B -> and A B.
Infix "/\" := and.

Notation "P <-> Q" := ((P -> Q)/\(Q -> P)).

Inductive ex (A: Type)(P: A -> Prop): Prop :=
| ex_intro: forall x: A, P x -> ex (A:=A) P.

Notation "'exists' x .. y , p" :=
  (ex (fun x => .. (ex (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'exists' '/ ' x .. y , '/ ' p ']'"): type_scope.



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

  Module Ex.
    Notation Setoid := type.
    Coercion carrier: Setoid >-> Sortclass.
    Coercion prf: Setoid >-> Equivalence.
    Existing Instance prf.

    Notation "x == y :> X" := (@equal X x y)
                               (at level 70,
                                y at next level, no associativity).
    Notation "x == y" := (x == y :> _) (at level 70, no associativity).

    Notation mkSetoid equiv := (make equiv).
  End Ex.
End Setoid.
Export Setoid.Ex.

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

  Module Ex.
    Notation isMap := spec.
    Notation Map := type.
    Coercion f: Map >-> Funclass.
    Coercion prf: Map >-> isMap.
    Existing Instance prf.

    Notation "[ x .. y :-> p ]" := 
      (build (fun x => .. (build (fun y => p)) ..))
        (at level 200, x binder, right associativity,
         format "'[' [ x .. y :-> '/ ' p ] ']'").
  End Ex.
  Import Ex.

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
Export Map.Ex.

(** 
 * (Coq 上の)圏論
Coq のシステム上に圏論を展開する、ということ。
 **)
(** 
 ** 圏
対象間の等価性は気にしないため、対象の型は [Type]

射全体に対する型は定義せず、対象から [Setoid] への函数と捉える。
射の等価性が重要な要素なので、 Hom 集合ではなく Hom Setoid が色々な場面で活躍する(はず)。
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

  Module Ex.
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
    Notation Id_ C X := (@id C X).
    Notation "'Id' X" := (Id_ _ X) (at level 30, right associativity).
  End Ex.

  Import Ex.

  Definition dom {C: Category}{X Y: C}(f: C X Y): C := X.
  Definition cod {C: Category}{X Y: C}(f: C X Y): C := Y.
  Arguments dom {C X Y} f /.
  Arguments cod {C X Y} f /.
  (**
   *** 圏の双対
[Category.build] のおかげで定義しやすい気がする。
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
Export Category.Ex.

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
 ** 射の等価性
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

(** 
 ** 函手
 **)
Module Functor.
  Class spec (C D: Category)
        (fobj: C -> D)
        (fmap: forall {X Y: C}, Map (C X Y) (D (fobj X) (fobj Y))) :=
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
        fmap: forall X Y: C, Map (C X Y) (D (fobj X) (fobj Y));

        prf: spec (@fmap)
      }.

  Notation build fobj fmap :=
    (@make _ _ fobj (fun _ _ => fmap) (@proof _ _ _ _ _ _))
      (only parsing).

  Module Ex.
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
  End Ex.

  Import Ex.

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

  Program Definition op (C D: Category)(F: Functor C D):
    Functor (Category.op C) (Category.op D) :=
    Functor.build (fun X => F X)
                  ([ f :-> fmap F f]).
  Next Obligation.
    simpl; intros C D F Y X.
    intro; apply Map.substitute.
  Qed.
  Next Obligation.
    simpl; intros C D F Z Y X g f.
    apply fmap_comp.
  Qed.
  Next Obligation.
    simpl; intros C D F X.
    apply fmap_id.
  Qed.
End Functor.
Export Functor.Ex.

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
  eapply eq_Hom_trans.
  - apply eq_Hom_def.
    apply Map.substitute, H.
  - apply HeqG.
Qed.
Next Obligation.
  intros C D K L F G H X Y f; simpl in *.
  apply eq_Hom_refl.
Qed.
Next Obligation.
  intros C D F X Y f; simpl in *.
  apply eq_Hom_refl.
Qed.
Next Obligation.
  intros C D F X Y f; simpl in *.
  apply eq_Hom_refl.
Qed.


(** 
 ** Hom 函手たち
[Hom(X,-)] と [Hom(-,Y)] を作るよ。
[Functor.build] 使うと定義書くのすごく楽。嬉しい。
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


(** 
 ** 自然変換
流れ的にね。
 **)
Module Natrans.
  Class spec
        (C D: Category)
        (F G: Functor C D)
        (natrans: forall X: C, D (F X) (G X)) :=
    naturality:
      forall (X Y: C)(f: C X Y),
        natrans Y \o fmap F f == fmap G f \o natrans X.

  Structure type {C D}(F G: Functor C D) :=
    make {
        natrans (X: C):  D (F X) (G X);
        prf: spec (@natrans)
      }.

  Notation build natrans := (@make _ _ _ _ natrans _).

  Module Ex.
    Notation Natrans := type.
    Notation isNatrans := spec.
    Coercion natrans: Natrans >-> Funclass.
    Coercion prf: Natrans >-> isNatrans.
    Existing Instance prf.

  End Ex.

  Import Ex.

  Section Defs.
    Context (C D: Category).

    Program Definition compose {F G H: Functor C D}
            (S: Natrans F G)(T: Natrans G H): Natrans F H :=
      build (fun X => T X \o S X).
    Next Obligation.
      intros; intros X Y f; simpl.
      eapply transitivity;
        [ apply Category.comp_assoc |].
      eapply transitivity;
        [ apply Category.comp_subst |].
      - apply naturality.
      - apply reflexivity.
      - eapply transitivity;
        [ apply symmetry,Category.comp_assoc |].
        eapply transitivity;
          [ apply Category.comp_subst |].
        + apply reflexivity.
        + apply naturality.
        + apply Category.comp_assoc.
    Qed.

    Program Definition id (F: Functor C D): Natrans F F :=
      build (fun X => Id (F X)).
    Next Obligation.
      intros F X Y f; simpl.
      eapply transitivity;
        [ apply Category.comp_id_cod
        | apply symmetry, Category.comp_id_dom ].
    Qed.

    Program Definition setoid (F G: Functor C D) :=
      Setoid.build (fun (S T: Natrans F G) => forall X: C, S X == T X).
    Next Obligation.
      intros F G S X; apply reflexivity.
    Qed.
    Next Obligation.
      intros F G S T Heq X; generalize (Heq X); apply symmetry.
    Qed.
    Next Obligation.
      intros F G S T U Heq Heq' X;
      generalize (Heq X) (Heq' X); apply transitivity.
    Qed.
  End Defs.
End Natrans.
Export Natrans.Ex.
(** 
 ** 函手圏
 **)
Program Definition Fun (C D: Category) :=
  Category.build (@Natrans.setoid C D)
                 (@Natrans.compose C D)
                 (@Natrans.id C D).
Next Obligation.
  intros C D F G H S S' T T' HeqS HeqT X; simpl.
  apply Category.comp_subst; [apply HeqS | apply HeqT].
Qed.
Next Obligation.
  intros C D F G H I S T U X; simpl in *.
  apply Category.comp_assoc.
Qed.
Next Obligation.
  intros C D F G S X; simpl in *.
  apply Category.comp_id_dom.
Qed.
Next Obligation.
  intros C D F G S X; simpl in *.
  apply Category.comp_id_cod.
Qed.

Notation "[ C :=> D ]" := (Fun C D) (D at level 200): cat_scope.

(** 
 ** 色々な積
 **)
Module Prod.
  Record type (X Y: Type): Type := make { fst: X; snd: Y }.

  Module Ex.
    Notation Prod := type.
    Notation "X * Y" := (Prod X Y).
    Notation "( x , y )" := (@make _ _ x y).
  End Ex.
  Import Ex.
  
  Program Definition setoid (X Y: Setoid) :=
    Setoid.build
      (fun (p q: X * Y) =>
         (fst p == fst q)/\(snd p == snd q)).
  Next Obligation.
    intros X Y [x y]; simpl; split; apply reflexivity.
  Qed.
  Next Obligation.
    intros X Y [x1 y1] [x2 y2]; simpl.
    intros [Heqx Heqy]; split;
    apply symmetry; assumption.
  Qed.
  Next Obligation.
    intros X Y [x1 y1] [x2 y2] [x3 y3]; simpl.
    intros [Heqx12 Heqy12] [Heqx23 Heqy23]; split.
    - apply transitivity with x2; assumption.
    - apply transitivity with y2; assumption.
  Qed.

  Local Infix "[*]" := setoid (at level 40, left associativity).

  Module fst.
    Lemma substitute:
      forall (X Y: Setoid)(p q: X [*] Y),
        p == q -> fst p == fst q.
    Proof.
      intros X Y [x1 y1] [x2 y2] [Heq _]; auto.
    Qed.
  End fst.
    
  Module snd.
    Lemma substitute:
      forall (X Y: Setoid)(p q: X [*] Y),
        p == q -> snd p == snd q.
    Proof.
      intros X Y [x1 y1] [x2 y2] [_ Heq]; auto.
    Qed.
  End snd.

  Lemma substitute:
    forall (X Y: Setoid)(x1 x2: X)(y1 y2: Y),
      x1 == x2 -> y1 == y2 -> (x1, y1) == (x2, y2) :> X [*] Y.
  Proof.
    intros; simpl.
    split; auto.
  Qed.

  Program Definition map {X Y Z W: Setoid}(f: Map X Z)(g: Map Y W):
    Map (X [*] Y) (Z [*] W) :=
    [ p :-> make (f (fst p)) (g (snd p))].
  Next Obligation.
    intros; intros [x1 y1] [x2 y2]; simpl.
    intros [Heqx Heqy]; split; apply Map.substitute; assumption.
  Qed.

  Definition arr {C D: Category}: type C D -> type C D -> Setoid :=
    fun (P Q: C * D) =>
      (C (fst P) (fst Q)) [*] (D (snd P) (snd Q)).

  Definition compose
          {C D: Category}(P Q R: C * D)
          (f: arr P Q)(g: arr Q R): arr P R :=
    make (fst g \o fst f) (snd g \o snd f).

  Definition id {C D: Category}(P: C * D): arr P P :=
    make (Id (fst P)) (Id (snd P)).

  Program Definition category (C D: Category) :=
    Category.build (@arr C D)
                   (@compose C D)
                   (@id C D).
  Next Obligation.
    intros C D [X1 Y1] [X2 Y2] [X3 Y3]; simpl.
    intros [fx fy] [fx' fy'] [gx gy] [gx' gy']; simpl in *.
    intros [Heqfx Heqfy] [Heqgx Heqgy]; split;
    apply Category.comp_subst; assumption.
  Qed.
  Next Obligation.
    intros C D [X1 Y1] [X2 Y2] [X3 Y3] [X4 Y4]; simpl.
    intros [fx fy] [gx gy] [hx hy]; simpl; split;
    apply Category.comp_assoc.
  Qed.
  Next Obligation.
    intros C D [X1 Y1] [X2 Y2] [f g]; simpl in *; split;
    apply Category.comp_id_dom.
  Qed.
  Next Obligation.
    intros C D [X1 Y1] [X2 Y2] [f g]; simpl in *; split;
    apply Category.comp_id_cod.
  Qed.

End Prod.
Export Prod.Ex.
Infix "[*]" := Prod.setoid (at level 40, left associativity).
Infix "[x]" := Prod.category (at level 40, left associativity).


(** 
 ** 米田の補題
有名なアレ
 **)
(**
 *** 評価函手
 **)
Program Definition EvalFunctor (C B: Category)
  : Functor ((Fun C B) [x] C) B :=
  Functor.build (fun FX => let (F,X) := FX in F X)
                ([ Sf :-> let (S,f) := Sf in fmap (Category.cod S) f \o S (Category.dom f)]).
Next Obligation.
  intros C B [F X] [G Y]; simpl.
  intros [S f] [T g]; simpl in *.
  intros [HeqST Heqfg]; apply Category.comp_subst; simpl.
  - apply HeqST.
  - apply Map.substitute, Heqfg.
Qed.
Next Obligation.
  intros C B [F X] [G Y] [H Z]; simpl.
  intros [S f] [T g]; simpl.
  eapply transitivity.
  {
    apply Category.comp_subst; [apply reflexivity |].
    apply Functor.fmap_comp.
  }
  eapply transitivity; [apply Category.comp_assoc |].
  eapply transitivity.
  {
    apply Category.comp_subst; [| apply reflexivity].
    eapply transitivity; [apply symmetry, Category.comp_assoc |].
    apply Category.comp_subst; [apply reflexivity |].
    apply symmetry, Natrans.naturality.
  }
  eapply transitivity.
  {
    apply Category.comp_subst; [| apply reflexivity].
    apply Category.comp_assoc.
  }
  eapply transitivity; [| apply symmetry, Category.comp_assoc].
  apply reflexivity.
Qed.
Next Obligation.
  intros C B [F X]; simpl.
  eapply transitivity; [apply Category.comp_id_dom |].
  apply Functor.fmap_id.
Qed.

Program Definition NFunctor (C: Category)
  : Functor (Fun C Setoids [x] C) Setoids :=
  Functor.build (fun FX => let (F,X) := FX in (Fun C Setoids) Hom(X,-) F)
                ([ Sf alpha :-> let (S,f) := Sf in
                                Natrans.build (fun X => S X \o alpha X \o fmap Hom(-,X) f )]).
Next Obligation.
  intros C [F X] [G Y] [S f] T; simpl in *.
  intros Z W h g; simpl in *.
  eapply symmetry, transitivity.
  {
    generalize (Natrans.naturality (natrans:=S)(f:=h) (T Z (g \o f))).
    intro H; apply symmetry, H.
  }
  simpl.
  apply Map.substitute.
  generalize (Natrans.naturality (natrans:=T)(f:=h) (g \o f)); simpl.
  intro H; apply symmetry.
  eapply transitivity; [| apply H].
  apply Map.substitute; simpl.
  apply Category.comp_assoc.
Qed.
Next Obligation.
  intros C [F X] [G Y] [S f] T U Heq; simpl in *.
  intros Z g; simpl.
  apply Map.substitute, Heq.
Qed.
Next Obligation.
  intros C [F X] [G Y] [S f] [S' f'] [HeqS Heqf]; simpl in *.
  intros T Z g; simpl.
  eapply transitivity; [apply HeqS | apply Map.substitute].
  apply Map.substitute; simpl.
  apply Category.comp_subst;
    [apply Heqf | apply reflexivity].
Qed.
Next Obligation.
  simpl.
  intros C [F X] [G Y] [H Z]; simpl.
  intros [S f] [T g]; simpl.
  intros U W h; simpl.
  do 3 apply Map.substitute; simpl.
  apply symmetry, Category.comp_assoc.
Qed.
Next Obligation.
  simpl.
  intros C [F X] S Y f; simpl in *.
  apply Map.substitute; simpl.
  apply Category.comp_id_dom.
Qed.


Program Definition yoneda (C: Category)
  : Natrans (@NFunctor C) (@EvalFunctor C Setoids) :=
  Natrans.build (fun FX => let (F, X) := FX in [alpha :-> alpha X (Id X)]).
Next Obligation.
  intros C [F X]; simpl.
  intros S T Heq.
  apply (Heq X (Id X)).
Qed.
Next Obligation.
  intros C [F X] [G Y] [S f] T; simpl in *.
  generalize (Natrans.naturality (natrans:=S) (f:=f) (T X (Id X))).
  simpl; intro Heq.
  eapply transitivity; [| apply Heq].
  clear Heq.
  apply Map.substitute.
  generalize (Natrans.naturality (natrans:=T) (f:=f) (Id X)).
  simpl; intro Heq.
  eapply transitivity; [| apply Heq].
  clear Heq.
  apply Map.substitute; simpl.
  eapply transitivity;
    [apply Category.comp_id_cod | apply symmetry, Category.comp_id_dom].
Qed.

Program Definition inv_yoneda (C: Category):
  Natrans (@EvalFunctor C Setoids) (@NFunctor C) :=
  Natrans.build
    (fun FX => let (F,X) := FX in
               [ x :-> Natrans.build (fun Y => [f :-> fmap F f x])]).
Next Obligation.
  intros C [F X]; simpl.
  intros x Y f g Heq.
  assert (HeqF: fmap F f == fmap F g).
  {
    apply Map.substitute, Heq.
  }
  apply (HeqF x).
Qed.
Next Obligation.
  intros C [F X]; simpl.
  intros x Y Z g; simpl.
  intro f.
  apply (Functor.fmap_comp (fobj:=F)(f:=f)(g:=g) x).
Qed.
Next Obligation.
  intros C [F X]; simpl.
  intros x y Heq Y f; simpl.
  apply Map.substitute, Heq.
Qed.
Next Obligation.
  intros C [F X] [G Y] [S f]; simpl in *.
  intros x Z g.
  assert (Heq: fmap G g \o fmap G f \o S X == S Z \o fmap F (g \o f)).
  {
    eapply transitivity; [apply symmetry,Category.comp_assoc |].
    eapply transitivity; [apply symmetry,Category.comp_subst |].
    - apply reflexivity.
    - apply Functor.fmap_comp.
    - apply symmetry,Natrans.naturality.
  }
  apply (Heq x).
Qed.

(** 
 ** 射の同型とか
 **)
Variant Iso (C: Category)(X Y: C): C X Y -> C Y X -> Prop :=
| Iso_def: forall f g, g \o f == Id X -> f \o g == Id Y -> Iso f g.

Definition NaturalIso {C D: Category}{F G: Functor C D}
           (S: Natrans F G): Prop :=
  forall X: C, exists g, Iso (S X) g.

Lemma yoneda_lemma:
  forall (C: Category), NaturalIso (@yoneda C).
Proof.
  intros C [F X]; simpl.
  exists (@inv_yoneda C (F,X)); simpl.
  apply Iso_def; simpl.
  - intros S Y f.
    apply symmetry.
    generalize (Natrans.naturality (natrans:=S)(f:=f)); simpl.
    intro Heq.
    eapply transitivity; [| apply (Heq (Id X))]; simpl.
    apply Map.substitute, symmetry; simpl.
    apply Category.comp_id_dom.
  - apply (Functor.fmap_id (fobj:=F)).
Qed.

(* Next: Grothendieck Functor *)
Program Definition HomNat {C: Category}(X Y: C)(f: C X Y)
  : Natrans Hom(Y,-) Hom(X,-) :=
  Natrans.build (fun Z => [ g :-> g \o f ]).
Next Obligation.
  intros C X Y f Z g g' Heq; simpl in *.
  apply Category.comp_subst; [apply reflexivity | apply Heq].
Qed.
Next Obligation.
  intros C X Y f Z W h g; simpl in *.
  apply Category.comp_assoc.
Qed.


Program Definition GrothFunctor (C: Category)
  : Functor (Category.op C) (Fun C Setoids) :=
  Functor.build
    (fun (X: C) => Hom(X,-))
    ([ f :-> HomNat (f: C _ _)]).
Next Obligation.
  intros C Y X f f' Heq Z g; simpl in *.
  apply Category.comp_subst; [apply Heq | apply reflexivity].
Qed.
Next Obligation.
  simpl.
  intros C Z Y X g f W h.
  apply symmetry, Category.comp_assoc.
Qed.
Next Obligation.
  simpl.
  intros C Y X f; apply Category.comp_id_dom.
Qed.

Module NatransCompose.
  Module Natrans.
    Program Definition dom_compose {C D E: Category}
            (F: Functor C D){G H: Functor D E}(S: Natrans G H)
    : Natrans (G \o{Cat} F) (H \o{Cat} F) :=
      Natrans.build (fun X => S (F X)).
    Next Obligation.
      intros C D E F G H S X Y f; simpl.
      apply Natrans.naturality.
    Qed.

    Program Definition cod_compose {C D E: Category}
            {F G: Functor C D}(H: Functor D E)(S: Natrans F G)
      : Natrans (H \o{Cat} F) (H \o{Cat} G) :=
      Natrans.build (fun X => fmap H (S X) ).
    Next Obligation.
      intros C D E F G H S X Y f; simpl.
      eapply transitivity; 
        [| apply Functor.fmap_comp].
      eapply transitivity; 
        [apply symmetry, Functor.fmap_comp |].
      apply Map.substitute, Natrans.naturality.
    Qed.

    Module Ex.
      Notation "N \oF F" := (dom_compose F N) (at level 55, left associativity).
      Notation "F \Fo N" := (cod_compose F N) (at level 55, left associativity).
    End Ex.
  End Natrans.
End NatransCompose.
Export NatransCompose.
Export NatransCompose.Natrans.Ex.
    
Module Monad.
      Class spec (C: Category)
        (T: Functor C C)
        (eta: Natrans (Id_ Cat C) T)
        (mu: Natrans (T \o{Cat} T) T) :=
    proof {
        mu_mu:
          forall X: C,
            mu X \o fmap T (mu X) == mu X \o mu (T X);
        etaT_mu:
          forall X: C,
            mu X \o eta (T X) == Id (T X);
        Teta_mu:
          forall X: C,
            mu X \o fmap T (eta X) == Id (T X)
      }.
  
  Structure type (C: Category) :=
    make {
        T: Functor C C;
        eta: Natrans (Functor.id (C:=C)) T;
        mu: Natrans (Functor.compose T T) T;

        prf: spec eta mu
      }.

  Notation build t eta mu :=
    (@make _ t eta mu (@proof _ _ _ _ _ _ _)).
  
  Module Ex.
    Notation isMonad := spec.
    Notation Monad := type.
    Arguments eta {C}(Monad): rename.
    Arguments mu {C}(Monad): rename.

    Coercion T: Monad >-> Functor.
    Coercion prf: Monad >-> isMonad.
    Existing Instance prf.

    Notation μ := mu.
    Notation η := eta.
  End Ex.
  Import Ex.

  Program Definition category {C: Category}(m: Monad C):=
    Category.build (fun X Y => C X (m Y))
                   (fun X Y Z f g => mu m Z \o fmap m g \o f)
                   (eta m).
  Next Obligation.
    intros C m X Y Z f f' g g' Heqf Heqg; simpl.
    apply Category.comp_subst; [| apply reflexivity].
    apply Category.comp_subst; [apply Heqf | apply Map.substitute,Heqg].
  Qed.
  Next Obligation.
    simpl; intros.
    (* mu W \o T (mu W \o T h \o g) \o f
     = mu W \o T (mu W) \o TT h \o T g \o f 
     = mu W \o mu (T W) \o TT h \o T g \o f
     = mu W \o T h \o mu Z \o T g \o f
     = mu W \o T h \o mu Z \o T g \o f
     *)
    eapply transitivity.
    { apply Category.comp_subst; [| apply reflexivity].
      apply Category.comp_subst; [apply reflexivity |].
      eapply transitivity; [apply Functor.fmap_comp |].
      apply Category.comp_subst; [| apply reflexivity].
      apply Functor.fmap_comp. }
    eapply transitivity.
    { eapply transitivity; [apply symmetry, Category.comp_assoc |].
      apply Category.comp_subst; [apply reflexivity |].
      eapply transitivity; [apply symmetry, Category.comp_assoc |].
      apply Category.comp_subst; [apply reflexivity |].
      apply mu_mu. }
    eapply transitivity.
    { eapply transitivity; [apply Category.comp_assoc |].
      eapply transitivity; [apply Category.comp_assoc |].      
      apply Category.comp_subst; [| apply reflexivity].
      eapply transitivity; [apply symmetry, Category.comp_assoc |].      
      apply Category.comp_subst; [apply reflexivity |].
      eapply transitivity; [apply symmetry,Category.comp_assoc |].
      apply Category.comp_subst; [apply reflexivity |].
      generalize (Natrans.naturality (natrans:=mu m)(f:=h)); simpl.
      intro H; apply H. }
    apply Category.comp_subst; [| apply reflexivity].
    eapply transitivity; apply Category.comp_assoc.    
  Qed.
  Next Obligation.
    simpl; intros.
    eapply transitivity; [apply Category.comp_subst |].    
    - apply symmetry,(Natrans.naturality (natrans:=eta m)).
    - apply reflexivity.
    - simpl.
      eapply transitivity; [apply symmetry,Category.comp_assoc |].
      eapply transitivity; [| apply Category.comp_id_cod].
      apply Category.comp_subst; [apply reflexivity |].
      apply etaT_mu.
  Qed.
  Next Obligation.
    simpl; intros.
    eapply transitivity; [| apply Category.comp_id_cod].
    eapply transitivity; [apply symmetry,Category.comp_assoc |].
    apply Category.comp_subst; [apply reflexivity |].
    apply Teta_mu.
  Qed.

End Monad.
Export Monad.Ex.


Module MPL.
  Class spec (C D: Category)
        (monad: Monad C)
        (pred: Functor (Category.op C) D)
        (tau: Natrans pred (Functor.compose (Functor.op monad) pred)) :=
    proof {
        tau_pred_eta:
          forall X: C,
            fmap pred (Monad.eta monad X) \o tau X == Id (pred X);
        tau_pred_mu:
          forall X: C,
            fmap pred (Monad.mu monad X) \o tau X == tau (monad X) \o tau X
          
      }.
  
  Structure type (C D: Category) :=
    make {
        monad: Monad C;
        pred: Functor (Category.op C) D;
        tau: Natrans pred (Functor.compose (Functor.op monad) pred);

        prf: spec tau
      }.

  Notation build monad pred tau :=
    (@make _ _ monad pred tau (@proof _ _ _ _ _ _ _)).

  Module Ex.
    Notation isMPL := spec.
    Notation MPL := type.

    Coercion monad: MPL >-> Monad.
    Coercion prf: MPL >-> isMPL.
    Existing Instance prf.

    Arguments pred {C D}(mpl): rename.
    Arguments tau {C D}(mpl): rename.

    Notation Φ := pred.
    Notation τ := tau.

  End Ex.
  Import Ex.

  Program Definition functor {C D: Category}(mpl: MPL C D)
    : Functor (Category.op (Monad.category mpl)) D :=
    Functor.build (fun X => pred mpl X)
                  ([f :-> fmap (pred mpl) f \o{D} tau mpl (Category.dom f)]).
  Next Obligation.
    simpl; intros C D mpl Y X f g Heq; simpl in *.
    apply Category.comp_subst; [apply reflexivity |].
    apply Map.substitute, Heq.
  Qed.
  Next Obligation.
    simpl; intros C D mpl Z Y X g f.
    eapply transitivity.
    { apply Category.comp_subst; [apply reflexivity |].
      apply (Functor.fmap_comp (spec:=pred mpl)). }
    eapply transitivity; [apply Category.comp_assoc |].
    eapply transitivity.
    { apply Category.comp_subst; [| apply reflexivity].
      apply (tau_pred_mu (spec:=mpl)). }
    eapply transitivity; [apply symmetry, Category.comp_assoc |].
    eapply transitivity.
    { apply Category.comp_subst; [apply reflexivity |].
      apply Category.comp_subst; [apply reflexivity |].
      apply (Functor.fmap_comp (spec:=pred mpl)). }
    eapply transitivity; [apply Category.comp_assoc |].
    eapply transitivity; [apply Category.comp_assoc |].
    eapply transitivity.
    { apply Category.comp_subst; [| apply reflexivity].
      eapply transitivity; [apply symmetry,Category.comp_assoc |].
      apply Category.comp_subst; [apply reflexivity |].
      apply symmetry, (Natrans.naturality (natrans:=tau mpl) (f:=g)). }
    eapply transitivity; [apply symmetry,Category.comp_assoc |].
    eapply transitivity.
    { apply Category.comp_subst; [apply reflexivity |].
      apply symmetry, Category.comp_assoc. }
    apply Category.comp_assoc.
  Qed.
  Next Obligation.
    simpl; intros C D mpl X.
    apply tau_pred_eta.
  Qed.
End MPL.
Export MPL.Ex.

Module Rel.
  Class spec (X: Setoid)(R: relation X) :=
    rel_subst:
      forall (x x' y y': X),
        x == x' -> y == y' -> R x y -> R x' y'.

  Structure type (X: Setoid) :=
    make {
        rel: relation X;
        prf: spec X rel
      }.

  Notation build rel := (@make _ rel _).

  Module Ex.
    Notation isRel := spec.
    Notation Rel := type.

    Arguments rel {X Rel}(x y): rename.
    Coercion rel: Rel >-> Funclass.
    Coercion prf: Rel >-> isRel.
    Existing Instance prf.
  End Ex.
End Rel.
Export Rel.Ex.

Class Antisymmetric `(R: Rel X) :=
  antisymmetric:
    forall (x y: X),
      R x y -> R y x -> x == y.

Class PartialOrder `(R: Rel X) :=
  {
    pord_refl:> Reflexive R;
    pord_asym:> Antisymmetric R;
    pord_trans:> Transitive R
  }.
Existing Instance pord_refl.
Existing Instance pord_asym.
Existing Instance pord_trans.

Variant True: Prop := I .
Hint Resolve I.
Variant Fale: Prop :=.

Program Definition PropSetoid (P: Prop) :=
  Setoid.build (fun (p q: P) => True).
Next Obligation.
  intros P _; auto.
Qed.
Next Obligation.
  intros P _ _; auto.
Qed.
Next Obligation.
  intros P _ _ _; auto.
Qed.

Module Poset.

  Structure type :=
    make {
        carrier: Setoid;
        pord: Rel carrier;
        prf: PartialOrder pord
      }.

  Notation build pord :=
    (@make _ (@Rel.build pord) (@Build_PartialOrder _ _ _ _ _)).
  
  Module Ex.
    Notation isPoset := PartialOrder.
    Notation Poset := type.

    Infix "<=" := (pord _) (at level 70, no associativity).
    Coercion carrier: Poset >-> Setoid.
    Coercion prf: Poset >-> isPoset.
    Existing Instance prf.
  End Ex.
  Import Ex.
  
  Definition arr (P: Poset)(p q: P) := p <= q.
  Definition compose (P: Poset)(p q r: P)
    : arr p q -> arr q r -> arr p r :=
    fun Hpq Hqr => pord_trans (R:=pord P) Hpq Hqr.

  Definition id (P: Poset)(p: P): arr p p :=
    pord_refl (R:=pord P).
  
  Program Definition category (P: type) :=
    Category.build (fun p q => PropSetoid (p <= q))
                   (@compose P)
                   (@id P).
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    simpl; auto.
  Qed.
  Next Obligation.
    simpl; auto.
  Qed.


End Poset.
Export Poset.Ex.



Module Monomap.
  Class spec (P Q: Poset)(f: Map P Q) :=
    monotone:
      forall (p q: P),
        p <= q -> f p <= f q.

  Structure type (P Q: Poset):=
    make {
        map: Map P Q;
        prf: spec P Q map
      }.

  Notation build map := (@make _ _ map _).
  Module Ex.
    Notation isMonomap := spec.
    Notation Monomap := type.

    Coercion map: Monomap >-> Map.
    Coercion prf: Monomap >-> isMonomap.
    Existing Instance prf.
  End Ex.
  Import Ex.


  Program Definition setoid (P Q: Poset) :=
    Setoid.build (fun (f g: Monomap P Q) => Map.equal f g).
  Next Obligation.
    intros P Q f x; apply reflexivity.
  Qed.
  Next Obligation.
    intros P Q f g Heq x; generalize (Heq x); apply symmetry.
  Qed.
  Next Obligation.
    intros P Q f g h Heqfg Heqgh x;
    generalize (Heqfg x) (Heqgh x); apply transitivity.
  Qed.

  Program Definition compose {P Q R: Poset}
          (f: Monomap P Q)(g: Monomap Q R): Monomap P R :=
    build (Map.compose f g).
  Next Obligation.
    intros P Q R f g p q Hpord; simpl.
    do 2 apply monotone; auto.
  Qed.

  Program Definition id (P: Poset): Monomap P P :=
    build (Map.id (X:=P)).
  Next Obligation.
    intros P p q Hpord; simpl; auto.
  Qed.

  Program Definition category :=
    Category.build setoid (@compose) (@id).
  Next Obligation.
    simpl; intros.
    apply (Category.comp_subst (spec:=Setoids)); auto.
  Qed.
  Next Obligation.
    intros; apply (Category.comp_assoc (spec:=Setoids)).
  Qed.
  Next Obligation.
    intros; apply (Category.comp_id_dom (spec:=Setoids)).
  Qed.
  Next Obligation.
    intros; apply (Category.comp_id_cod (spec:=Setoids)).
  Qed.

End Monomap.
Import Monomap.Ex.

Definition Posets := Monomap.category.  

Module Pred.
  Class spec (X: Setoid)(P: predicate X) :=
    substitute:
      forall (x y: X),
        x == y -> P x -> P y.

  Structure type (X: Setoid) :=
    make {
        pred: predicate X;
        prf: spec X pred
      }.

  Notation build pred := (@make _ pred _).
  Module Ex.
    Notation isPred := spec.
    Notation Pred := type.

    Notation "{ x | P }" := (build (fun x => P)).
    Coercion pred: Pred >-> Funclass.
    Coercion prf: Pred >-> isPred.
    Existing Instance prf.
  End Ex.
  Import Ex.

  Program Definition setoid (X: Setoid) :=
    Setoid.build (fun (P Q: Pred X) => forall x, P x <-> Q x).
  Next Obligation.
    intros X P x.
    split; auto.
  Qed.  
  Next Obligation.
    intros X P Q H x; split; apply H.
  Qed.  
  Next Obligation.
    intros X P Q R Hpq Hqr x; split.
    - intro Hp; apply Hqr, Hpq, Hp.
    - intro Hr; apply Hpq, Hqr, Hr.
  Qed.  

  Definition rel {X: Setoid}(P Q: setoid X) :=
    forall x: X, P x -> Q x.

  Program Definition poset (X: Setoid) :=
    Poset.build (@rel X).
  Next Obligation.
    intros X P Q R S Hpq Hrs; simpl in *.
    intros Hpr x Hq.
    apply Hrs, Hpr, Hpq, Hq.
  Qed.  
  Next Obligation.
    intros X P x; auto.
  Qed.  
  Next Obligation.
    intros X P Q Hpq Hqp x.
    split; auto.
  Qed.  
  Next Obligation.
    intros X P Q R Hpq Hqr x; auto.
  Qed.

  Program Definition sub {X Y: Setoid}(f: Map X Y)(Q: Pred Y)
    : Pred X :=
    { x | Q (f x)}.
  Next Obligation.
    intros X Y f Q x y Heq.
    apply substitute, Map.substitute; auto.
  Qed.
  
  Program Definition functor
    : Functor (Category.op Setoids) Posets :=
    Functor.build (fun (X: Setoid) => poset X)
                  ([f :-> Monomap.build ([Q :-> sub f Q])]).
  Next Obligation.
    simpl.
    intros Y X f Q Q' H x; simpl.
    apply H.
  Qed.
  Next Obligation.
    simpl.
    intros Y X f Q Q' H x; simpl in *.
    apply H.
  Qed.
  Next Obligation.
    simpl.
    intros Y X f g Heq Q y; simpl in *.
    split; apply substitute; [| apply symmetry]; apply Heq.
  Qed.
  Next Obligation.
    simpl.
    intros Z Y X g f R x; simpl; split; auto.
  Qed.
  Next Obligation.
    simpl.
    intros X P x; simpl; split; auto.
  Qed.
End Pred.
Export Pred.Ex.

Module Maybe.

  Variant type (X: Type): Type :=
  | some (x: X) | none.

  Module Ex.
    Notation option := type.
  End Ex.
  Import Ex.

  Definition equal (X: Setoid)(mx my: option X) :=
    match mx, my with
    | some x, some y => x == y
    | none, none => True
    | _, _ => False
    end.
  Program Definition setoid (X: Setoid) :=
    Setoid.build (@equal X).
  Next Obligation.
    intros X [x|]; simpl; auto.
    apply reflexivity.
  Qed.
  Next Obligation.
    intros X [x|] [y|] Heq; simpl in *; auto.
    apply symmetry, Heq.
  Qed.
  Next Obligation.
    intros X [x|] [y|] [z|]; simpl in *; auto.
    - apply transitivity.
    - intro H; elim H.
  Qed.
  
  Program Definition map (X: Setoid): Map X (setoid X) :=
    [ x :-> some x ].
  Next Obligation.
    intros X x y Heq; simpl; auto.
  Qed.

  Definition fmap {X Y: Type}
    : (X -> Y) -> (option X) -> (option Y) :=
    fun f mx => match mx with
                | some x => some (f x)
                | none => none
                end.

  Program Definition functor
    : Functor Setoids Setoids :=
    Functor.build setoid ([ f mx :-> fmap f mx]).
  Next Obligation.
    intros X Y f [x|] [y|]; simpl; auto.
    apply Map.substitute.
  Qed.
  Next Obligation.
    intros X Y f g Heq [x|]; simpl; auto.
  Qed.
  Next Obligation.
    intros X Y Z f g [x|]; simpl; auto.
    apply reflexivity.
  Qed.
  Next Obligation.
    intros X [x|]; simpl; auto.
    apply reflexivity.
  Qed.

  Definition mu (X: Type)(mmx: option (option X)): option X :=
    match mmx with
    | some mx => mx
    | none => none
    end.
  Program Definition monad :=
    Monad.build functor
                (Natrans.build (fun X => map))
                (Natrans.build (fun X => [mmx :-> mu mmx])).
  Next Obligation.
    intros X Y f x; simpl.
    apply reflexivity.
  Qed.
  Next Obligation.
    intros X [[x|]|] [[y|]|]; simpl in *; auto.
  Qed.
  Next Obligation.
    intros X Y f [[x|]|]; simpl in *; auto.
    apply reflexivity.
  Qed.
  Next Obligation.
    simpl.
    intros X [[[x|]|]|]; simpl; auto.
    apply reflexivity.
  Qed.
  Next Obligation.
    simpl.
    intros X [x|]; simpl; auto.
    apply reflexivity.
  Qed.
  Next Obligation.
    simpl.
    intros X [x|]; simpl; auto.
    apply reflexivity.
  Qed.

  Definition pred (X: Type)(P: predicate X): predicate (option X) :=
    fun mx => match mx with
              | some x => P x
              | none => False
              end.
  Program Definition natrans
    : Natrans Pred.functor
              (Functor.compose (Functor.op monad) Pred.functor) :=
    Natrans.build (fun (X: Setoids) =>
                     Monomap.build
                       ([ P :-> { mp | pred P mp }])).
  Next Obligation.
    intros X P; simpl in *.
    intros [x|] [y|]; simpl; auto.
    - apply Pred.substitute.
    - intros.
      elim H.
  Qed.
  Next Obligation.
    intros X P Q Hpq [x|]; simpl in *; auto.
    split; auto.
  Qed.
  Next Obligation.
    intros X P Q Hpq [x|]; simpl in *; auto.
  Qed.
  Next Obligation.
    simpl.
    intros Y X f; simpl in *; auto.
    intros Q [x |]; simpl; split; auto.
  Qed.
  Check (MPL.make (C:=Setoids)(D:=Posets)
                  (pred:=Pred.functor)).

  Program Definition mpl: MPL Setoids Posets :=
    MPL.build monad Pred.functor natrans.
  Next Obligation.
    simpl.
    intros X P x; simpl.
    split; auto.
  Qed.
  Next Obligation.
    intros X P [[x|]|]; simpl; split; auto.
  Qed.

End Maybe.
Export Maybe.Ex.

Module Pointed.
  Structure type :=
    make {
        carrier: Setoid;
        point: carrier
      }.

  Module Ex.
    Notation PSetoid := type.

    Coercion carrier: PSetoid >-> Setoid.
  End Ex.
  Import Ex.

  (*
  Program Definition pred (S: PSetoid)(X: Setoid) := Pred.poset (X [*] S).
  Program Definition sub (S: PSetoid){X Y: Setoid}(f: Map X Y)
    : Monomap (pred S X) (pred S Y) :=
    Monomap.build (Pred.sub (Prod.map f (Map.id (X:=S)))).
   *)
  Program Definition functor (S: PSetoid)
    : Functor (Category.op Setoids) Posets :=
    Functor.build (fun X => Pred.functor (X [*] S))
                  ([ f :->
                       fmap Pred.functor (Prod.map f (Map.id (X:=S)))]).
  Next Obligation.
    intros S Y X f g Heq Q [x s]; simpl in *.
    split; apply Pred.substitute.
    - apply Prod.substitute; [apply Heq | apply reflexivity].
    - apply Prod.substitute; [apply symmetry,Heq | apply reflexivity].
  Qed.
  Next Obligation.
    intros S Z Y X g f; simpl in *.
    intros R [x s]; simpl.
    split; auto.
  Qed.
  Next Obligation.
    intros S X P [x s]; simpl in *.
    split; auto.
  Qed.

End Pointed.
Export Pointed.Ex.

Module State.

  Definition type (S: PSetoid)(X: Setoid) := Map S (X [*] S).

  Module Ex.
    Notation State := type.
  End Ex.
  Import Ex.

  Definition setoid (S: PSetoid)(X: Setoid): Setoid :=
    Map.setoid S (X [*] S).

  Program Definition functor (S: PSetoid)
    : Functor Setoids Setoids :=
    Functor.build (fun X => setoid S X)
                  ([ f mx s :-> let (x,s') := mx s in (f x, s')]).
  Next Obligation.
    intros S X Y f mx s s' Heqs; simpl.
    assert (Heq: mx s == mx s').
    {
      apply Map.substitute,Heqs.
    }
    destruct (mx s), (mx s'); simpl in Heq.
    split; [apply Map.substitute |]; apply Heq.
  Qed.
  Next Obligation.
    intros S X Y f k k' Heqk s; simpl in *.
    generalize (Heqk s); simpl; intros [Heqfst Heqsnd].
    destruct (k s), (k' s); simpl in *.
    split; [apply Map.substitute |]; assumption.
  Qed.
  Next Obligation.
    intros S X Y f f' Heqf k s; simpl in *.
    destruct (k s).
    split; [apply Heqf | apply reflexivity].
  Qed.
  Next Obligation.
    simpl.
    intros S X Y Z f g k s.
    destruct (k s).
    split; apply reflexivity.
  Qed.
  Next Obligation.
    simpl.
    intros S X k s.
    destruct (k s); simpl.
    split; apply reflexivity.
  Qed.

  Program Definition monad (S: PSetoid): Monad Setoids :=
    Monad.build (functor S)
                (Natrans.build (fun X => [x s :-> (x,s)]))
                (Natrans.build (fun X => [m s :->
                                            let (f,x) := m s in
                                            f x])).
  Next Obligation.
    intros S X x s s' Heq; simpl in *.
    split; [apply reflexivity | assumption].
  Qed.
  Next Obligation.
    intros S X x y Heq s; simpl in *.
    split; [assumption | apply reflexivity].
  Qed.
  Next Obligation.
    intros S X Y f; simpl.
    intros x s; split; apply reflexivity.
  Qed.
  Next Obligation.
    simpl.
    intros S X k s s' Heq.
    assert (Heqk: k s == k s') by apply Map.substitute,Heq.
    destruct (k s), (k s'); simpl in *.
    destruct Heqk as [Heqk Heqsnd].
    split.
    - eapply transitivity.
      + apply (Heqk snd).
      + apply Prod.fst.substitute, Map.substitute, Heqsnd.
    - eapply transitivity.
      + apply (Heqk snd).
      + apply Prod.snd.substitute, Map.substitute, Heqsnd.
  Qed.
  Next Obligation.
    intros S X k k' Heqk s; simpl.
    assert (Heqks: k s == k' s) by apply (Heqk s).
    destruct (k s), (k' s); simpl in *.
    destruct Heqks as [Heqks Heqsnd].
    split.
    - eapply transitivity.
      + apply (Heqks snd).
      + apply Prod.fst.substitute, Map.substitute, Heqsnd.
    - eapply transitivity.
      + apply (Heqks snd).
      + apply Prod.snd.substitute, Map.substitute, Heqsnd.
  Qed.
  Next Obligation.
    intros S X Y f k s; simpl in *.
    destruct (k s); simpl.
    destruct (fst snd); simpl.
    split; apply reflexivity.
  Qed.
  Next Obligation.
    intros S X kk s; simpl in *.
    destruct (kk s) as [k s'], (k s') as [f s''].
    split; apply reflexivity.
  Qed.
  Next Obligation.
    intros S X k s; simpl in *.
    split; apply reflexivity.
  Qed.
  Next Obligation.
    intros S X k s; simpl in *.
    destruct (k s); simpl.
    split; apply reflexivity.
  Qed.


  Program Definition natrans (S: PSetoid)
    : Natrans (Pointed.functor S)
              (Functor.compose (Functor.op (monad S))
                               (Pointed.functor S)) :=
    Natrans.build (fun (X: Setoids) =>
                     Monomap.build
                       ([ P :-> { m | let (k,s) := m in P (k s) }])).
  Next Obligation.
    simpl.
    intros S X P [k s] [k' s']; simpl.
    intros [Heqk Heqs].
    apply Pred.substitute.
    apply transitivity with (k s').
    - apply Map.substitute, Heqs.
    - apply Heqk.
  Qed.
  Next Obligation.
    simpl.
    intros S X P Q Heq [k s]; simpl.
    apply Heq.
  Qed.
  Next Obligation.
    simpl.
    intros S X P Q Hpor [k s]; simpl.
    apply Hpor.
  Qed.
  Next Obligation.
    simpl.
    intros S Y X f Q [k s]; simpl in *.
    destruct (k s) as [x s']; simpl.
    split; auto.
  Qed.
  
  Program Definition mpl (S: PSetoid)
    : MPL Setoids Posets :=
    MPL.build (monad S)
              (Pointed.functor S)
              (@natrans S).
  Next Obligation.
    simpl.
    intros S X P [x s]; simpl.
    split; auto.
  Qed.
  Next Obligation.
    simpl.
    intros S X P [kk s]; simpl.
    split; auto.
  Qed.
End State.
Export State.Ex.


Module KT.
  Class spec (C: Category)
        (T: C -> C)
        (ret: forall (X: C), C X (T X))
        (bind: forall {X Y: C}, C X (T Y) -> C (T X) (T Y)) :=
    proof {
        bind_isMap: forall X Y: C, isMap (@bind X Y);
        bind_ret:
          forall (X: C), bind (ret X) == Id (T X);

        ret_comp_bind:
          forall (X Y: C)(f: C X (T Y)),
            bind f \o ret X == f;

        bind_comp:
          forall (X Y Z: C)(f: C X (T Y))(g: C Y (T Z)),
            bind g \o bind f == bind (bind g \o f)
      }.

  Structure type (C: Category) :=
    make {
        T: C -> C;
        ret: forall (X: C), C X (T X);
        bind: forall {X Y: C}, C X (T Y) -> C (T X) (T Y);

        prf: spec (@ret) (@bind)
      }.

  Notation build T ret bind :=
    (@make _ T ret bind (@proof _ _ _ _ _ _ _ _)).

  Module Ex.
    Notation isKT := spec.
    Notation KT := type.

    Coercion T: KT >-> Funclass.
    Coercion prf: KT >-> isKT.
    Existing Instance bind_isMap.
    Existing Instance prf.
  End Ex.

End KT.
Export KT.Ex.

Module KPL.
  Class spec
        (C D: Category)
        (kt: KT C)
        (pred: C -> D)
        (modal: forall {X Y: C}, C X (kt Y) -> D (pred Y) (pred X)) :=
    proof {
        modal_isMap: forall X Y: C, isMap (@modal X Y);

        modal_ret:
          forall (X: C), modal (KT.ret (X:=X)) == Id (pred X);
        modal_bind:
          forall (X Y Z: C)(f: C X (kt Y))(g: C Y (kt Z)),
            modal (KT.bind g \o f) == modal f \o modal g
      }.

  Structure type (C D: Category) :=
    make {
        kt: KT C;
        pred: C -> D;
        modal: forall {X Y: C}, C X (kt Y) -> D (pred Y) (pred X);

        prf: spec (@modal)
      }.

  Notation build kt pred modal :=
    (@make _ _ kt pred modal (@proof _ _ _ _ _ _ _ _)).

  Module Ex.
    Notation isKPL := spec.
    Notation KPL := type.

    Coercion kt: KPL >-> KT.
    Coercion prf: KPL >-> isKPL.
    Notation "[]" := modal.
    Existing Instance prf.
    Existing Instance modal_isMap.
  End Ex.
End KPL.
Export KPL.Ex.

Definition Maybebind (X Y: Type)(f: X -> option Y)(mx: option X) :=
  match mx with
  | Maybe.some x => f x
  | Maybe.none => Maybe.none
  end.

Program Definition MaybeKT: KT Setoids :=
  KT.build Maybe.setoid
           (fun X => Maybe.map (X:=X))
           (fun X Y f => [ mx :-> Maybebind f mx]).
Next Obligation.
  simpl.
  intros X Y f [x|] [x'|] Heq; simpl in *; try elim Heq; auto.
  assert (Heqf: f x == f x') by apply Map.substitute, Heq.
  destruct (f x) as [y|], (f x') as [y'|]; simpl; auto.
Qed.
Next Obligation.
  simpl.
  intros X Y f g Heq [x|]; simpl; auto.
  generalize (Heq x); intro Heqx.
  destruct (f x) as [y|], (g x) as [y'|]; simpl in *; auto.
Qed.
Next Obligation.
  intros X [x|]; simpl; auto.
  apply reflexivity.
Qed.
Next Obligation.
  intros X Y f x; simpl.
  destruct (f x) as [y|]; simpl; auto.
  apply reflexivity.
Qed.
Next Obligation.
  simpl.
  intros X Y Z f g [x|]; simpl; auto.
  destruct (f x) as [y|]; simpl; auto.
  destruct (g y) as [z|]; simpl; auto.
  apply reflexivity.
Qed.

Program Definition MaybeKPL: KPL Setoids Posets :=
  KPL.build MaybeKT
            (fun X => Pred.poset X)
            (fun X Y (f: Map X (Maybe.setoid Y)) =>
               Monomap.build ([Q :-> { x | Maybe.pred Q (f x)}])).
Next Obligation.
  simpl.
  intros X Y f Q x x' Heq.
  assert (Heqf: f x == f x') by apply Map.substitute, Heq.
  destruct (f x) as [y|], (f x') as [y'|]; simpl in *; try auto.
  - apply Pred.substitute, Heqf.
  - elim Heqf.
Qed.
Next Obligation.
  simpl.
  intros X Y f Q Q' Heq x; simpl.
  destruct (f x) as [y|]; simpl; split; auto; apply Heq.
Qed.
Next Obligation.
  simpl.
  intros X Y f Q Q' Hpord x; simpl in *.
  destruct (f x) as [y|]; simpl; auto.
Qed.
Next Obligation.
  simpl.
  intros X Y f g Heq Q x; simpl.
  assert (Heqf: f x == g x) by apply Heq.
  clear Heq.
  destruct (f x) as [y|], (g x) as [y'|]; simpl in *; split;
  try elim Heqf; auto.
  - apply Pred.substitute, Heqf.
  - apply Pred.substitute, symmetry, Heqf.
Qed.
Next Obligation.
  simpl.
  intros X P x; simpl; split; auto.
Qed.
Next Obligation.
  simpl.
  intros X Y Z f g R x; simpl.
  destruct (f x) as [y|]; simpl; split; auto.
Qed.


Module MonadKT.
  Module Monad.
    Program Definition kt {C: Category}(monad: Monad C): KT C :=
      KT.build (Functor.fobj monad)
               (fun X => Monad.eta monad X)
               (fun X Y f => Monad.mu monad _ \o fmap monad f).
    Next Obligation.
      simpl.
      intros C m X Y f g Heq.
      apply Category.comp_subst;
        [apply Map.substitute,Heq | apply reflexivity].
    Qed.
    Next Obligation.
      simpl.
      intros C m X.
      apply Monad.Teta_mu.
    Qed.
    Next Obligation.
      simpl.
      intros C m X Y f.
      eapply transitivity; [apply Category.comp_assoc |].
      eapply transitivity; [apply Category.comp_subst |].
      - apply symmetry, (Natrans.naturality (natrans:=Monad.eta m)).
      - apply reflexivity.
      - simpl.
        eapply transitivity; [apply symmetry,Category.comp_assoc |].
        eapply transitivity;
          [apply Category.comp_subst | apply Category.comp_id_cod].
        + apply reflexivity.
        + apply Monad.etaT_mu.
    Qed.
    Next Obligation.
      simpl.
      intros C m X Y Z f g.
      eapply transitivity; [apply Category.comp_assoc |].
      eapply transitivity; [apply Category.comp_subst |].
      - eapply transitivity; [apply symmetry, Category.comp_assoc |].
        apply Category.comp_subst; [apply reflexivity |].
        apply symmetry, (Natrans.naturality (natrans:=Monad.mu m)).
      - apply reflexivity.
      - simpl.
        eapply transitivity; [apply symmetry,Category.comp_assoc |].
        eapply transitivity; [apply Category.comp_subst |].
        + apply reflexivity.
        + eapply transitivity; [apply symmetry,Category.comp_assoc |].
          apply Category.comp_subst; [apply reflexivity |].
          apply symmetry, Monad.mu_mu.
        + eapply transitivity; [apply Category.comp_assoc |].
          eapply transitivity; [apply Category.comp_assoc |].
          apply Category.comp_subst; [| apply reflexivity].
          apply symmetry.
          eapply transitivity; [apply Functor.fmap_comp |].
          eapply transitivity; [| apply Category.comp_assoc].
          apply Category.comp_subst;
            [apply reflexivity | apply Functor.fmap_comp].
    Qed.
  End Monad.

  Module KT.
    (* Program Definition functor {C: Category}(kt: KT C) *)
    (* : Functor C C := *)
    (*   Functor.build kt ([f :-> KT.bind (KT.ret \o f)]). *)
    (* Next Obligation. *)
    (*   intros C kt X Y f g Heq. *)
    (*   apply Map.substitute. *)
    
    (* Program Definition eta {C: Category}(kt: KT C) *)
    (* : Natrans (Functor.id (C:=C)) (KT.T kt) := *)
    (*   (Natrans.build (fun X => KT.ret (X:=X))). *)

    Program Definition monad {C: Category}(kt: KT C): Monad C :=
      Monad.build
        (Functor.build kt ([f :-> KT.bind (KT.ret \o f)]))
        (Natrans.build (fun X => KT.ret (X:=X)))
        (Natrans.build (fun X => KT.bind (Id (kt X)))).
    Next Obligation.
      simpl.
      intros C kt X Y f f' Heq; simpl.
      apply Map.substitute.
      apply Category.comp_subst; [apply Heq | apply reflexivity].
    Qed.
    Next Obligation.
      simpl.
      intros C kt X Y Z f g.
      apply symmetry.
      eapply transitivity; [apply KT.bind_comp |].
      apply Map.substitute.
      eapply transitivity; [| apply Category.comp_assoc].
      eapply transitivity; [apply symmetry,Category.comp_assoc |].
      apply Category.comp_subst; [apply reflexivity |].
      eapply transitivity; [apply KT.ret_comp_bind |].
      apply reflexivity.
    Qed.
    Next Obligation.
      simpl.
      intros C kt X.
      eapply transitivity;
        [apply Map.substitute | apply KT.bind_ret].
      apply Category.comp_id_dom.
    Qed.
    Next Obligation.
      simpl.
      intros C kt X Y f; simpl.
      apply symmetry, KT.ret_comp_bind.
    Qed.
    Next Obligation.
      intros C kt X Y f; simpl.
      eapply transitivity; [apply KT.bind_comp |].
      eapply transitivity; [| apply symmetry, KT.bind_comp].
      apply Map.substitute; simpl.
      eapply transitivity; [apply symmetry, Category.comp_assoc |].
      eapply transitivity; [apply Category.comp_subst |].
      - apply reflexivity.
      - apply KT.ret_comp_bind.
      - eapply transitivity;
        [apply Category.comp_id_cod
        | apply symmetry, Category.comp_id_dom].
    Qed.
    Next Obligation.
      simpl.
      intros C kt X.
      eapply transitivity; [apply KT.bind_comp |].
      eapply transitivity; [| apply symmetry, KT.bind_comp].
      apply Map.substitute; simpl.
      eapply transitivity; [apply symmetry, Category.comp_assoc |].
      eapply transitivity; [apply Category.comp_subst |].
      - apply reflexivity.
      - apply KT.ret_comp_bind.
      - eapply transitivity;
        [apply Category.comp_id_cod
        | apply symmetry, Category.comp_id_dom].
    Qed.
    Next Obligation.
      simpl.
      intros C kt X.
      apply KT.ret_comp_bind.
    Qed.
    Next Obligation.
      simpl.
      intros C kt X.
      eapply transitivity; [apply KT.bind_comp |].
      eapply transitivity;
        [apply Map.substitute | apply KT.bind_ret].
      eapply transitivity; [apply symmetry, Category.comp_assoc |].
      eapply transitivity;
        [apply Category.comp_subst | apply Category.comp_id_cod].
      - apply reflexivity.
      - apply KT.ret_comp_bind.
    Qed.
  End KT.
  (* W.I.P *)

  Module MPL.
    Program Definition kpl {C D: Category}(mpl: MPL C D): KPL C D :=
      KPL.build (Monad.kt mpl)
                (MPL.pred mpl)
                (fun X Y f => fmap (MPL.pred mpl) f \o MPL.tau mpl Y).
    Next Obligation.
      intros C D mpl X Y f g Heq.
      apply Category.comp_subst;
        [apply reflexivity | apply Map.substitute, Heq].
    Qed.
    Next Obligation.
      simpl.
      intros C D mpl X.
      apply MPL.tau_pred_eta.
    Qed.
    Next Obligation.
      simpl; intros C D mpl X Y Z f g.
      assert (H: fmap (Φ mpl) f \o fmap (Φ mpl) (fmap mpl g) \o τ mpl (mpl Z) \o τ mpl Z
                 ==
                 (fmap (Φ mpl) f \o τ mpl Y) \o fmap (Φ mpl) g \o τ mpl Z
             ).
      {
        apply symmetry.
        eapply transitivity.
        - eapply transitivity; [apply Category.comp_assoc |].
          apply Category.comp_subst; [| apply reflexivity].
          eapply transitivity; [apply symmetry, Category.comp_assoc |].
          apply Category.comp_subst; [apply reflexivity |].
          apply (Natrans.naturality (natrans:=MPL.tau mpl)).
        - simpl.
          apply Category.comp_subst; [| apply reflexivity].
          apply Category.comp_assoc.
      }
      eapply transitivity; [| apply H]; clear H.
      assert
        (H: fmap (Φ mpl) f \o fmap (Φ mpl) (fmap mpl g) \o fmap (Φ mpl) (μ mpl Z) \o τ mpl Z
            == 
            fmap (Φ mpl) f \o fmap (Φ mpl) (fmap mpl g) \o τ mpl (mpl Z) \o τ mpl Z).
      {
        apply Category.comp_subst; [| apply reflexivity].
        apply Category.comp_subst; [| apply reflexivity].
        apply MPL.tau_pred_mu.
      }
      eapply transitivity; [| apply H]; clear H.
      eapply transitivity; [| apply Category.comp_assoc].
      eapply transitivity; [| apply Category.comp_assoc].
      apply Category.comp_subst; [apply reflexivity |].
      eapply transitivity; [apply (Functor.fmap_comp (fobj:=Φ mpl)) |].
      eapply transitivity; [apply Category.comp_subst |].
      - apply (Functor.fmap_comp (fobj:=Φ mpl)).
      - apply reflexivity.
      - apply symmetry,Category.comp_assoc.
    Qed.
  End MPL.

  Module KPL.
    Program Definition mpl {C D: Category}(kpl: KPL C D): MPL C D :=
      MPL.build (KT.monad kpl)
                (Functor.build
                   (fun X => KPL.pred kpl X)
                   ([f :-> KPL.modal (t:=kpl) (KT.ret \o{C} f)]))
                (Natrans.build
                   (fun X => KPL.modal (t:=kpl) (Id (kpl X)))).
    Next Obligation.
      simpl.
      intros C D kpl Y X f g Heq.
      apply Map.substitute, Category.comp_subst;
        [apply Heq | apply reflexivity].
    Qed.      
    Next Obligation.
      simpl.
      intros C D kpl Z Y X g f; simpl.
      eapply transitivity; [apply Map.substitute | apply KPL.modal_bind].
      eapply transitivity; [apply symmetry, Category.comp_assoc |].
      eapply transitivity; [| apply Category.comp_assoc].
      apply Category.comp_subst; [apply reflexivity |].
      apply symmetry, KT.ret_comp_bind.
    Qed.      
    Next Obligation.
      simpl.
      intros C D kpl X.
      eapply transitivity; [apply Map.substitute | apply KPL.modal_ret].
      apply Category.comp_id_dom.
    Qed.      
    Next Obligation.
      simpl.
      intros C D kpl Y X f; simpl in *.
      eapply transitivity; [apply symmetry, KPL.modal_bind |].
      eapply transitivity; [apply Map.substitute | apply KPL.modal_bind].
      eapply transitivity; [apply Category.comp_id_dom |].
      eapply transitivity; [apply symmetry,Category.comp_id_cod |].
      eapply transitivity; [apply Category.comp_subst |].
      - apply reflexivity.
      - apply symmetry, KT.ret_comp_bind.
      - apply Category.comp_assoc.
    Qed.      
    Next Obligation.
      simpl.
      intros C D kpl X.
      eapply transitivity; [apply symmetry, KPL.modal_bind |].
      eapply transitivity; [| apply KPL.modal_ret].
      apply Map.substitute.
      eapply transitivity; [apply symmetry,Category.comp_assoc |].
      eapply transitivity;
        [apply Category.comp_subst |apply Category.comp_id_cod].
      - apply reflexivity.
      - apply KT.ret_comp_bind.
    Qed.      
    Next Obligation.
      simpl.
      intros C D kpl X.
      eapply transitivity; [apply symmetry, KPL.modal_bind |].
      eapply transitivity; [| apply KPL.modal_bind].
      apply Map.substitute.
      eapply transitivity; [apply symmetry,Category.comp_assoc |].
      eapply transitivity; [apply Category.comp_subst |].
      - apply reflexivity.
      - apply KT.ret_comp_bind.
      - eapply transitivity;
        [apply Category.comp_id_cod
        |apply symmetry, Category.comp_id_dom].
    Qed.      
  End KPL.      
End MonadKT.
Export MonadKT.

Module Equalities.
  Module Natrans.
    Definition equal2
               {C D: Category}
               {F G: Functor C D}(S: Natrans F G)
               {F' G': Functor C D}(T: Natrans F' G') :=
      forall X: C, S X =H T X.
  End Natrans.

  Module Monad.
    Definition equal {C: Category}(m1 m2: Monad C) :=
      (Monad.T m1 == Monad.T m2 :> Functor.setoid C C)/\
      (Natrans.equal2 (η m1) (η m2))/\
      (Natrans.equal2 (μ m1) (μ m2)).
    Arguments equal {C} m1 m2 /.

    Program Definition setoid (C: Category) :=
      Setoid.build (@equal C).
    Next Obligation.
      intros C mpl; simpl; repeat split;
      apply reflexivity.
    Qed.
    Next Obligation.
      intros C m1 m2 [HeqT [HeqEta HeqMu]]; simpl; repeat split.
      - intros X Y f; apply eq_Hom_symm, HeqT.
      - intros X; apply eq_Hom_symm, HeqEta.
      - intros X; apply eq_Hom_symm, HeqMu.
    Qed.
    Next Obligation.
      intros C m1 m2 m3
             [HeqT12 [HeqEta12 HeqMu12]]
             [HeqT23 [HeqEta23 HeqMu23]]; simpl; repeat split.
      - intros X Y f; eapply eq_Hom_trans; [apply HeqT12 | apply HeqT23].
      - intros X; eapply eq_Hom_trans; [apply HeqEta12 | apply HeqEta23].
      - intros X; eapply eq_Hom_trans; [apply HeqMu12 | apply HeqMu23].
    Qed.

  End Monad.

  Variant jmeq {X: Setoid}(x: X):
    forall {Y: Setoid}, Y -> Prop :=
  | jmeq_def: forall (x': X), x == x' :> X -> jmeq x x'.
    
  Module KT.
    Definition equal {C: Category}(kt1 kt2: KT C) :=
      (forall (X: C), KT.ret (t:=kt1)(X:=X) =H KT.ret (t:=kt2) (X:=X))/\
      (forall (X Y: C),
          jmeq (X:=Map.setoid _ _) (Y:=Map.setoid _ _)
               (Map.make (KT.bind_isMap (spec:=kt1)(X:=X)(Y:=Y)))
               (Map.make (KT.bind_isMap (spec:=kt2)(X:=X)(Y:=Y)))).
    Arguments equal {C} kt1 kt2 /.

    Program Definition setoid (C: Category) :=
      Setoid.build (@equal C).
    Next Obligation.
      intros C kt; split.
      - intros; apply eq_Hom_refl.
      - intros X Y.
        apply jmeq_def; simpl.
        intros f.
        apply Map.substitute.
        apply reflexivity.
    Qed.
    Next Obligation.
      intros C kt1 kt2 [Heqret Heqbind]; split.
      - intros X.
        apply eq_Hom_symm, Heqret.
      - intros X Y.
        destruct (Heqbind X Y).
        apply jmeq_def.
        apply symmetry, H.
    Qed.
    Next Obligation.
      intros C kt1 kt2 kt3
             [Heqret12 Heqbind12] [Heqret23 Heqbind23]; split.
      - intros X.
        eapply eq_Hom_trans; [apply Heqret12 | apply Heqret23].
      - intros X Y.
        generalize (Heqbind23 X Y). 
        destruct (Heqbind12 X Y); simpl in *.
        intro H'; destruct H'.
        apply jmeq_def.
        eapply transitivity; [apply H | apply H0].
    Qed.
  End KT.

  (* Monad -> KT -> Monad で復元 *)
  Lemma monad_kt_monad_eq:
    forall (C: Category)(m: Monad C),
      KT.monad (Monad.kt m) == m :> Monad.setoid C.
  Proof.
    intros C m; simpl.
    split; [| split].
    {
      intros X Y f; apply eq_Hom_def.
      eapply transitivity;
        [apply Category.comp_subst |].
      + apply Functor.fmap_comp.
      + apply reflexivity.
      + eapply transitivity;
        [apply symmetry, Category.comp_assoc |].
        eapply transitivity;
          [apply Category.comp_subst | apply Category.comp_id_cod].
        * apply reflexivity.
        * apply Monad.Teta_mu.
    }
    {
      intros X; simpl; apply eq_Hom_refl.
    }
    {
      intros X; simpl; apply eq_Hom_def.
      eapply transitivity; [| apply Category.comp_id_dom].
      apply Category.comp_subst; [| apply reflexivity].
      apply Functor.fmap_id.
    }
  Qed.

  (* KT -> Monad -> KT で復元 *)
  Lemma kt_monad_kt_eq:
    forall (C: Category)(kt: KT C),
      Monad.kt (KT.monad kt) == kt :> KT.setoid C.
  Proof.
    intros C kt; split; simpl.
    {
      intros X; apply eq_Hom_refl.
    }
    {
      intros X Y; apply jmeq_def; simpl.
      intros f; simpl.
      eapply transitivity; [apply KT.bind_comp |].
      apply Map.substitute.
      eapply transitivity; [| apply Category.comp_id_cod].
      eapply transitivity; [apply symmetry,Category.comp_assoc |].
      apply Category.comp_subst; [apply reflexivity |].
      apply KT.ret_comp_bind.
    }
  Qed.

  (* W.I.P *)
  Fail Lemma mpl_kpl_mpl_eq:
    forall (C D: Category)(mpl: MPL C D),
      KPL.mpl (MPL.kpl mpl) == mpl :> MPL.setoid C D.
        
  Fail Lemma mpl_kpl_mpl_eq:
    forall (C D: Category)(kpl: KPL C D),
      MPL.kpl (KPL.mpl kpl) == kpl :> KPL.setoid C D.

End Equalities.

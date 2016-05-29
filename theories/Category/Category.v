Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Setoid.

Delimit Scope cat_scope with cat.
Open Scope cat_scope.

(** 
 * (Coq 上の)圏論
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
        comp_subst:> forall (X Y Z: obj), Proper ((==) ==> (==) ==> (==)) (@comp X Y Z);
        
        comp_assoc:
          forall (X Y Z W: obj)
                 (f: arr X Y)(g: arr Y Z)(h: arr Z W),
            (comp f (comp g h)) == (comp (comp f g) h);

        comp_id_dom:
          forall (X Y: obj)(f: arr X Y),
            (comp (id X) f) == f;

        comp_id_cod:
          forall (X Y: obj)(f: arr X Y),
            (comp f (id Y)) == f
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

    Notation "f \;{ C } g" := (@comp C _ _ _ f g) (at level 60, right associativity): category_scope.
    Notation "f \; g" := (@comp _ _ _ _ f g) (at level 60, right associativity): category_scope.
    Notation "g \o{ C } f" := (@comp C _ _ _ f g) (at level 60, right associativity): cat_scope.
    Notation "g \o f" := (g \o{_} f) (at level 60, right associativity): cat_scope.
    Notation Id_ C X := (@id C X).
    Notation "'Id' X" := (Id_ _ X) (at level 30, right associativity): cat_scope.

  End Ex.

  Import Ex.

  Definition dom {C: Category}{X Y: C}(f: C X Y): C := X.
  Definition cod {C: Category}{X Y: C}(f: C X Y): C := Y.
  Arguments dom {C X Y} f /.
  Arguments cod {C X Y} f /.

  Lemma comp_subst_dom {C: Category}(X Y Z: C)(f f': C X Y)(g: C Y Z):
    f == f' -> g \o f == g \o f'.
  Proof.
    intros Heq; apply Category.comp_subst; [apply Heq | apply reflexivity].
  Qed.

  Lemma comp_subst_cod {C: Category}(X Y Z: C)(f: C X Y)(g g': C Y Z):
    g == g' -> g \o f == g' \o f.
  Proof.
    intros Heq; apply Category.comp_subst; [apply reflexivity | apply Heq].
  Qed.
  
  (**
   *** 圏の双対
[Category.build] のおかげで定義しやすい気がする。
   **)
  Program Definition op (C: Category): Category :=
    build (fun (X Y: C) => C Y X)
          (fun X Y Z f g => f \o g)
          (fun X => Id X).
  Next Obligation.
    now intros f f' Hf g g' Hg; rewrite Hf, Hg.
  Qed.
  Next Obligation.
    intros; simpl in *.
    now rewrite comp_assoc.
  Qed.
  Next Obligation.
    intros; simpl in *.
    now rewrite comp_id_cod.
  Qed.
  Next Obligation.
    intros; simpl in *.
    now rewrite comp_id_dom.
  Qed.

  Module Ex2.
    Notation catCa := comp_assoc.
    Notation catC1f := comp_id_dom.
    Notation catCf1 := comp_id_cod.
    Notation catCs := comp_subst.
    Notation catCsd := comp_subst_dom.
    Notation catCsc := comp_subst_cod.
  End Ex2.
    
End Category.
Export Category.Ex.
Export Category.Ex2.


(** * Category **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Export COC.Base.Setoid.

Class IsCategory
      (obj: Type)
      (hom: obj -> obj -> Setoid)
      (comp: forall {X Y Z: obj}, hom X Y -> hom Y Z -> hom X Z)
      (id: forall (X: obj), hom X X) :=
  {
    cat_comp_proper:>
      forall (X Y Z: obj),
        Proper ((==) ==> (==) ==> (==)) (@comp X Y Z);
    
    cat_comp_assoc:
      forall X Y Z W (f: hom X Y)(g: hom Y Z)(h: hom Z W),
        comp f (comp g h) == comp (comp f g) h;
    
    cat_comp_id_dom:
      forall X Y (f: hom X Y),
        comp (id X) f == f;
    
    cat_comp_id_cod:
      forall X Y (f: hom X Y),
        comp f (id Y) == f
  }.
Hint Resolve cat_comp_assoc cat_comp_id_dom cat_comp_id_cod.

Structure Category :=
  {
    cat_obj:> Type;
    cat_hom:> cat_obj -> cat_obj -> Setoid;
    cat_comp:
      forall (X Y Z: cat_obj),
        cat_hom X Y -> cat_hom Y Z -> cat_hom X Z;
    cat_id: forall X: cat_obj, cat_hom X X;

    cat_prf:> IsCategory cat_comp cat_id
  }.
Existing Instance cat_prf.

Notation "[ 'Category' 'by' hom 'with' comp , id ]" :=
  (@Build_Category _ hom comp id _).
Notation "[ 'Category' 'by' hom 'with' 'comp' := comp 'with' 'id' := id ]" :=
  [Category by hom with comp , id].

Notation "g \o{ C } f" := (@cat_comp C _ _ _ f g) (at level 60, right associativity).
Notation "g \o f" := (g \o{_} f) (at level 60, right associativity) .
Notation "Id_{ C } X" := (@cat_id C X) (at level 20, no associativity).
Notation "'Id' X" := (Id_{_} X) (at level 30, right associativity).

Definition domain {C: Category}{X Y: C}(f: C X Y) := X.
Definition codomain {C: Category}{X Y: C}(f: C X Y) := Y.

Class Isomorphic (C: Category)(X Y: C)(f: C X Y)(g: C Y X) :=
  {
    isomorphic_iso: g \o f == Id X;
    isomorphic_inv: f \o g == Id Y
  }.

Definition isomorphic (C: Category)(X Y: C) :=
  exists (f: C X Y)(g: C Y X), Isomorphic f g.

Program Definition isomorphic_setoid (C: Category) :=
  [Setoid by isomorphic C on C].
Next Obligation.
  - intros X.
    exists (Id X), (Id X); split.
    + now rewrite cat_comp_id_dom.
    + now rewrite cat_comp_id_cod.
  - intros X Y [f [g [Heqfg Heqgf]]].
    now exists g, f.
  - intros X Y Z [f [f' [Heqf Heqf']]] [g [g' [Heqg Heqg']]].
    exists (g \o f), (f' \o g'); split.
    + rewrite cat_comp_assoc, <- (cat_comp_assoc f), Heqg.
      now rewrite cat_comp_id_cod, Heqf.
    + rewrite cat_comp_assoc, <- (cat_comp_assoc g'), Heqf'.
      now rewrite cat_comp_id_cod, Heqg'.
Qed.
Notation "X === Y 'in' C" := (X == Y in (isomorphic_setoid C)) (at level 70, no associativity, Y at next level).
Notation "X === Y" := (X === Y in _) (at level 70, no associativity).

(** Category of Type **)
Program Definition Types :=
  [Category by function
   with (fun X Y Z f g x => g (f x)),
        (fun X x => x)].
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl.
  now rewrite Heqf, Heqg.
Qed.
Canonical Structure Types.

(** Category of Setoid **)
Program Definition Setoids :=
  [Category by Map_setoid with Map_compose, Map_id].
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl.
  now rewrite (Heqf x), (Heqg (f' x)).
Qed.
Canonical Structure Setoids.

(** Discrete category **)
Program Definition Prop_setoid (P: Prop) :=
  [Setoid by (fun _ _ => True) on P].

Program Definition DiscreteCategory (X: Setoid): Category :=
  [Category by `(Prop_setoid (x == y)) with _,_].
Next Obligation.
  revert H H0.
  now apply transitivity.
Qed.

(** Dual category **)
Program Definition DualCategory (C: Category): Category :=
  [Category by (fun X Y => C Y X)
   with (fun X Y Z (f: C Y X)(g: C Z Y) => f \o g),
        (fun X => Id X)].
Next Obligation.
  - now intros f f' Heqf g g' Heqg; rewrite Heqf, Heqg.
  - now rewrite cat_comp_assoc.
  - now rewrite cat_comp_id_cod.
  - now rewrite cat_comp_id_dom.
Qed.
Notation "C ^op" := (DualCategory C) (at level 0, format "C ^op").

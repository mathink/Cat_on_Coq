(* scratch *)

Require Import 
Ssreflect.ssreflect
Ssreflect.ssrfun
Ssreflect.eqtype
Ssreflect.ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Definition relation (A: Type) := A -> A -> Prop.

(* * Equivalence Relation *)
Module Relation.

  Section RelProperties.

    Variables (A: Type)(R: relation A).

    Definition reflexive:=
      forall (a: A), R a a.

    Definition symmetric:=
      forall (a b: A), R a b -> R b a.

    Definition transitive:=
      forall (a b c: A), R a b -> R b c -> R a c.

  End RelProperties.

End Relation.

(* Module Equivalence. *)

(*   Structure mixin_of (A: Type)(eq: relation A) := *)
(*     Mixin *)
(*       { _ : Relation.reflexive eq; *)
(*         _ : Relation.symmetric eq; *)
(*         _ : Relation.transitive eq }. *)

(*   Module Exports. *)
(*     Notation mkEquiv := Mixin. *)
(*     Notation equiv := mixin_of. *)
(*   End Exports. *)

(* End Relation. *)
(* Export Relation.Exports. *)
Hint Unfold Relation.reflexive Relation.symmetric Relation.transitive.

(*
Lemma equiv_refl T (e: equiv T):
  Relation.reflexive e.
Proof.
  by case: e => ?.
Qed.

Lemma equiv_symm T (e: equiv T):
  Relation.symmetric e.
Proof.
  by case: e => ?.
Qed.

Lemma equiv_trans T (e: equiv T):
  Relation.transitive e.
Proof.
  by case: e => ?.
Qed.
*)

(* ** instance of equivalence *)

(** * Setoid *)
Module Setoid.

  Structure mixin_of T :=
    Mixin
      { equal: relation T;
        _: Relation.reflexive equal;
        _: Relation.symmetric equal;
        _: Relation.transitive equal }.
  Notation class_of := mixin_of (only parsing).

  Section ClassDef.
    Structure type :=
      Pack
        { sort;
          _: class_of sort;
          _: Type }.
    Local Coercion sort : type >-> Sortclass.
    Variables (T: Type)(t: type).

    Definition class :=
      let: Pack _ c _ := t return mixin_of t in c.

    Definition pack c := @Pack T c T.

    Definition clone := fun c & t -> T & phant_id (pack c) t => pack c.
  End ClassDef.

  Module Exports.
    Coercion sort: type >-> Sortclass.
    Notation setoid := type.
    Notation SetoidMixin := Mixin.
    Notation SetoidType T s := (@pack T s).
  End Exports.

End Setoid.
Export Setoid.Exports.

Definition setoid_eq {S: setoid}: relation S := Setoid.equal (Setoid.class S).
Hint Unfold setoid_eq.

Notation "x === y" := (setoid_eq x y) (at level 89, no associativity).

(* level 90 にすると， Proof General 上で C-c C-u したときに例外を起こす coqtop でも再現するのだろうか*)

Lemma setoidE (S: setoid) x: setoid_eq x = (Setoid.equal (Setoid.class S)) x.
Proof.
  by [].
Qed.


Lemma setoid_eq_refl (s: setoid):
  Relation.reflexive (@setoid_eq s).
Proof.
  by case: s => ? [].
Qed.

Lemma setoid_eq_symm (s: setoid):
  Relation.symmetric (@setoid_eq s).
Proof.
  by case: s => ? [].
Qed.

Lemma setoid_eq_trans (s: setoid):
  Relation.transitive (@setoid_eq s).
Proof.
  by case: s => ? [].
Qed.


(* ** instance of setoid *)
Section eqSetoid.

  Variable (A: Type).

  Lemma eqrefl:
    Relation.reflexive (@eq A).
  Proof.
    done.
  Qed.

  Lemma eqsymm:
    Relation.symmetric (@eq A).
  Proof.
    done.
  Qed.

  Lemma eqtrans:
    Relation.transitive (@eq A).
  Proof.
    by move=> a b c -> -> //=.
  Qed.


  Canonical eqSetoidMixin := Eval hnf in SetoidMixin eqrefl eqsymm eqtrans.
  Canonical eqSetoidType := Eval hnf in SetoidType A eqSetoidMixin.
  
End eqSetoid.


Definition ext_eq {X Y: Type}(f g: X -> Y) :=
  forall x, f x = g x.
Hint Unfold ext_eq.

Section functionEquiv.
  
  Variables (X Y: Type).
  
  Lemma exteqrefl: Relation.reflexive (@ext_eq X Y).
  Proof.
    done.
  Qed.
  
  Lemma exteqsymm: Relation.symmetric (@ext_eq X Y).
  Proof.
    by move=> f g H.
  Qed.
  
  Lemma exteqtrans: Relation.transitive (@ext_eq X Y).
  Proof.
    by move=> f g h Heqfg Heqgh x; move: (Heqfg x) => ->.
  Qed.

  Canonical functionSetoidMixin := SetoidMixin exteqrefl exteqsymm exteqtrans.
  Canonical functionSetoidType  := Eval hnf in SetoidType (X -> Y) functionSetoidMixin.

End functionEquiv.


Module Morphism.

  Section Properties.
    
    Variables (dom cod: setoid)(f: dom -> cod).

    Definition well_defined :=
      forall (x y: dom), x === y -> f x === f y.

  End Properties.

  Structure mixin_of (dom cod: setoid)(f: dom -> cod) := 
    Mixin
      { _: well_defined f }.
  Notation class_of := mixin_of (only parsing).

  Section ClassDef.
    Structure type (domain codomain: setoid) :=
      Pack
        { morphism;
          _: @class_of domain codomain morphism;
          _: domain -> codomain }.
    Local Coercion morphism: type >-> Funclass.
    Variables (dom cod: setoid)(f: dom -> cod)(t: type dom cod).

    Definition class :=
      let: Pack _ c _ := t return class_of t in c.

    Definition pack c := @Pack dom cod f c f.

  End ClassDef.

  Module Exports.
    Coercion morphism: type >-> Funclass.
    Notation morphism := type.
    Notation MorphismMixin := Mixin.
    Notation MorphismType m := (@pack _ _ _ m).
  End Exports.    
End Morphism.
Export Morphism.Exports.

Lemma morphism_f_equal {X Y: setoid}(f: morphism X Y):
  forall (x y: X), x === y -> f x === f y.
Proof.
  by case: f => [g [H e]] //=.
Qed.

Section MorphismCompose.
 Variables (X Y Z: setoid)(f: morphism X Y)(g: morphism Y Z).
 
 Lemma morphismCompose_well_defined:
   Morphism.well_defined (fun x => g (f x)).
 Proof.
   rewrite/Morphism.well_defined.
   by move=> x y Heq; do 2 apply morphism_f_equal.
 Qed.

 Canonical morphismComposeMorphismMixin := MorphismMixin morphismCompose_well_defined.

End MorphismCompose.

Canonical morphismComposeMorphismType {X Y Z: setoid}(f: morphism X Y)(g: morphism Y Z) :=
  Eval hnf in MorphismType (morphismComposeMorphismMixin f g).

Section IdMorphism.
 Variables (X: setoid).
 
 Lemma idMorphism_well_defined:
   Morphism.well_defined (fun x: X => x).
 Proof.
   by []. 
 Qed.

 Canonical idMorphismMixin := MorphismMixin idMorphism_well_defined.

End IdMorphism.

Canonical idMorphismType (X: setoid) :=
  Eval hnf in MorphismType (idMorphismMixin X).

Section eqMorphism.

  Variables (A B: Type)(f: A -> B).

  Lemma eqfwd:
    Morphism.well_defined f.
  Proof.
    move=> x y -> //=.
  Qed.

  Canonical eqMorphismMixin :=  MorphismMixin eqfwd.
  Canonical eqMorphismType := Eval hnf in MorphismType eqMorphismMixin.

End eqMorphism.

Ltac eq_rewrite H :=
  do [ apply (setoid_eq_trans H) | apply setoid_eq_symm, (setoid_eq_trans (setoid_eq_symm H)), setoid_eq_symm ].

  
(* ** instance of morphism *)
Section morphismSetoid.
  Variables (dom cod: setoid).
  Let eqmorphism (f g: morphism dom cod) :=
    forall x: dom, f x === g x.
  Hint Unfold eqmorphism.
  
  Lemma eqmorphism_refl:
    Relation.reflexive eqmorphism.
  Proof.
    move=> f x; apply setoid_eq_refl.
  Qed.  

  Lemma eqmorphism_symm:
    Relation.symmetric eqmorphism.
  Proof.
    move=> f g Heq x; apply setoid_eq_symm, Heq.
  Qed.  

  Lemma eqmorphism_trans:
    Relation.transitive eqmorphism.
  Proof.
    move=> f g h Heqfg Heqgh x.
    eq_rewrite (Heqfg x); apply Heqgh.
  Qed.

  Canonical morphismSetoidMixin := SetoidMixin eqmorphism_refl eqmorphism_symm eqmorphism_trans.
  Canonical morphismSetoidType := Eval hnf in SetoidType (morphism dom cod) morphismSetoidMixin.

End morphismSetoid.
Notation "X --> Y" := (morphismSetoidType X Y) (at level 70, right associativity).

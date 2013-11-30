(* scratch *)

Require Import 
Ssreflect.ssreflect
Ssreflect.ssrfun
Ssreflect.eqtype
Ssreflect.ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Binary relation *)
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

Check setoid_eq.
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


  Canonical eqSetoidMixin := SetoidMixin eqrefl eqsymm eqtrans.
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
  Canonical functionSetoidType  := SetoidType (X -> Y) functionSetoidMixin.

End functionEquiv.


Check (S === S).
Check (true === false).
Check (1 === 2).
(* Check id. *)
(* Definition Id (X: Type)(x: X) := x. *)
(* Check  (@Id nat). *)
(* Check ((@Id nat) === S). *)
Check (S === id).
Check (tt === tt).


(* * map from setoid to setoid *)
Module Map.

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
        { map;
          _: @mixin_of domain codomain map;
          _: domain -> codomain }.
    Local Coercion map: type >-> Funclass.
    Variables (dom cod: setoid)(f: dom -> cod)(t: type dom cod).

    Definition class :=
      let: Pack _ c _ := t return class_of t in c.

    Definition pack c := @Pack dom cod f c f.

  End ClassDef.

  Module Exports.
    Coercion map: type >-> Funclass.
    Notation map := type.
    Notation MapMixin := Mixin.
    Notation MapType m := (@pack _ _ _ m).
  End Exports.    
End Map.
Export Map.Exports.

Lemma map_f_equal {X Y: setoid}(f: map X Y):
  forall (x y: X), x === y -> f x === f y.
Proof.
  by case: f => [g [H e]] //=.
Qed.

Section MapCompose.
 Variables (X Y Z: setoid)(f: map X Y)(g: map Y Z).
 Check Map.well_defined.
 
 Lemma mapCompose_well_defined:
   Map.well_defined (fun x => g (f x)).
 Proof.
   rewrite/Map.well_defined.
   by move=> x y Heq; do 2 apply map_f_equal.
 Qed.

 Canonical mapComposeMapMixin := MapMixin mapCompose_well_defined.

End MapCompose.

Canonical mapComposeMapType {X Y Z: setoid}(f: map X Y)(g: map Y Z) :=
  Eval hnf in MapType (mapComposeMapMixin f g).

Section IdMap.
 Variables (X: setoid).
 
 Lemma idMap_well_defined:
   Map.well_defined (fun x: X => x).
 Proof.
   by []. 
 Qed.

 Canonical idMapMixin := MapMixin idMap_well_defined.

End IdMap.

Canonical idMapType (X: setoid) :=
  Eval hnf in MapType (idMapMixin X).

Section eqMap.

  Variables (A B: Type)(f: A -> B).

  Lemma eqfwd:
    Map.well_defined f.
  Proof.
    move=> x y -> //=.
  Qed.

  Canonical eqMapMixin := MapMixin eqfwd.
  Check eqMapMixin.
  Canonical eqMapType := Eval hnf in MapType eqMapMixin.

End eqMap.

Ltac eq_rewrite H :=
  do [ apply (setoid_eq_trans H) | apply setoid_eq_symm, (setoid_eq_trans (setoid_eq_symm H)), setoid_eq_symm ].

  
(* ** instance of map *)
Section mapSetoid.
  Variables (dom cod: setoid).
  Check map.
  Let eqmap (f g: map dom cod) :=
    forall x: dom, f x === g x.
  Hint Unfold eqmap.
  
  Lemma eqmap_refl:
    Relation.reflexive eqmap.
  Proof.
    move=> f x; apply setoid_eq_refl.
  Qed.  

  Lemma eqmap_symm:
    Relation.symmetric eqmap.
  Proof.
    move=> f g Heq x; apply setoid_eq_symm, Heq.
  Qed.  

  Lemma eqmap_trans:
    Relation.transitive eqmap.
  Proof.
    move=> f g h Heqfg Heqgh x.
    eq_rewrite (Heqfg x); apply Heqgh.
  Qed.

  Canonical mapSetoidMixin := SetoidMixin eqmap_refl eqmap_symm eqmap_trans.
  Canonical mapSetoidType := Eval hnf in SetoidType (map dom cod) mapSetoidMixin.

End mapSetoid.
Notation "X --> Y" := (mapSetoidType X Y) (at level 70, right associativity).
(* Hint Unfold eqmap. *)

(* Section MapSetoidCompose. *)
(*   Variables (X Y Z: setoid). *)
  
(*   Lemma mapSetoidCompsoe_well_defined_1 (f: X --> Y): *)
(*     Map.well_defined (@mapComposeMapType _ _ Z f). *)
(*   Proof. *)
(*     rewrite/Map.well_defined. *)
(*     simpl. *)
(*     move: f => [f [Hf f']] [g [Hg g']] [h [Hh h']] Heq. *)
(*     rewrite/mapComposeMapType /mapComposeMapMixin. *)


(*   Definition mapSetoidCompose_Mixin_1 (f: X --> Y): (Y --> Z) --> (X --> Z) := *)
(*     MapMixin (mapComposeMapType f). *)
    

(*     :=  *)
(*   Coercion mapSetoidCompose *)
(* Coercion mapSetoidCompose:  *)
(* Definition mapSetoidCompose_Setoid {X Y Z: setoid}: *)
(*   mapSetoidType (X --> Y) (mapSetoidType (Y --> Z) (X --> Z)). *)
(* Proof. *)
(*   simpl. *)


(* For Category Theory *)
(** * Axioms of Category *)
Module Category.
  Section Properties.
    Variables (T: Type)(hom: T -> T -> setoid)
              (comp: forall (X Y Z: T),
                       (hom X Y) -> (hom Y Z) -> (hom X Z))
              (id: forall (X: T), hom X X).
    Arguments comp {X Y Z}(f g).
    Arguments id (X).

    Definition comp_id_dom :=
      forall (X Y: T)(f: hom X Y), comp (id X) f === f.

    Definition comp_id_cod :=
      forall (X Y: T)(f: hom X Y), comp f (id Y) === f.

    Definition comp_assoc :=
      forall (X Y Z W: T)(f: hom X Y)(g: hom Y Z)(h: hom Z W),
        comp f (comp g h) === comp (comp f g) h.

  End Properties.
    
  (* component of Categorical Structure *)
  Structure mixin_of (T: Type) :=
    Mixin
      { hom: T -> T -> setoid;
        comp: forall (X Y Z: T),
                hom X Y -> hom Y Z -> hom X Z;
        id: forall (X: T), hom X X;
        _: comp_id_dom comp id;
        _: comp_id_cod comp id;
        _: comp_assoc comp }.
  Notation class_of := mixin_of (only parsing).
  
  Section ClassDef.
    Structure type :=
      Pack 
        { obj;
          _: class_of obj;
          _: Type }.
    Local Coercion obj: type >-> Sortclass.
    Variables (Obj: Type)(t: type).

    Definition class :=
      let: Pack _ cat _ := t return mixin_of t in cat.

    Definition pack cat := @Pack Obj cat Obj.
    Definition clone := fun cat & t -> Obj & phant_id (pack cat) t => cat.
  End ClassDef.

  Module Exports.
    Coercion obj: type >-> Sortclass.
    Notation Hom X Y := (@hom _ _ X Y). 
    Notation category := type.
    Notation CatMixin := Mixin.
    Notation CatType T c := (@pack T c).
  End Exports.
End Category.
Export Category.Exports.

Definition compose (C: category) := @Category.comp _ (Category.class C).
Lemma composeE C x y z f g : @compose C x y z f g = @Category.comp _ (Category.class C) x y z f g.
Proof. by []. Qed.
Arguments compose {C X Y Z}(f g).

Definition ident c := Category.id (Category.class c).

Lemma identE C x : ident x = Category.id (Category.class C) x.
Proof. by []. Qed.

Arguments ident {c}(X).

Notation "g • f" := (compose f g)
                        (at level 60, right associativity).
Lemma comp1f (C: category):
  forall (X Y: C)(f: Hom X Y), f • (ident X) === f.
Proof.
  by case: C => ? [].
Qed.

Lemma compf1 (C: category):
  forall (X Y: C)(f: Hom X Y), (ident Y)•f === f.
Proof.
  by case: C => ? [].
Qed.

Lemma compA (C: category):
  forall (X Y Z W: C)(f: Hom X Y)(g: Hom Y Z)(h: Hom Z W),
    (h•g)•f === h•(g•f).
Proof.
  by case: C => ? [].
Qed.


Section Setoids.
  Check Category.comp_id_dom.
  Lemma setoids_comp_id_dom:
    Category.comp_id_dom (@mapComposeMapType) (@idMapType).
  Proof.
    rewrite/Category.comp_id_dom /setoid_eq //=.
      by move=> X Y f x; apply setoid_eq_refl.
  Qed.           

  Lemma setoids_comp_id_cod:
    Category.comp_id_cod (@mapComposeMapType) (@idMapType).
  Proof.
    rewrite/Category.comp_id_cod /setoid_eq //=.
      by move=> X Y f x; apply setoid_eq_refl.
  Qed.           

  Lemma setoids_comp_assoc:
    Category.comp_assoc (@mapComposeMapType).
  Proof.
    rewrite/Category.comp_assoc /setoid_eq //=.
      by move=> X Y Z W f g h x; apply setoid_eq_refl.
  Qed.           

  Canonical SetoidsCatMixin := CatMixin setoids_comp_id_dom setoids_comp_id_cod setoids_comp_assoc.
  Canonical SetoidsCatType := CatType setoid SetoidsCatMixin.
End Setoids.

Section Sets.
  Definition function_compose (X Y Z: Type)(f: X -> Y)(g: Y -> Z) :=
    fun x => g (f x).
  Definition function_id (X: Type) := fun x: X => x.

  Lemma sets_comp_id_dom:
    Category.comp_id_dom function_compose function_id.
  Proof.
    by [].
  Qed.           

  Lemma sets_comp_id_cod:
    Category.comp_id_cod function_compose function_id.
  Proof.
    by [].
  Qed.           

  Lemma sets_comp_assoc:
    Category.comp_assoc function_compose.
  Proof.
    by [].
  Qed.           

  Canonical SetsCatMixin := CatMixin sets_comp_id_dom sets_comp_id_cod sets_comp_assoc.
  Canonical SetsCatType := CatType Type SetsCatMixin.
End Sets.


Check (plus • S).

    
(** * Meta Graph *)
Module MetaGraph.

  Structure mixin (obj arr: setoid) :=
    Mixin
      { dom: arr --> obj;
        cod: arr --> obj }.

  Section ClassDef.
    Structure type :=
      Pack
        { obj;
          arr;
          _: mixin obj arr;
          _: setoid;
          _: setoid }.
    Variables (O A: setoid)(t: type).

    Definition class :=
      let: Pack _ _ mg _ _ := t return mixin (obj t) (arr t) in mg.

    Definition pack mg := @Pack O A mg O A.

    (* Definition clone := fun mg & (obj t) -> O & (arr t) -> A & phant_id (pack mg) t => pack mg. *)
  End ClassDef.

  Module Exports.
    Coercion obj: type >-> setoid.
    Notation mgType := type.
    Notation mkMetaGraph := Mixin.
    Notation MGType O A mg := (@pack O A mg).
  End Exports.
End MetaGraph.
Export MetaGraph.Exports.

Definition obj mg := Eval hnf in MetaGraph.obj mg.
Definition arr mg := Eval hnf in MetaGraph.arr mg.
Definition dom mg := Eval hnf in @MetaGraph.dom (obj mg) (arr mg) (MetaGraph.class mg).
Definition cod mg := Eval hnf in @MetaGraph.cod (obj mg) (arr mg) (MetaGraph.class mg).


Module SmallCategory.
  
  Section homSetoid.

    Variable (meta: mgType).
    
    Definition hom (X Y: obj meta) :=
      { f : arr meta | dom meta f === X & cod meta f === Y }.

    Definition eqhom {X Y: obj meta}(f g: hom X Y) :=
      match f, g with
        | exist2 f' _ _, exist2 g' _ _ => f' === g'
      end.
    
    Section eqhomEquiv.

      Variables (X Y: obj meta).
      
      Lemma eqhom_refl:
        Relation.reflexive (@eqhom X Y).
      Proof.
        move=> [f Hdom Hcod] /=; apply setoid_eq_refl.
      Qed.

      Lemma eqhom_symm:
        Relation.symmetric (@eqhom X Y).
      Proof.
        move=> [f Hdf Hcf] [g Hdg Hcg] /=; apply setoid_eq_symm.
      Qed.

      Lemma eqhom_trans:
        Relation.transitive (@eqhom X Y).
      Proof.
        move=> [f Hdf Hcf] [g Hdg Hcg] [h Hdh Hch] /=;
                           apply setoid_eq_trans.
      Qed.

      Canonical homSetoidMixin := SetoidMixin eqhom_refl eqhom_symm eqhom_trans.
      Canonical homSetoidType := Eval hnf in SetoidType (hom X Y) homSetoidMixin.
    End eqhomEquiv.

  End homSetoid.
  Notation Hom := homSetoidType.

  Section Properties.

    Variable (meta: mgType)
             (comp: forall (X Y Z: obj meta),
                      (Hom X Y) --> (Hom Y Z) --> (Hom X Z))
             (id: forall (X: obj meta), Hom X X).
    Arguments comp {X Y Z}.
    Arguments id (X).

    Definition compose_id_dom :=
      forall (X Y: obj meta)(f: Hom X Y), comp (id X) f === f.

    Definition compose_id_cod :=
      forall (X Y: obj meta)(f: Hom X Y), comp f (id Y) === f.

    Definition compose_assoc :=
      forall (X Y Z W: obj meta)(f: Hom X Y)(g: Hom Y Z)(h: Hom Z W),
        comp f (comp g h) === comp (comp f g) h.

  End Properties.

  Structure mixin (meta: mgType) :=
    Mixin
      { comp: forall (X Y Z: obj meta),
                Hom X Y --> Hom Y Z --> Hom X Z;
        id: forall (X: obj meta), Hom X X;
        _: compose_id_dom comp id;
        _: compose_id_cod comp id;
        _: compose_assoc comp }.

  Section ClassDef.
    Structure type :=
      Pack
        { meta;
          _: mixin meta;
          _: mgType }.
    Variables (M: mgType)(t: type).

    Definition class :=
      let: Pack _ c _ := t return mixin (meta t) in c.

    Definition pack mg := @Pack M mg M.

    (* Definition clone := fun c & (meta t) -> M & phant_id (pack c) t => pack c. *)
  End ClassDef.

  Module Exports.
    Coercion meta: type >-> mgType.
    Notation scategory := type.
    Notation sCatMixin := Mixin.
    Notation sCatType M mg := (@pack M mg).
    Arguments homSetoidType {meta}(X Y).
    Notation Hom := homSetoidType.
  End Exports.

End SmallCategory.
Export SmallCategory.Exports.

Definition compose c := Category.comp (Category.class c).
Arguments compose {c X Y Z}.
Definition ident c := Category.id (Category.class c).
Arguments ident {c}(X).

Notation "g • f" := (compose f g)
                        (at level 60, right associativity).

(* こういう名前じゃないほうがいいとは思うけど，一旦ね *)
Lemma comp1f (c: category):
  forall (X Y: c)(f: Hom X Y), f • (ident X) === f.
Proof.
  by case: c => ? [].
Qed.

Lemma compf1 (c: category):
  forall (X Y: c)(f: Hom X Y), (ident Y)•f === f.
Proof.
  by case: c => ? [].
Qed.

Lemma compA (c: category):
  forall (X Y Z W: c)(f: Hom X Y)(g: Hom Y Z)(h: Hom Z W),
    (h•g)•f === h•(g•f).
Proof.
  by case: c => ? [].
Qed.



(* Locally Small Category *)

Module LSCat.

  Section Properties.

    Variable (T: Type)
             (hom: T -> T -> setoid)
             (comp: forall (X Y Z: T),
                      (hom X Y) --> (hom Y Z) --> (hom X Z))
             (id: forall (X: T), hom X X).
    Arguments comp {X Y Z}.
    Arguments id (X).

    Definition compose_id_dom :=
      forall (X Y: T)(f: hom X Y), comp (id X) f === f.

    Definition compose_id_cod :=
      forall (X Y: T)(f: hom X Y), comp f (id Y) === f.

    Definition compose_assoc :=
      forall (X Y Z W: T)(f: hom X Y)(g: hom Y Z)(h: hom Z W),
        comp f (comp g h) === comp (comp f g) h.

  End Properties.


  Structure mixin_of (T: Type) :=
    Mixin
      { hom: T -> T -> setoid;
        comp: forall (X Y Z: T),
                hom X Y --> hom Y Z --> hom X Z;
        id: forall (X: T), hom X X;
        _: compose_id_dom comp id;
        _: compose_id_cod comp id;
        _: compose_assoc comp }.

  Section ClassDef.
    Structure type :=
      Pack
        { sort;
          _: mixin_of sort;
          _: Type }.
    Coercion sort: type >-> Sortclass.
    Variables (T: Type)(t: type).

    Definition class :=
      let: Pack _ c _ := t return mixin_of t in c.

    Definition pack c := @Pack T c T.

    Definition clone := fun c & T -> T & phant_id (pack c) T => pack c.
  End ClassDef.

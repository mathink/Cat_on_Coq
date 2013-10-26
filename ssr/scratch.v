(* scratch *)

Require Import 
Ssreflect.ssreflect
Ssreflect.ssrfun
Ssreflect.eqtype
Ssreflect.ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.

(* Binary relation *)
Definition relation (A: Type) := A -> A -> Prop.

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

  Structure Equivalence (A: Type)(eq: relation A) :=
    Mixin
      { _ : reflexive eq;
        _ : symmetric eq;
        _ : transitive eq }.

  Module Exports.
    Notation mkEquiv := Mixin.
    Notation equiv := Equivalence.
  End Exports.

End Relation.
Export Relation.Exports.
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

Section eqEquiv.

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

  Canonical eqEquiv := mkEquiv (eqrefl) (eqsymm) (eqtrans).

End eqEquiv.

Module Setoid.

  Structure mixin T :=
    Mixin
      { equal: relation T;
        _: equiv equal }.

  Section ClassDef.
    Structure type :=
      Pack
        { sort;
          _: mixin sort;
          _: Type }.
    Local Coercion sort : type >-> Sortclass.
    Variables (T: Type)(t: type).

    Definition class :=
      let: Pack _ c _ := t return mixin t in c.

    Definition pack c := @Pack T c T.

    Definition clone := fun c & t -> T & phant_id (pack c) t => pack c.
  End ClassDef.

  Module Exports.
    Coercion sort: type >-> Sortclass.
    Notation setoid := type.
    Notation mkSetoid := Mixin.
    Notation SetoidType T s := (@pack T s).
  End Exports.

End Setoid.
Export Setoid.Exports.

Definition setoid_eq {S: setoid}: relation S := Setoid.equal (Setoid.class S).
Hint Unfold setoid_eq.

Notation "x === y" := (setoid_eq x y) (at level 89, no associativity).

(* level 90 にすると， Proof General 上で C-c C-u したときに例外を起こす coqtop でも再現するのだろうか*)

Check setoid_eq.
Lemma eqE T x : eq_op x = Equality.op (Equality.class T) x.
Proof. by []. Qed.

Lemma setoidE (S: setoid) x: setoid_eq x = (Setoid.equal (Setoid.class S)) x.
Proof.
  by [].
Qed.

Lemma setoid_eq_refl (s: setoid):
  Relation.reflexive (@setoid_eq s).
Proof.
  by case: s => [t [e []]].
Qed.

Lemma setoid_eq_symm (s: setoid):
  Relation.symmetric (@setoid_eq s).
Proof.
  by case: s => [t [e []]].
Qed.

Lemma setoid_eq_trans (s: setoid):
  Relation.transitive (@setoid_eq s).
Proof.
  by case: s => [t [e []]].
Qed.


Section eqSetoid.

  Variable (A: Type).

  Canonical eqSetoidMixin := mkSetoid (eqEquiv A).
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

  Canonical functionEquiv := mkEquiv exteqrefl exteqsymm exteqtrans.

End functionEquiv.

Canonical functionSetoid (X Y: Type) := mkSetoid (functionEquiv X Y).

Check (1 === 2).
Check (true === false).
Check (S === S).
(* Check id. *)
(* Definition Id (X: Type)(x: X) := x. *)
(* Check  (@Id nat). *)
(* Check ((@Id nat) === S). *)
Check (S === id).
Check (tt === tt).

Module Map.

  Section Properties.
    
    Variables (dom cod: setoid)(f: dom -> cod).

    Definition well_defined :=
      forall (x y: dom), x === y -> f x === f y.

  End Properties.

  Structure mixin (dom cod: setoid)(f: dom -> cod) := 
    Mixin
      { _: well_defined f }.

  Section ClassDef.
    Structure type (domain codomain: setoid) :=
      Pack
        { map;
          _: @mixin domain codomain map;
          _: domain -> codomain }.
    Local Coercion map: type >-> Funclass.
    Variables (dom cod: setoid)(f: dom -> cod)(t: type dom cod).

    Definition class :=
      let: Pack _ c _ := t return mixin t in c.

    Definition pack c := @Pack dom cod f c f.

  End ClassDef.

  Module Exports.
    Coercion map: type >-> Funclass.
    Notation map := type.
    Notation mkMap := Mixin.
    Notation MapType f m := (@pack f m).
  End Exports.    
End Map.
Export Map.Exports.

Section eqMap.

  Variables (A B: Type)(f: A -> B).

  Lemma eqfwd:
    Map.well_defined f.
  Proof.
    move=> x y -> //=.
  Qed.

  Canonical eqMapMixin := mkMap eqfwd.
  Check eqMapMixin.
  Canonical eqMapType := Eval hnf in MapType (eqSetoidType A) (eqSetoidType B) eqMapMixin.

End eqMap.

Ltac eq_rewrite H :=
  do [ apply (setoid_eq_trans H) | apply setoid_eq_symm, (setoid_eq_trans (setoid_eq_symm H)), setoid_eq_symm ].

  

Section mapSetoid.
  Variables (dom cod: setoid).
  Check map.
  Definition eqmap (f g: map dom cod) :=
    forall x: dom, f x === g x.
  
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

  Canonical eqmapEquiv := mkEquiv eqmap_refl eqmap_symm eqmap_trans.

End mapSetoid.
Canonical mapSetoidMixin (dom cod: setoid):= mkSetoid (@eqmapEquiv dom cod).
Canonical mapSetoidType (dom cod: setoid) := Eval hnf in SetoidType (map dom cod) (mapSetoidMixin dom cod).
Notation "X --> Y" := (mapSetoidType X Y) (at level 70, right associativity).


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


Module Category.
  
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

      Canonical eqhomEquiv := mkEquiv eqhom_refl eqhom_symm eqhom_trans.
    End eqhomEquiv.

    Canonical homSetoidMixin (X Y: obj meta) := mkSetoid (@eqhomEquiv X Y).
    Canonical homSetoidType (X Y: obj meta) := Eval hnf in SetoidType (hom X Y) (homSetoidMixin X Y).

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
    Notation category := type.
    Notation mkCategory := Mixin.
    Notation CatType M mg := (@pack M mg).
    Arguments homSetoidType {meta}(X Y).
    Notation Hom := homSetoidType.
  End Exports.

End Category.
Export Category.Exports.

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



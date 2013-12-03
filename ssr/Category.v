(* 
   Definitions of Structure of (Locally Small) Category.
 *)

Require Import 
Ssreflect.ssreflect
Ssreflect.ssrfun
Ssreflect.eqtype
Ssreflect.ssrbool

Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Locally Small Category *)
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
  Structure mixin_of (T: Type)(hom: T -> T -> setoid) :=
    Mixin
      { 
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
          hom;
          _: @class_of obj hom;
          _: Type;
          _: obj -> obj -> setoid}.
    Local Coercion obj: type >-> Sortclass.
    Local Coercion hom: type >-> Funclass.
    Variables (Obj: Type)(Hom: Obj -> Obj -> setoid)(t: type).

    Definition class :=
      let: Pack _ _ cat _ _ := t return class_of t in cat.

    Definition pack cat := @Pack Obj Hom cat Obj Hom.
    Definition clone :=
      fun cat & t -> Obj & phant_id (pack cat) t => cat.
  End ClassDef.

  Module Exports.
    Coercion obj: type >-> Sortclass.
    Coercion hom: type >-> Funclass.
    Notation Hom X Y := (@hom _ X Y). 
    Notation category := type.
    Notation CatMixin := Mixin.
    Notation CatType T c := (@pack T _ c).
  End Exports.
End Category.
Export Category.Exports.

Definition compose (C: category) :=
  @Category.comp _ _ (Category.class C).
Lemma composeE C x y z f g : @compose C x y z f g = @Category.comp _ _ (Category.class C) x y z f g.
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
  by case: C => ? ? [].
Qed.

Lemma compf1 (C: category):
  forall (X Y: C)(f: Hom X Y), (ident Y)•f === f.
Proof.
  by case: C => ? ? [].
Qed.

Lemma compA (C: category):
  forall (X Y Z W: C)(f: Hom X Y)(g: Hom Y Z)(h: Hom Z W),
    (h•g)•f === h•(g•f).
Proof.
  by case: C => ? ? [].
Qed.


Section OpCategory.
  Variable (C: category).

  Definition opHom := fun (X Y: C) => Hom Y X.
  Definition opCompose (X Y Z: C)(f: opHom X Y)(g: opHom Y Z) := f • g.
  Definition opIdent (X: C): opHom X X := ident X.
    
  Lemma opcat_comp_id_dom :
    Category.comp_id_dom opCompose opIdent.
  Proof.
    by move=> X Y f; apply compf1.
  Qed.           

  Lemma opcat_comp_id_cod :
    Category.comp_id_cod opCompose opIdent.
  Proof.
    by move=> X Y f; apply comp1f.
  Qed.           

  Lemma opcat_comp_assoc:
    Category.comp_assoc opCompose.
  Proof.
    by move=> X Y Z W f g h; apply setoid_eq_symm, compA.
  Qed.           
  
  Canonical OpCatMixin := CatMixin opcat_comp_id_dom opcat_comp_id_cod opcat_comp_assoc.
  Canonical OpCat := Eval hnf in CatType C OpCatMixin.

End OpCategory.


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

  Canonical SetsMixin := CatMixin sets_comp_id_dom sets_comp_id_cod sets_comp_assoc.
  Canonical Sets := Eval hnf in CatType Type SetsMixin.
End Sets.

Goal (plus 1 • S === S • plus 1).
Proof.
  by [].
Qed.

Goal (negb • negb === ident (bool: Sets)).
Proof.
  by move=> [] /=.
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
  Canonical SetoidsCatType := Eval hnf in CatType setoid SetoidsCatMixin.
End Setoids.


(* constructing below *)

(* Small Category *)
(* * MetaGraph *)
Module MetaGraph.

  Structure mixin_of (obj arr: setoid) :=
    Mixin
      { dom: arr --> obj;
        cod: arr --> obj }.

  Structure class_of (O A: Type) :=
    Class { base_obj: Setoid.class_of O;
            base_arr: Setoid.class_of A;
            mixin: mixin_of (Setoid.Pack base_obj O) (Setoid.Pack base_arr A) }.

  Section ClassDef.
    Structure type :=
      Pack
        { obj;
          arr;
          _: class_of obj arr;
          _: Type;
          _: Type }.
    Variables (O A: Type)(t: type).

    Definition class :=
      let: Pack _ _ mg _ _ := t return class_of (obj t) (arr t) in mg.

    (* Definition clone := fun mg & (obj t) -> O & (arr t) -> A & phant_id (pack mg) t => pack mg. *)
    Let xO := let: Pack O A _ _ _ := t in O.
    Let xA := let: Pack O A _ _ _ := t in A.
    Notation xclass := (class : class_of xO xA).

    Definition pack bo0 ba0 (m0: mixin_of (SetoidType O bo0) (SetoidType A ba0)) :=
      fun boT baT bo ba & phant_id (Setoid.class boT) bo & phant_id (Setoid.class baT) ba =>
        fun m & phant_id m0 m => Pack (@Class O A bo ba m) O A.

    Definition objSetoid := @Setoid.Pack (obj t) (base_obj xclass) xO.
    Definition arrSetoid := @Setoid.Pack (arr t) (base_arr xclass) xA.
    
  End ClassDef.

  Module Exports.
    Coercion objSetoid: type >-> Setoid.type.
    Coercion base_obj: class_of >-> Setoid.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Canonical objSetoid.
    Canonical arrSetoid.
    Notation mgObj := objSetoid.
    Notation mgArr := arrSetoid.
    Notation mgType := type.
    Notation MetaGraphMixin := Mixin.
    Notation MetaGraphType O A mg := (@pack O A _ _ mg _ _ _ _ id id _ id).
  End Exports.
End MetaGraph.
Export MetaGraph.Exports.
(* Definition obj mg := Eval hnf in MetaGraph.mgObj mg. *)
(* Definition mgArr mg := Eval hnf in MetaGraph.mgArr mg. *)
Definition dom mg := Eval hnf in @MetaGraph.dom (mgObj mg) (mgArr mg) (MetaGraph.class mg).
Definition cod mg := Eval hnf in @MetaGraph.cod (mgObj mg) (mgArr mg) (MetaGraph.class mg).


Module SmallCategory.
  
  Section homSetoid.

    Variable (meta: mgType).
    
    Definition hom (X Y: mgObj meta) :=
      { f : mgArr meta | dom meta f === X & cod meta f === Y }.

    Definition eqhom {X Y: mgObj meta}(f g: hom X Y) :=
      match f, g with
        | exist2 f' _ _, exist2 g' _ _ => f' === g'
      end.
    
    Section eqhomEquiv.

      Variables (X Y: mgObj meta).
      
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
             (comp: forall (X Y Z: mgObj meta),
                      (Hom X Y) --> (Hom Y Z) --> (Hom X Z))
             (id: forall (X: mgObj meta), Hom X X).
    Arguments comp {X Y Z}.
    Arguments id (X).

    Definition compose_id_dom :=
      forall (X Y: mgObj meta)(f: Hom X Y), comp (id X) f === f.

    Definition compose_id_cod :=
      forall (X Y: mgObj meta)(f: Hom X Y), comp f (id Y) === f.

    Definition compose_assoc :=
      forall (X Y Z W: mgObj meta)(f: Hom X Y)(g: Hom Y Z)(h: Hom Z W),
        comp f (comp g h) === comp (comp f g) h.

  End Properties.


  Structure mixin_of (meta: mgType) :=
    Mixin
      { mixin_base: Category.mixin_of (@homSetoidType meta) }.

  Structure class_of (O A: Type) :=
    Class { base: MetaGraph.class_of O A;
            mixin: mixin_of (MetaGraph.Pack base O A) }.

  Section ClassDef.
    Structure type :=
      Pack
        { obj;
          arr;
          _: class_of obj arr;
          _: Type;
          _: Type }.
    Variables (O A: setoid)(t: type).

    Definition class :=
      let: Pack _ _ c _ _ := t return class_of (obj t) (arr t) in c.

    Definition pack b0 (m0: mixin_of (MetaGraphType O A b0)) :=
      fun bT b & phant_id (MetaGraph.class bT) b  =>
        fun m & phant_id m0 m => Pack (@Class O A b m) O A.

    (* Definition clone := fun c & (meta t) -> M & phant_id (pack c) t => pack c. *)
    Let xO := let: Pack O' _ _ _ _ := t in O'.
    Let xA := let: Pack _ A' _ _ _ := t in A'.
    Notation xclass := (class : class_of xO xA).

    Definition mgType := @MetaGraph.Pack (obj t) (arr t) (base xclass) xO xA.
    Definition category := @Category.Pack (obj t) (@homSetoidType mgType) (@mixin_base mgType (mixin xclass)) xO (@homSetoidType mgType).
  End ClassDef.

  Module Import Exports.
    Coercion mixin_base : mixin_of >-> Category.mixin_of.
    Coercion base: class_of >-> MetaGraph.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion obj: type >-> Sortclass.
    Coercion mgType: type >-> MetaGraph.type.
    Canonical mgType.
    Coercion category: type >-> Category.type.
    Canonical category.
    Notation scategory := type.
    Notation sCatMixin := Mixin.
Check @pack.
    Notation sCatType mg cat := (@pack _ _ mg cat _ _ id _ id).
    Notation sHom sC X Y := (@homSetoidType (mgType sC) X Y).
    (* Notation sHom := homSetoidType. *)
    (* Check Category.hom. *)
  End Exports.

End SmallCategory.
Export SmallCategory.Exports.

Definition small_compose (C: scategory) := @compose (SmallCategory.category C).
Arguments small_compose {C X Y Z}(f g).
Definition small_ident C := @ident (SmallCategory.category C).
Arguments small_ident {C}(X).

Notation "f >>> g" := (small_compose f g)
                        (at level 60, right associativity).

Section sigSetoid.
  Variables (T: Type)(P: T -> Prop).
  Let S := {x: T | P x }.

  Definition sig_eq (x y: S) :=
    match x, y with
      | exist x' _, exist y' _ => x' = y'
    end.

  Lemma sig_eq_refl:
    Relation.reflexive sig_eq.
  Proof.
    by move=> [x ?] /=.
  Qed.

  Lemma sig_eq_symm:
    Relation.symmetric sig_eq.
  Proof.
    by move=> [x ?] [y ?] /=.
  Qed.

  Lemma sig_eq_trans:
    Relation.transitive sig_eq.
  Proof.
    move=> [x ?] [y ?] [z ?] /=; apply eqtrans.
  Qed.


  Canonical sigSetoidMixin := Eval hnf in SetoidMixin sig_eq_refl sig_eq_symm sig_eq_trans.
  Canonical sigSetoidType := Eval hnf in SetoidType S sigSetoidMixin.

End sigSetoid.


(* example of small category *)
Require Import Ssreflect.ssrnat.
Section nat_le_scat.
  Definition nat_le_pord := sigSetoidType (fun p => fst p <= snd p).

  Definition nlp_dom (p: nat_le_pord): nat :=
    let: exist (x,_) _ := p in x.
  
  Lemma nlp_dom_wd:
    Map.well_defined nlp_dom.
  Proof.
    by rewrite/Map.well_defined /setoid_eq;
    move=> [[x1 x2] Hx] [[y1 y2] Hy] /=; case.
  Qed.

  Canonical nlp_dom_MapMixin := MapMixin nlp_dom_wd.
  Canonical nlp_dom_Map := MapType nlp_dom_MapMixin.


  Definition nlp_cod (p: nat_le_pord): nat :=
    let: exist (_,y) _ := p in y.

  Lemma nlp_cod_wd:
    Map.well_defined nlp_cod.
  Proof.
    by rewrite/Map.well_defined /setoid_eq;
    move=> [[x1 x2] Hx] [[y1 y2] Hy] /=; case.
  Qed.

  Canonical nlp_cod_MapMixin := MapMixin nlp_cod_wd.
  Canonical nlp_cod_Map := Eval hnf in MapType nlp_cod_MapMixin.

  Canonical nlp_MGMixin := Eval hnf in MetaGraphMixin nlp_dom_Map nlp_cod_Map.
  Canonical nlp_MG := Eval hnf in MetaGraphType nat nat_le_pord nlp_MGMixin.

  Definition nlp_comp (n m p: nat):
    @SmallCategory.homSetoidType nlp_MG n m -> @SmallCategory.homSetoidType nlp_MG m p -> @SmallCategory.homSetoidType nlp_MG n p.
    rewrite/SmallCategory.homSetoidType /SmallCategory.hom /setoid_eq /=.
    move=> [[[? ?] /= ?] /= ? ?] [[[? ?] /= ?] /= ? ?] /=; subst.
    have H: n <= p; first by apply leq_trans with m.
    refine (exist2 _ _ (exist _ (n,p) H) _ _); reflexivity.
  Defined.

  Definition nlp_id (n: nat): 
    @SmallCategory.homSetoidType nlp_MG n n.
    rewrite/SmallCategory.homSetoidType /SmallCategory.hom /setoid_eq /=.
    refine (exist2 _ _ (exist _ (n,n) (leqnn n)) _ _ ); reflexivity.
  Defined.

  Lemma nlp_comp_id_dom:
    Category.comp_id_dom nlp_comp nlp_id.
  Proof.
    rewrite/Category.comp_id_dom /setoid_eq /= /SmallCategory.hom /=.
    move=> X Y [[[]]] /=; rewrite /setoid_eq /=.
          by move=> a b Hle Heqa Heqb; subst.
  Qed.

  Lemma nlp_comp_id_cod:
    Category.comp_id_cod nlp_comp nlp_id.
  Proof.
    rewrite/Category.comp_id_cod /setoid_eq /= /SmallCategory.hom /=.
    move=> X Y [[[]]] /=; rewrite /setoid_eq /=.
          by move=> a b Hle Heqa Heqb; subst.
  Qed.

  Lemma nlp_comp_assoc:
    Category.comp_assoc nlp_comp.
  Proof.
    rewrite/Category.comp_assoc /setoid_eq /= /SmallCategory.hom /SmallCategory.eqhom /= /setoid_eq /=.
           by move=> X Y Z W [[[? ?] /= ?] /= ? ?] [[[? ?] /= ?] /= ? ?] [[[? ?] /= ?] /= ? ?] /=; subst.
  Qed.

  Canonical nlpCatMixin := Eval hnf in CatMixin nlp_comp_id_dom nlp_comp_id_cod nlp_comp_assoc.
  Canonical nlpCatType := Eval hnf in CatType _ nlpCatMixin.

  Canonical nlpSCatMixin := Eval hnf in sCatMixin nlpCatMixin.
  Canonical nlpSCatType := Eval hnf in sCatType nlp_MGMixin nlpSCatMixin.

End nat_le_scat.

Check (fun (f: sHom nlpSCatType 1 2)(g: sHom nlpSCatType 2 3) => f >>> g: sHom nlpSCatType 1 3).

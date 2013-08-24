
Require Import Setoid Category Functor Natrans.

Set Implicit Arguments.

Section AdjunctionDef.
  Context (C D: Category)(F: Functor C D)(G: Functor D C).
  
  (* Homset-Definition *)
  Class Adjunction_Hom :=
    { adj_phi (X: C)(Y: D): (F X ⟶ Y) -> (X ⟶ G Y);
      adj_phi_inv (X: C)(Y: D): (X ⟶ G Y) -> (F X ⟶ Y);

      adj_phi_subst:
        forall (X: C)(Y: D)(f f': F X ⟶ Y),
          f == f' -> adj_phi X Y f == adj_phi X Y f';
      adj_phi_inv_subst:
        forall (X: C)(Y: D)(g g': X ⟶ G Y),
          g == g' -> adj_phi_inv X Y g == adj_phi_inv X Y g';

      adj_phi_iso:
        forall (X: C)(Y: D)(f: F X ⟶ Y),
          adj_phi_inv X Y (adj_phi X Y f) == f;
      adj_phi_inv_iso:
        forall (X: C)(Y: D)(g: X ⟶ G Y),
          adj_phi X Y (adj_phi_inv X Y g) == g;
      
      adj_phi_naturality:
        forall (X Y: C)(Z W: D)(f: X ⟶ Y)(g: F Y ⟶ Z)(h: Z ⟶ W),
          adj_phi X W (h◦g◦fmap f) == fmap h ◦ adj_phi Y Z g ◦ f }.

  Lemma adj_phi_inv_naturality:
    forall (adj_h: Adjunction_Hom)
       (X Y: C)(Z W: D)(f: X ⟶ Y)(g: Y ⟶ G Z)(h: Z ⟶ W),
      adj_phi_inv X W (fmap h◦g◦ f) == h ◦ adj_phi_inv Y Z g ◦ fmap f.
  Proof.
    simpl; intros.
    equiv_trns_with
    (adj_phi_inv X W (fmap h ◦ (adj_phi Y Z (adj_phi_inv Y Z g)) ◦ f));
      [ apply adj_phi_inv_subst | ].
    - apply compose_subst_fst;
      apply compose_subst_snd;
      equiv_symm; auto; apply adj_phi_inv_iso.
    - eapply transitivity; [ | apply adj_phi_iso ].
      apply adj_phi_inv_subst.
      equiv_symm; auto; apply adj_phi_naturality.
  Qed.
  

  (* Unit definition *)
  Class Adjunction_Unit :=
    { adj_unit:> Natrans (IdFunctor C) (ComposeFunctor F G);

      adj_dc {X: C}{Y: D}(f: X ⟶ G Y): F X ⟶ Y;
      adj_dc_property:
        forall (X: C)(Y: D)(f: X ⟶ G Y),
          fmap (adj_dc f) ◦ adj_unit X == f;
      adj_dc_uniqueness:
        forall (X: C)(Y: D)(f: X ⟶ G Y)(h: F X ⟶ Y),
          fmap h ◦ adj_unit X == f -> adj_dc f == h }.
  Lemma adj_dc_subst:
    forall (adj_u: Adjunction_Unit)(X: C)(Y: D)(f f': X ⟶ G Y),
      f == f' -> adj_dc f == adj_dc f'.
  Proof.
    intros.
    apply adj_dc_uniqueness.
    equiv_trns_with f';
      [ apply adj_dc_property | equiv_symm; auto; assumption ].
  Qed.
  
  (* Counit definition *)
  Class Adjunction_Counit :=
    { adj_counit:> Natrans (ComposeFunctor G F) (IdFunctor D);

      adj_cd {X: C}{Y: D}(f: F X ⟶ Y): X ⟶ G Y;
      adj_cd_property:
        forall (X: C)(Y: D)(f: F X ⟶ Y),
          adj_counit Y ◦ fmap (adj_cd f) == f;
      adj_cd_uniqueness:
        forall (X: C)(Y: D)(f: F X ⟶ Y)(h: X ⟶ G Y),
          adj_counit Y ◦ fmap h == f -> adj_cd f == h }.
  Lemma adj_cd_subst:
    forall (adj_c: Adjunction_Counit)(X: C)(Y: D)(f f': F X ⟶ Y),
      f == f' -> adj_cd f == adj_cd f'.
  Proof.
    intros.
    apply adj_cd_uniqueness.
    equiv_trns_with f';
      [ apply adj_cd_property | equiv_symm; auto; assumption ].
  Qed.

  
  (* Equivalency of Definitions *)
  (* 1. Unit -> Hom *)
  Program Instance Adj_Unit_Hom (adj_u: Adjunction_Unit): Adjunction_Hom :=
    { adj_phi X Y f := fmap f ◦ adj_unit X;
      adj_phi_inv X Y f := adj_dc f }.
  Next Obligation.
    intros.
    apply compose_subst_snd; apply ap_preserve_eq; assumption.
  Qed.  
  Next Obligation.
    apply adj_dc_subst.
    auto.
  Qed.  
  Next Obligation.
    intros.
    apply adj_dc_uniqueness.
    equiv_refl; auto.
  Qed.
  Next Obligation.
    intros.
    apply adj_dc_property.
  Qed.
  Next Obligation.
    simpl; intros.
    equiv_trns_with ((fmap h◦fmap g◦fmap (fmap f))◦adj_unit X);
      [ apply compose_subst_snd | ].
    - simpl.
      apply transitivity with (fmap h ◦ fmap (g ◦ fmap f));
        [ equiv_symm; auto; apply fmap_compose | ].
      apply compose_subst_fst;
        equiv_symm; auto;
        apply fmap_compose.
    - equiv_symm; auto.
      apply transitivity with (fmap h◦(fmap g◦fmap (fmap f))◦adj_unit X);
        [ apply compose_subst_fst
        | equiv_symm; auto; apply compose_assoc ].
      eapply transitivity; [ apply compose_assoc | ].
      eapply transitivity; [ | equiv_symm; auto; apply compose_assoc ].
      apply compose_subst_fst; apply (naturality (Natrans:=adj_unit)).
  Qed.

  (* 2. Hom -> Unit *)
  (* First, make Unit *)
  Program Instance Adj_Hom_Unit_Natrans (adj_h: Adjunction_Hom)
  : Natrans (IdFunctor C) (ComposeFunctor F G) :=
    { natrans X := adj_phi X (F X) id }.
  Next Obligation.
    simpl; intros.
    simpl.
    eapply transitivity; [ | apply id_dom ].
    equiv_trns_with
    (fmap (Functor:=ComposeFunctor F G) f ◦ adj_phi X (F X) id ◦ id);
      [ | equiv_symm; auto; apply compose_assoc ].
    eapply transitivity; [ | apply adj_phi_naturality ].
    equiv_symm; auto.
    eapply transitivity; [ apply adj_phi_subst | ].
    - equiv_trns_with (fmap f◦fmap id); [ | ].
      + apply compose_subst_fst; apply id_cod.
      + equiv_trns_with (fmap (f◦id));
        [ apply fmap_compose | apply ap_preserve_eq; apply id_dom ].
    - eapply transitivity;
      [ | apply id_cod ].
      eapply transitivity;
        [ | apply compose_subst_snd; apply fmap_id ].
      eapply transitivity;
        [ | apply adj_phi_naturality ].
      apply adj_phi_subst.
      equiv_symm; auto.
      equiv_trns_with (id◦fmap f);
        [ apply id_cod | apply id_cod ].
  Qed.

  (* Then, prove. *)
  Program Instance Adj_Hom_Unit (adj_h: Adjunction_Hom): Adjunction_Unit :=
    { adj_unit := Adj_Hom_Unit_Natrans adj_h; 
      adj_dc := adj_phi_inv }.
  Next Obligation.
    simpl; intros.
    equiv_symm; auto.
    eapply transitivity;
      [ | apply id_dom ].
    eapply transitivity;
      [ | equiv_symm; auto; apply compose_assoc ].
    eapply transitivity;
      [ | apply adj_phi_naturality  ].
    equiv_symm; auto.
    eapply transitivity;
      [ apply adj_phi_subst | ].
    eapply transitivity;
      [ apply compose_subst_fst; apply id_cod | ].
    eapply transitivity;
      [ apply compose_subst_fst; apply fmap_id | ].
    apply id_dom.
    apply adj_phi_inv_iso.
  Qed.
  Next Obligation.
    intros; simpl in *.
    eapply transitivity;
      [ apply adj_phi_inv_subst; equiv_symm; auto; apply H | ].
    eapply transitivity;
      [ apply adj_phi_inv_subst; equiv_symm; auto; apply id_dom | ].
    eapply transitivity;
      [ apply adj_phi_inv_subst; apply compose_assoc | ].
    eapply transitivity;
      [ apply adj_phi_inv_naturality | ].
    eapply transitivity;
      [ repeat apply compose_subst_fst; apply fmap_id | ].
    eapply transitivity;
      [ apply compose_subst_fst; apply id_dom | ].
    eapply transitivity;
      [ apply compose_subst_fst; apply adj_phi_iso | ].
    apply id_dom.
  Qed.
  
  
  (* 3. Counit -> Hom *)
  Program Instance Adj_Counit_Hom (adj_c: Adjunction_Counit): Adjunction_Hom :=
    { adj_phi X Y f := adj_cd f;
      adj_phi_inv X Y f := adj_counit Y ◦ fmap f }.
  Next Obligation.
    apply adj_cd_subst; auto.
  Qed.
  Next Obligation.
    intros.
    apply compose_subst_fst; apply ap_preserve_eq; assumption.
  Qed.
  Next Obligation.
    intros.
    apply adj_cd_property.
  Qed.
  Next Obligation.
    intros.
    apply adj_cd_uniqueness.
    equiv_refl; auto.
  Qed.
  Next Obligation.
    simpl.
    intros.
    eapply transitivity;
      [ apply adj_cd_uniqueness | apply compose_assoc ].
    eapply transitivity;
      [ apply compose_subst_fst; equiv_symm; auto;
        apply fmap_compose
      | ].
    eapply transitivity;
      [ | apply compose_assoc ].
    eapply transitivity;
      [ equiv_symm; auto; apply compose_assoc | ].
    apply compose_subst_snd.
    eapply transitivity;
      [ apply compose_subst_fst;
               equiv_symm; auto; apply fmap_compose | ].
    eapply transitivity;
      [ equiv_symm; auto; apply compose_assoc | ].
    eapply transitivity;
      [ apply compose_subst_snd | ].
    simpl.
    apply (naturality (Natrans:=adj_counit)).
    simpl.
    eapply transitivity;
      [ apply compose_assoc | ].
    apply compose_subst_fst; apply adj_cd_property.
  Qed.
  
  
  (* 4. Hom -> Counit *)
  (* First, make Counit *)
  Program Instance Adj_Hom_Counit_Natrans (adj_h: Adjunction_Hom)
  : Natrans (ComposeFunctor G F) (IdFunctor D) :=
    { natrans X := adj_phi_inv (G X) X id }.
  Next Obligation.
    simpl; intros.
    eapply transitivity;
      [ | apply id_dom ].
    eapply transitivity;
      [ | apply compose_subst_fst; apply fmap_id ].
    eapply transitivity;
      [ | equiv_symm; auto; apply compose_assoc ].
    eapply transitivity;
      [ | apply adj_phi_inv_naturality ].
    equiv_symm; auto.
    eapply transitivity;
      [ | apply id_cod ].
    eapply transitivity;
      [ | apply adj_phi_inv_naturality ].
    apply adj_phi_inv_subst.
    eapply transitivity;
      [ equiv_symm; auto; apply compose_assoc | ].
    eapply transitivity; [ apply id_dom | ].
    eapply transitivity; [ apply id_dom | ].
    equiv_symm; auto.
    eapply transitivity; [ apply compose_subst_snd; apply fmap_id | ].
    eapply transitivity; [ apply id_cod | ].
    eapply transitivity; [ apply id_cod | ].
    equiv_refl; auto.
  Qed.
  
  (* Then, prove. *)
  Program Instance Adj_Hom_Counit (adj_h: Adjunction_Hom): Adjunction_Counit :=
    { adj_counit := Adj_Hom_Counit_Natrans adj_h; 
      adj_cd := adj_phi }.
  Next Obligation.
    simpl in *; intros.
    eapply transitivity;
      [ equiv_symm; auto; apply id_cod | ].
    eapply transitivity;
      [ equiv_symm; auto; apply adj_phi_inv_naturality | ].
    eapply transitivity;
      [ | apply adj_phi_iso ].
    apply adj_phi_inv_subst.
    eapply transitivity;
      [ apply compose_subst_snd; apply fmap_id | ].
    eapply transitivity; [ apply id_cod | ].
    eapply transitivity; [ apply id_cod | ].
    equiv_refl; auto.
  Qed.
  Next Obligation.
    simpl; intros.
    eapply transitivity;
      [ apply adj_phi_subst; equiv_symm; auto; apply H | ].
    eapply transitivity;
      [ apply adj_phi_subst; equiv_symm; auto; apply id_cod | ].
    eapply transitivity;
      [ apply adj_phi_naturality | ].
    eapply transitivity;
      [ equiv_symm; auto; apply compose_assoc | ].
    eapply transitivity;
      [ apply compose_subst_snd | apply id_cod ].
    eapply transitivity;
      [ apply compose_subst_snd; apply fmap_id | ].
    eapply transitivity;
      [ apply id_cod | ].
    apply adj_phi_inv_iso.
  Qed.
  
  
  (*
       以下，直接構成しようと試みるもうまく行かなかったため，
       とっても妥協しての定義である．
   *)
  (* 5. Unit -> Counit *)
  Program Instance Adj_Unit_Counit (adj_u: Adjunction_Unit)
  : Adjunction_Counit := Adj_Hom_Counit (Adj_Unit_Hom adj_u).

  (* 6. Counit -> Unit *)
  Program Instance Adj_Counit_Unit (adj_c: Adjunction_Counit)
  : Adjunction_Unit := Adj_Hom_Unit (Adj_Counit_Hom adj_c).

End AdjunctionDef.


Program Instance ADJ_phi_Setoid
        (C D: Category)(F: Functor C D)(G: Functor D C)
        (adj: Adjunction_Hom F G)(X: C)(Y: D)
: Map (F X ⟶ Y) (X ⟶ G Y) :=
  { ap f := adj_phi X Y f }.
Next Obligation.
  intros.
  apply adj_phi_subst; assumption.
Qed.


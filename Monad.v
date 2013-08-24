
Require Import Setoid Category Functor Natrans Adjunction.

Set Implicit Arguments.

Class Monad {C: Category}(T: Functor C C) :=
  { m_unit:> Natrans (IdFunctor C) T;
    m_join:> Natrans (ComposeFunctor T T) T;

    m_join_unit_T:
      forall (X: C),
        (m_join X) ◦ (m_unit (T X)) == id;
    m_join_T_unit:
      forall (X: C),
        (m_join X) ◦ fmap (m_unit X) == id;
    m_join_join:
      forall (X: C),
        (m_join X) ◦ (m_join (T X)) == (m_join X) ◦ fmap (m_join X) }.


Program Instance Adj_Monad_join
        {C D: Category}{F: Functor C D}{G: Functor D C}
        (adj_u: Adjunction_Unit F G)
: Natrans (ComposeFunctor (ComposeFunctor F G) (ComposeFunctor F G))
          (ComposeFunctor F G) :=
  { natrans X :=
      fmap (adj_counit (Adjunction_Counit:=Adj_Unit_Counit adj_u) (F X)) }.
Next Obligation.
  simpl; intros.
  remember (fmap f) as Ff. 
  eapply transitivity;
    [ apply fmap_compose | ].
  eapply transitivity;
    [ | equiv_symm; auto; apply fmap_compose ].
  apply ap_preserve_eq.
  equiv_symm; auto.
  eapply transitivity;
    [ equiv_symm; auto; apply adj_dc_uniqueness | ].
  simpl.
  eapply transitivity;
    [ apply compose_subst_snd; equiv_symm; auto;
      apply fmap_compose
    | ].
  eapply transitivity;
    [ apply compose_assoc | ].
  eapply transitivity;
    [ apply compose_subst_fst; apply adj_dc_property
    | ].
  apply id_dom.
  apply adj_dc_uniqueness.
  simpl.
  eapply transitivity;
    [ apply compose_subst_snd; equiv_symm; auto;
      apply fmap_compose
    | ].
  eapply transitivity;
    [ apply compose_assoc | ].
  eapply transitivity;
    [ apply compose_subst_fst; equiv_symm; auto;
      apply (naturality (Natrans:=adj_unit (Adjunction_Unit:=adj_u)))
    | ].
  eapply transitivity;
    [ equiv_symm; auto; apply compose_assoc | ].
  eapply transitivity;
    [ apply compose_subst_snd; apply adj_dc_property
    | ].
  apply id_cod.
Qed.    


Program Instance Adj_Monad
        {C D: Category}{F: Functor C D}{G: Functor D C}
        (adj_h: Adjunction_Hom F G)
: Monad (ComposeFunctor F G) :=
  { m_unit := adj_unit (Adjunction_Unit:=Adj_Hom_Unit adj_h);
    m_join := Adj_Monad_join (Adj_Hom_Unit adj_h) }.
Next Obligation.
  simpl; intros.
  equiv_symm; auto.
  eapply transitivity; [ | apply id_dom ].
  eapply transitivity; [ | equiv_symm; auto; apply compose_assoc ].
  eapply transitivity; [ | apply adj_phi_naturality ].
  eapply transitivity;
    [ equiv_symm; auto; apply adj_phi_inv_iso | ].
  apply adj_phi_subst.
  equiv_symm; auto.
  eapply transitivity;
    [ apply compose_subst_fst; apply id_cod | ].
  eapply transitivity;
    [ apply compose_subst_fst; apply fmap_id | ].
  apply id_dom.
Qed.
Next Obligation.
  simpl; intros.
  eapply transitivity; [ apply fmap_compose | ].
  apply transitivity with (fmap id);
    [ apply ap_preserve_eq | apply fmap_id ].
  equiv_symm; auto.
  eapply transitivity; [ | apply id_cod ].
  eapply transitivity; [ | apply adj_phi_inv_naturality ].
  eapply transitivity;
    [ equiv_symm; auto; apply adj_phi_iso | ].
  apply adj_phi_inv_subst.
  equiv_symm; auto.
  eapply transitivity;
    [ apply compose_subst_fst; apply id_cod | ].
  eapply transitivity;
    [ apply compose_subst_snd; apply fmap_id | ].
  apply id_cod.
Qed.
Next Obligation.
  simpl; intros.
  equiv_symm; auto.
  eapply transitivity; [ apply fmap_compose | ].
  eapply transitivity; [ apply ap_preserve_eq | ].
  - equiv_symm; auto.
    eapply transitivity; [ | apply id_cod ].
    eapply transitivity; [ | apply adj_phi_inv_naturality ].
    equiv_symm; auto.
    eapply transitivity; [ apply adj_phi_inv_subst | ].
    eapply transitivity; [ apply compose_subst_fst; apply id_cod | ].
    eapply transitivity; [ apply compose_subst_snd; apply fmap_id | ].
    eapply transitivity; [ apply id_cod | ].
    equiv_symm; auto.
    eapply transitivity; [ | apply id_dom ].
    eapply transitivity; [ | apply id_dom ].
    equiv_symm; auto.
    apply compose_assoc.
    eapply transitivity; [ apply adj_phi_inv_naturality | ].
    apply compose_subst_fst.
    eapply transitivity;
      [ apply compose_subst_fst; apply fmap_id | apply id_dom ].
  - equiv_symm; auto.
    apply fmap_compose.
Qed.


Class KT {C: Category}(T: C -> C) :=
  { ret {X: C}: X ⟶ T X;
    bind {X Y: C}: (X ⟶ T Y) -> (T X ⟶ T Y);
    
    bind_subst:
      forall {X Y: C}(f f': X ⟶ T Y),
        f == f' -> bind f == bind f';

    bind_ret_id:
      forall (X: C),
        bind (ret (X:=X)) == id;
    bind_f_ret_f:
      forall (X Y: C)(f: X ⟶ T Y),
        bind f ◦ ret == f;
    bind_assoc:
      forall (X Y Z: C)(f: X ⟶ T Y)(g: Y ⟶ T Z),
        bind g◦bind f == bind (bind g◦f) }.


Program Instance MonadKT `(monad: Monad): KT fobj :=
  { ret X := m_unit X;
    bind X Y f := m_join Y ◦ fmap f }.
Next Obligation.
  intros.
  apply compose_subst; [ | equiv_refl; auto ].
  apply ap_preserve_eq.
  apply H.
Qed.
Next Obligation.
  intros.
  apply m_join_T_unit.
Qed.
Next Obligation.
  intros.
  apply transitivity with (m_join Y ◦ fmap f ◦ m_unit X);
    [ apply compose_assoc | ].
  apply transitivity with (m_join Y ◦ (m_unit (T Y)) ◦ fmap f);
    [ apply compose_subst_fst;
             equiv_symm; auto; apply naturality | ].
  apply transitivity with ((m_join Y ◦ m_unit (T Y)) ◦ fmap f);
    [ equiv_symm; auto;  apply compose_assoc | ].
  simpl.
  apply transitivity with (id ◦ f); 
    [ apply compose_subst_snd; apply m_join_unit_T | apply id_cod ].
Qed.
Next Obligation.
  intros.
  equiv_symm; auto.
  apply transitivity
  with ((m_join Z ◦ m_join (T Z)) ◦ (fmap (fmap g) ◦ fmap f)); auto.
  - equiv_symm; auto.
    eapply transitivity; [ apply compose_subst | ].
    + apply fmap_compose.
    + apply m_join_join.
    + apply transitivity
      with ((m_join Z ◦ fmap (m_join Z)) ◦ fmap (fmap g) ◦ fmap f);
      [ apply compose_subst_fst; equiv_symm; auto; apply fmap_compose | ].
      eapply transitivity; [ apply compose_assoc | ].
      apply compose_subst_fst.
      eapply transitivity; [ equiv_symm; auto; apply compose_assoc | ].
      eapply transitivity; [ apply compose_subst_snd; apply fmap_compose | ].
      apply fmap_compose.
  - eapply transitivity; [ | apply compose_assoc ].
    eapply transitivity; [ equiv_symm; auto; apply compose_assoc | ].
    apply compose_subst_snd.
    eapply transitivity; [ apply compose_assoc | ].
    eapply transitivity; [ | equiv_symm; auto; apply compose_assoc ].
    apply compose_subst_fst.
    apply (naturality (Natrans:=m_join)).
Qed.

Program Instance KT_fmap_Map
        (C: Category)(T: C -> C)(kt: KT T)(X Y: C)
: Map (X ⟶ Y)
      (T X ⟶ T Y) :=
  { ap f := bind (ret ◦ f) }.
Next Obligation.
  intros.
  apply bind_subst.
  apply compose_subst; [ apply Heq | equiv_refl; auto ].
Qed.

Program Instance KTFunctor {C: Category}{T: C -> C}(kt: KT T): Functor C C :=
  { fobj := T;
    fmap X Y := KT_fmap_Map C T kt X Y}.
Next Obligation.
  simpl; intros.
  apply transitivity with (bind ret);
    [ apply bind_subst; apply id_dom | apply bind_ret_id ].
Qed.
Next Obligation.
  simpl; intros.
  eapply transitivity; [ apply bind_assoc | ].
  apply bind_subst.
  eapply transitivity; [ | apply compose_assoc ].
  eapply transitivity; [ equiv_symm; auto; apply compose_assoc | ].
  apply compose_subst_snd; apply bind_f_ret_f.
Qed.

Program Instance KTNatrans_unit
        {C: Category}{T: C -> C}(kt: KT T)
: Natrans (IdFunctor C) (KTFunctor kt) :=
  { natrans X := ret }.
Next Obligation.
  simpl; intros.
  equiv_symm; auto; apply bind_f_ret_f.
Qed.

Program Instance KTNatrans_join
        {C: Category}{T: C -> C}(kt: KT T)
: Natrans (ComposeFunctor (KTFunctor kt) (KTFunctor kt)) (KTFunctor kt):=
  { natrans X := bind id }.
Next Obligation.
  simpl; intros.
  eapply transitivity; [ apply bind_assoc | ].
  eapply transitivity; [ | equiv_symm; auto; apply bind_assoc ].
  apply bind_subst.
  eapply transitivity; [ equiv_symm; auto; apply compose_assoc | ].
  eapply transitivity; [ apply compose_subst_snd; apply bind_f_ret_f | ].
  eapply transitivity; [ apply id_cod | equiv_symm; auto; apply id_dom ].
Qed.

Program Instance KTMonad
        {C: Category}{T: C -> C}(kt: KT T)
: Monad (KTFunctor kt).
Next Obligation.
  simpl; intros.
  apply bind_f_ret_f.
Qed.
Next Obligation.
  simpl; intros.
  eapply transitivity; [ apply bind_assoc | ].
  eapply transitivity; [ | apply bind_ret_id ].
  apply bind_subst.
  eapply transitivity; [ | apply id_cod ].
  eapply transitivity; [ equiv_symm; auto; apply compose_assoc | ].
  apply compose_subst_snd; apply bind_f_ret_f.
Qed.
Next Obligation.
  simpl; intros.
  eapply transitivity; [ apply bind_assoc | ].
  eapply transitivity; [ | equiv_symm; auto; apply bind_assoc ].
  apply bind_subst.
  eapply transitivity; [ apply id_dom | ].
  eapply transitivity; [ | apply compose_assoc ].
  equiv_symm; auto.
  eapply transitivity;
    [ apply compose_subst_snd; apply bind_f_ret_f 
    | apply id_cod ].
Qed.


Definition KTCompose {C: Category}{T: C -> C}(kt: KT T)
           (X Y Z: C)(f: X ⟶ T Y)(g: Y ⟶ T Z): X ⟶ T Z :=
  bind g ◦ f.
Hint Unfold KTCompose.

Program Instance KT_KleisliCategory
        {C: Category}{T: C -> C}(kt: KT T)
: Category :=
  { obj := obj;
    arr X Y := X ⟶ T Y;
    
    compose X Y Z f g := bind g ◦ f;
    id X := ret }.
Next Obligation.
  simpl; intros.
  eapply transitivity; [ apply compose_subst_snd;
                           equiv_symm; auto; apply bind_assoc
                    | apply compose_assoc ].
Qed.      
Next Obligation.
  simpl; intros.
  apply compose_subst; [ | apply bind_subst ]; auto.
Qed.
Next Obligation.
  simpl; intros.
  apply bind_f_ret_f.
Qed.
Next Obligation.
  simpl; intros.
  eapply transitivity;
    [ apply compose_subst_snd; apply bind_ret_id | apply id_cod ].
Qed.

Program Instance KleisliCategory
        {C: Category}{T: Functor C C}(m: Monad T)
: Category := KT_KleisliCategory (MonadKT m).


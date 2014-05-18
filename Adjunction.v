Require Import 
Ssreflect.ssreflect
COC.Setoid COC.Category COC.Functor COC.Natrans.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

Section AdjunctionDef.
  Context (C D: Category)(F: Functor C D)(G: Functor D C).
  
  (* F -| G : C -> D *)

  (* Homset-Definition *)
  (* 
       F X --> Y
     =============
       X --> G Y
   *)
  Class Adjunction_Hom :=
    { adj_h_phi {X: C}{Y: D}: Map (F X --> Y) (X --> G Y);
      adj_h_phi_inv {X: C}{Y: D}: Map (X --> G Y) (F X --> Y);

      adj_h_phi_iso:
        forall (X: C)(Y: D)(f: F X --> Y),
          adj_h_phi_inv (adj_h_phi f) === f;
      adj_h_phi_inv_iso:
        forall (X: C)(Y: D)(g: X --> G Y),
          adj_h_phi (adj_h_phi_inv g) === g;
      
      adj_h_phi_naturality:
        forall (X Y: C)(Z W: D)(f: X --> Y)(g: F Y --> Z)(h: Z --> W),
          adj_h_phi (h • g • fmap F f) === fmap G h • adj_h_phi g • f }.

  Lemma adj_h_phi_inv_naturality:
    forall (adj_h: Adjunction_Hom)
       (X Y: C)(Z W: D)(f: X --> Y)(g: Y --> G Z)(h: Z --> W),
      adj_h_phi_inv (fmap G h•g• f) === h • adj_h_phi_inv g • fmap F f.
  Proof.
    move=> adj_h X Y Z W f g h.
    apply transitivity with
    (adj_h_phi_inv (fmap G h • (adj_h_phi (adj_h_phi_inv g)) • f));
      [ apply map_preserve_eq | ].
    - apply compose_subst_fst;
      apply compose_subst_snd;
      apply symmetry, adj_h_phi_inv_iso.
    - eapply transitivity; [ | apply adj_h_phi_iso ].
      apply map_preserve_eq;
      apply symmetry, adj_h_phi_naturality.
  Qed.
  

  (* Unit definition *)
  Class Adjunction_Unit
        (adj_u_unit: Natrans (IdFunctor C) (ComposeFunctor F G)) :=
    { adj_dc {X: C}{Y: D}: Map (X --> G Y) (F X --> Y);
      adj_dc_property:
        forall (X: C)(Y: D)(f: X --> G Y),
          fmap G (adj_dc f) • adj_u_unit X === f;
      adj_dc_uniqueness:
        forall (X: C)(Y: D)(f: X --> G Y)(h: F X --> Y),
          fmap G h • adj_u_unit X === f -> adj_dc f === h }.

  Lemma adj_dc_subst:
    forall `(H: Adjunction_Unit adj_u_unit)(X: C)(Y: D)(f f': X --> G Y),
      f === f' -> adj_dc f === adj_dc f'.
  Proof.
    move=> adj_u_unit H X Y f f' Heq.
    apply adj_dc_uniqueness.
    apply transitivity with f'; [| apply symmetry; assumption].
    apply adj_dc_property.
  Qed.
  
  (* Counit definition *)
  Class Adjunction_Counit
        (adj_c_counit: Natrans (ComposeFunctor G F) (IdFunctor D)) :=
    { adj_cd {X: C}{Y: D}: Map (F X --> Y) (X --> G Y);
      adj_cd_property:
        forall (X: C)(Y: D)(f: F X --> Y),
          adj_c_counit Y • fmap F (adj_cd f) === f;
      adj_cd_uniqueness:
        forall (X: C)(Y: D)(f: F X --> Y)(h: X --> G Y),
          adj_c_counit Y • fmap F h === f -> adj_cd f === h }.

  Lemma adj_cd_subst:
    forall `(H: Adjunction_Counit adj_c_counit)(X: C)(Y: D)(f f': F X --> Y),
      f === f' -> adj_cd f === adj_cd f'.
  Proof.
    move=> counit H X Y f f' Heq.
    apply adj_cd_uniqueness.
    apply transitivity with f'; [| apply symmetry; assumption].
    apply adj_cd_property.
  Qed.

  
  (* Equivalency of Definitions *)
  (* 1. Unit -> Hom *)
  Program Instance Adj_Unit_Hom
  `(Hu: Adjunction_Unit adj_u_unit): Adjunction_Hom :=
    { adj_h_phi X Y :=
        {| map_function f := fmap G f • adj_u_unit X |};
      adj_h_phi_inv X Y := adj_dc }.
  Next Obligation.
    apply compose_subst_snd; apply map_preserve_eq; assumption.
  Qed.  
  Next Obligation.
    by apply adj_dc_uniqueness; apply reflexivity.
  Qed.
  Next Obligation.
    by apply adj_dc_property.
  Qed.
  Next Obligation.
    eapply transitivity;
    [ apply compose_subst_snd; apply symmetry, fmap_compose |].
    eapply transitivity; [ apply compose_assoc |].
    apply compose_subst_fst.
    eapply transitivity;
      [apply compose_subst_snd; apply symmetry, fmap_compose |].
    eapply transitivity; [apply compose_assoc |].
    eapply transitivity;
      [apply compose_subst_fst |].
    apply symmetry.
    apply (@naturality _ _ _ _ adj_u_unit).
    by apply symmetry, compose_assoc.
  Qed.

  (* 2. Hom -> Unit *)
  (* First, make Unit *)
  Program Definition Adj_Hom_Unit_Natrans (adj_h: Adjunction_Hom)
  : Natrans (IdFunctor C) (ComposeFunctor F G) :=
    {| natrans X := adj_h_phi id |}.
  Next Obligation.
    apply transitivity with
    (fmap (ComposeFunctor F G) f • adj_h_phi id • id);
    [| eapply transitivity;
       [ apply symmetry, compose_assoc |]; apply id_dom].
    eapply transitivity; [ | apply adj_h_phi_naturality ].
    apply transitivity with (adj_h_phi (fmap F f)).
    - apply symmetry.
      apply transitivity with (adj_h_phi (id•id•fmap F f)).
      + apply map_preserve_eq.
        eapply transitivity; [ apply symmetry, id_cod |].
        eapply transitivity;
          [| apply compose_assoc ]; apply compose_subst_snd;
          apply symmetry, id_cod.
      + eapply transitivity; [apply adj_h_phi_naturality |].
        eapply transitivity; [| apply id_cod ];
        apply compose_subst_snd, fmap_id.
    - apply map_preserve_eq.
      apply transitivity with (fmap F f•id);
        [ apply symmetry, id_dom | apply compose_subst_fst].
      apply symmetry.
      apply transitivity with (fmap F id);
        [ apply id_cod | apply fmap_id ].
  Qed.

  (* Then, prove. *)
  Program Instance Adj_Hom_Unit (adj_h: Adjunction_Hom)
  : Adjunction_Unit (Adj_Hom_Unit_Natrans adj_h) :=
    { adj_dc := @adj_h_phi_inv adj_h }.
  Next Obligation.
    eapply transitivity; [ apply symmetry, id_dom |].
    eapply transitivity; [ apply compose_assoc |].
    eapply transitivity; [ apply symmetry, adj_h_phi_naturality |].
    eapply transitivity;
      [| apply adj_h_phi_inv_iso ]; apply map_preserve_eq.
    eapply transitivity;
      [ apply compose_subst_fst; apply id_cod |].
    eapply transitivity;
      [ apply compose_subst_fst; apply fmap_id | apply id_dom ].
  Qed.
  Next Obligation.
    eapply transitivity;
    [ apply symmetry, map_preserve_eq, H |].
    eapply transitivity;
    [ apply symmetry, map_preserve_eq, id_dom |].
    eapply transitivity;
    [ apply map_preserve_eq, compose_assoc |].
    eapply transitivity;
    [ apply adj_h_phi_inv_naturality |].
    apply transitivity with (h•id); [| apply id_dom ];
    apply compose_subst_fst;
    eapply transitivity; [| apply fmap_id ].
    eapply transitivity; [ apply compose_subst_snd | apply id_cod  ];
    apply adj_h_phi_iso.
  Qed.
  
  
  (* 3. Counit -> Hom *)
  Program Instance Adj_Counit_Hom
          `(Hc: Adjunction_Counit adj_c_counit): Adjunction_Hom :=
    { adj_h_phi X Y := adj_cd;
      adj_h_phi_inv X Y := 
        {| map_function f := adj_c_counit Y • fmap F f |} }.
  Next Obligation.
    by apply compose_subst_fst, map_preserve_eq, Heq.
  Qed.
  Next Obligation.
    by apply adj_cd_property.
  Qed.
  Next Obligation.
    by apply adj_cd_uniqueness; apply reflexivity.
  Qed.
  Next Obligation.
    apply adj_cd_uniqueness.
    eapply transitivity;
      [apply symmetry, compose_subst_fst, fmap_compose |].
    eapply transitivity;
      [apply symmetry, compose_assoc |].
    eapply transitivity;
      [apply symmetry, compose_subst_fst, fmap_compose |].
    eapply transitivity; [apply symmetry, compose_assoc |].
    eapply transitivity; [| apply compose_assoc]; apply compose_subst_snd.
    eapply transitivity; [ apply compose_subst_snd |].
    apply (@naturality _ _ _ _ adj_c_counit).
    eapply transitivity; [ apply compose_assoc |].
    apply compose_subst; [ apply adj_cd_property |  apply reflexivity ].
  Qed.
  
  
  (* 4. Hom -> Counit *)
  (* First, make Counit *)
  Program Definition Adj_Hom_Counit_Natrans (adj_h: Adjunction_Hom)
  : Natrans (ComposeFunctor G F) (IdFunctor D) :=
    {| natrans X := adj_h_phi_inv id |}.
  Next Obligation.
    (* adj_h_phi_inv (fmap G h•g• f) === h • adj_h_phi_inv g • fmap F f *)
    apply symmetry;
    eapply transitivity; [| apply id_cod].
    eapply transitivity; [| apply adj_h_phi_inv_naturality].
    apply transitivity with (adj_h_phi_inv (fmap G f));
      [| apply map_preserve_eq ].
    apply transitivity with (f•adj_h_phi_inv id•fmap F id);
      [ eapply transitivity;
        [ apply symmetry; eapply transitivity;
          [ apply compose_subst_fst, fmap_id | apply id_dom ]
        | apply compose_assoc ] |].
    apply symmetry; eapply transitivity;
    [| apply adj_h_phi_inv_naturality ].
    apply map_preserve_eq.
    apply symmetry.
    eapply transitivity; [apply compose_subst_fst, id_dom | apply id_dom].
    apply symmetry.
    eapply transitivity; [ apply compose_subst_snd, fmap_id |].
    eapply transitivity; apply id_cod.
  Qed.
  
  (* Then, prove. *)
  Program Instance Adj_Hom_Counit (adj_h: Adjunction_Hom)
  : Adjunction_Counit (Adj_Hom_Counit_Natrans adj_h) := 
    { adj_cd := @adj_h_phi adj_h }.
  Next Obligation.
    (* adj_h_phi_inv (fmap G h•g• f) === h • adj_h_phi_inv g • fmap F f *)
    apply symmetry; eapply transitivity; [| apply id_cod];
    eapply transitivity; [| apply adj_h_phi_inv_naturality ].
    apply symmetry; eapply transitivity; [| apply adj_h_phi_iso].
    apply map_preserve_eq;
      eapply transitivity; [| apply id_cod].
    eapply transitivity; [ apply symmetry, compose_assoc |].
    apply compose_subst_snd.
    eapply transitivity; [ apply id_dom | apply fmap_id].
  Qed.
  Next Obligation.
    apply transitivity with
    (adj_h_phi (id•adj_h_phi_inv id •fmap F h));
    [ apply map_preserve_eq |].
    eapply transitivity; [| apply symmetry, id_cod ];
    apply symmetry, H.
    eapply transitivity; [ apply adj_h_phi_naturality |].
    eapply transitivity; [ apply compose_subst_snd, fmap_id |].
    eapply transitivity; [ apply id_cod |].
    eapply transitivity; [ apply compose_subst_snd, adj_h_phi_inv_iso | apply id_cod].
  Qed.
  
  
  (*
       以下，直接構成しようと試みるもうまく行かなかったため，
       とっても妥協しての定義である．
   *)
  (* 5. Unit -> Counit *)
  Program Instance Adj_U_Unit_Counit
          `(Hu: Adjunction_Unit adj_u_unit)
  : Adjunction_Counit _ := Adj_Hom_Counit (Adj_Unit_Hom Hu).

  (* 6. Counit -> Unit *)
  Program Instance Adj_C_Counit_Unit 
          `(Hc: Adjunction_Counit)
  : Adjunction_Unit _ := Adj_Hom_Unit (Adj_Counit_Hom Hc).

  
  Structure Adjunction :=
    { adj_phi {X: C}{Y: D}: Map (F X --> Y) (X --> G Y);
      adj_phi_inv {X: C}{Y: D}: Map (X --> G Y) (F X --> Y);
      adj_unit: Natrans (IdFunctor C) (ComposeFunctor F G);
      adj_counit: Natrans (ComposeFunctor G F) (IdFunctor D);

      adj_phi_iso:
        forall (X: C)(Y: D)(f: F X --> Y),
          adj_phi_inv (adj_phi f) === f;
      adj_phi_inv_iso:
        forall (X: C)(Y: D)(g: X --> G Y),
          adj_phi (adj_phi_inv g) === g;
      
      adj_phi_naturality:
        forall (X Y: C)(Z W: D)(f: X --> Y)(g: F Y --> Z)(h: Z --> W),
          adj_phi (h • g • fmap F f) === fmap G h • adj_phi g • f;
      
      adj_phi_inv_naturality:
        forall (adj: Adjunction_Hom)
               (X Y: C)(Z W: D)(f: X --> Y)(g: Y --> G Z)(h: Z --> W),
          adj_phi_inv (fmap G h•g• f) === h•adj_phi_inv g•fmap F f;

      adj_phi_inv_counit:
        forall (X: C)(Y: D)(f: X --> G Y),
          fmap G (adj_phi_inv f) • adj_unit X === f;
      adj_phi_inv_uniqueness:
        forall (X: C)(Y: D)(f: X --> G Y)(h: F X --> Y),
          fmap G h • adj_unit X === f -> adj_phi_inv f === h;

      adj_phi_counit:
        forall (X: C)(Y: D)(f: F X --> Y),
          adj_counit Y • fmap F (adj_phi f) === f;

      adj_phi_uniqueness:
        forall (X: C)(Y: D)(f: F X --> Y)(h: X --> G Y),
          adj_counit Y • fmap F h === f -> adj_phi f === h }.


  (* mendoi node atode *)
  (*
  Program Definition Adj_Hom_Adj (adj: Adjunction_Hom): Adjunction :=
    {| adj_phi := @adj_h_phi adj;
       adj_phi_inv := @adj_h_phi_inv adj;
       adj_unit := Adj_Hom_Unit_Natrans adj;
       adj_counit := Adj_Hom_Counit_Natrans adj
    |}.
  Next Obligation.
    *)
          
  
End AdjunctionDef.

Arguments Adjunction (C D F G): rename.
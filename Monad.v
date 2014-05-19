
Require Import
Ssreflect.ssreflect
COC.Setoid COC.Category COC.Functor COC.Natrans COC.Adjunction.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

Set Implicit Arguments.

Class Monad_Spec {C: Category}
      (T: Functor C C)
      (unit: Natrans (IdFunctor C) T)
      (join: Natrans (ComposeFunctor T T) T) :=
  { monad_join_unit_T:
      forall (X: C),
        join X • unit (T X) === id;
    monad_join_T_unit:
      forall (X: C),
        join X • fmap T (unit X) === id;
    monad_join_join:
      forall (X: C),
        join X • join (T X) === join X • fmap T (join X) }.

Structure Monad {C: Category}(T: Functor C C) :=
  make_Monad
    { monad_unit: Natrans (IdFunctor C) T;
      monad_join: Natrans (ComposeFunctor T T) T;
      monad_spec:> Monad_Spec monad_unit monad_join }.
Existing Instance monad_spec.
Coercion make_Monad: Monad_Spec >-> Monad.

Program Definition join_from_Adj
        `(adj: @Adjunction C D F G)
: Natrans (ComposeFunctor (ComposeFunctor F G) (ComposeFunctor F G))
          (ComposeFunctor F G) :=
  {| natrans X :=
       fmap G (adj_counit adj (F X)) |}.
Next Obligation.
  simpl; intros.
  eapply transitivity; [ apply fmap_compose | ].
  eapply transitivity; [| apply symmetry, fmap_compose ].
  apply map_preserve_eq.
  apply transitivity with (adj_counit adj (F Y) • (fmap (ComposeFunctor G F) (fmap F f))); [ apply reflexivity |].
  eapply transitivity.
  apply (@naturality _ _ _ _ (adj_counit adj)).
  apply reflexivity.
Qed.    


Program Definition Monad_from_Adj
        `(adj: @Adjunction C D F G)
: Monad (ComposeFunctor F G) :=
  {| monad_unit := adj_unit adj;
     monad_join := join_from_Adj adj |}.
Next Obligation.
  split; move=> X /=.
  - eapply transitivity; [ apply compose_subst_snd |].
    apply map_preserve_eq; apply adj_counit_as_phi_inv.
    eapply transitivity; [ apply compose_subst_fst |].
    apply adj_unit_as_phi.
    (* adj_phi (h • g • fmap F f) === fmap G h • adj_phi g • f; *)
    apply symmetry.
    eapply transitivity; [| apply id_dom ].
    eapply transitivity; [| apply symmetry,compose_assoc ].
    eapply transitivity; [| apply adj_phi_naturality ].
    apply symmetry; eapply transitivity; [apply map_preserve_eq |].
    eapply transitivity; [apply compose_subst_fst; apply id_cod |].
    eapply transitivity; [apply compose_subst_fst; apply fmap_id | apply id_dom].
    apply adj_phi_inv_iso.
    
  - eapply transitivity; [ apply fmap_compose |].
    eapply transitivity; [ apply map_preserve_eq | apply fmap_id ].
    eapply transitivity;
      [ apply compose_subst;
        [ apply map_preserve_eq; apply adj_unit_as_phi
        | apply adj_counit_as_phi_inv ]
       |].
    (* adj_phi_inv (fmap G h•g• f) === h•adj_phi_inv g•fmap F f; *)
    eapply transitivity; [ apply symmetry, id_cod |].
    eapply transitivity; [ apply symmetry, adj_phi_inv_naturality |].
    eapply transitivity; [ apply map_preserve_eq | apply adj_phi_iso ].
    eapply transitivity; [ apply symmetry, compose_assoc | ].
    eapply transitivity; [ apply compose_subst_snd | apply id_cod ].
    eapply transitivity; [ apply compose_subst_snd | apply id_cod ].
    apply fmap_id.

  - eapply transitivity; [ apply fmap_compose | ].
    eapply transitivity; [ apply map_preserve_eq | ].
    eapply transitivity;
      [ apply compose_subst;
        apply adj_counit_as_phi_inv
       |].
    eapply transitivity; [ apply symmetry, id_dom |].
    eapply transitivity; [ apply symmetry, compose_subst_fst, fmap_id |].
    eapply transitivity; [ apply compose_assoc |].
    eapply transitivity; [ apply symmetry, adj_phi_inv_naturality |].
    apply map_preserve_eq.
    eapply transitivity; [ apply compose_subst_fst |]; apply id_dom.
    apply symmetry.
    
    eapply transitivity; [ apply fmap_compose | ].
    eapply transitivity; [ apply map_preserve_eq | ].
    eapply transitivity;
      [ apply compose_subst;
        [| apply adj_counit_as_phi_inv]
       |].
    do 2 apply map_preserve_eq; apply adj_counit_as_phi_inv.
    eapply transitivity; [ apply symmetry, id_cod |].
    eapply transitivity; [ apply symmetry, adj_phi_inv_naturality |].
    apply map_preserve_eq.
    eapply transitivity; [ apply compose_subst_snd, fmap_id |].
    eapply transitivity; apply id_cod.
    reflexivity.
Qed.


Structure KT {C: Category}(T: C -> C) :=
  { ret {X: C}: X --> T X;
    bind {X Y: C}: (X --> T Y) -> (T X --> T Y);
    
    bind_subst:
      forall {X Y: C}(f f': X --> T Y),
        f === f' -> bind f === bind f';

    bind_ret_id:
      forall (X: C),
        bind (ret (X:=X)) === id;
    bind_f_ret_f:
      forall (X Y: C)(f: X --> T Y),
        bind f • ret === f;
    bind_assoc:
      forall (X Y Z: C)(f: X --> T Y)(g: Y --> T Z),
        bind g•bind f === bind (bind g•f) }.


Program Definition MonadKT `(monad: @Monad C T): KT T :=
  {| ret X := monad_unit monad X;
     bind X Y f := monad_join monad Y • fmap T f |}.
Next Obligation.
  by apply compose_subst_fst, map_preserve_eq, H.
Qed.
Next Obligation.
  by apply monad_join_T_unit.
Qed.
Next Obligation.
  eapply transitivity; [ apply compose_assoc |].
  eapply transitivity;
    [ apply symmetry, compose_subst_fst, (@naturality _ _ _ _ (monad_unit monad)) |].
  eapply transitivity; [ apply symmetry, compose_assoc |].
  eapply transitivity; [ apply compose_subst_snd, monad_join_unit_T |].
  apply id_cod.
Qed.
Next Obligation.
  eapply transitivity.
  eapply transitivity; [ apply compose_assoc |].
  eapply transitivity; [ apply compose_subst_fst |].
  eapply transitivity; [ apply symmetry, compose_assoc |].
  apply symmetry, compose_subst_snd, (@naturality _ _ _ _(monad_join monad)).
  eapply transitivity; [ apply symmetry, compose_assoc |].
  eapply transitivity; [ apply compose_subst_snd |].
  eapply transitivity; [ apply symmetry, compose_assoc |].
  eapply transitivity; [ apply compose_subst_snd |].
  apply monad_join_join.
  apply compose_assoc.
  apply compose_assoc.
  apply compose_subst_fst.
  eapply transitivity; [ apply compose_assoc |].
  eapply transitivity; [ apply compose_subst_fst |].
  simpl.
  apply fmap_compose.
  eapply transitivity; [ apply fmap_compose |].
  apply map_preserve_eq.
  apply symmetry, compose_assoc.
Qed.


Program Definition KT_fmap_Map
        (C: Category)(T: C -> C)(kt: KT T)(X Y: C)
: Map (X --> Y)
      (T X --> T Y) :=
  {| map_function f := bind kt (ret kt • f) |}.
Next Obligation.
  by apply bind_subst, compose_subst_fst, Heq.
Qed.

Program Definition KTFunctor {C: Category}{T: C -> C}(kt: KT T): Functor C C :=
  {| fobj := T;
     fmap X Y := KT_fmap_Map kt X Y |}.
Next Obligation.
  by eapply transitivity;
  [ apply bind_subst, id_dom | apply bind_ret_id ].
Qed.
Next Obligation.
  eapply transitivity; [ apply bind_assoc | ].
  apply bind_subst.
  eapply transitivity; [ | apply compose_assoc ].
  eapply transitivity; [ apply symmetry, compose_assoc | ].
  apply compose_subst_snd, bind_f_ret_f.
Qed.

Program Definition KTNatrans_unit
        {C: Category}{T: C -> C}(kt: KT T)
: Natrans (IdFunctor C) (KTFunctor kt) :=
  {| natrans X := ret kt |}.
Next Obligation.
  apply symmetry, bind_f_ret_f.
Qed.

Program Definition KTNatrans_join
        `(kt: @KT C T)
: Natrans (ComposeFunctor (KTFunctor kt) (KTFunctor kt)) (KTFunctor kt):=
  {| natrans X := bind kt id |}.
Next Obligation.
  eapply transitivity; [ apply bind_assoc | ].
  eapply transitivity; [ | apply symmetry, bind_assoc ].
  apply bind_subst.
  eapply transitivity; [ apply symmetry, compose_assoc | ].
  eapply transitivity; [ apply compose_subst_snd, bind_f_ret_f | ].
  eapply transitivity; [ apply id_cod | equiv_symm; auto; apply id_dom ].
Qed.

Program Definition KTMonad
        {C: Category}{T: C -> C}(kt: KT T)
: Monad (KTFunctor kt) :=
  {| monad_unit := KTNatrans_unit kt;
     monad_join := KTNatrans_join kt |}.
Next Obligation.
  split; move=> X /=.
  - apply bind_f_ret_f.
  - eapply transitivity; [ apply bind_assoc | ].
    eapply transitivity; [| apply bind_ret_id ].
    apply bind_subst.
    eapply transitivity; [| apply id_cod ].
    eapply transitivity; [ apply symmetry, compose_assoc |].
    apply compose_subst_snd; apply bind_f_ret_f.
  - eapply transitivity; [ apply bind_assoc |].
    eapply transitivity; [| apply symmetry, bind_assoc ].
    apply bind_subst.
    eapply transitivity; [ apply id_dom |].
    eapply transitivity; [| apply compose_assoc ].
    apply symmetry; eapply transitivity;
    [ apply compose_subst_snd; apply bind_f_ret_f 
    | apply id_cod ].
Qed.

Definition KTCompose {C: Category}{T: C -> C}(kt: KT T)
           (X Y Z: C)(f: X --> T Y)(g: Y --> T Z): X --> T Z :=
  bind kt g • f.
Hint Unfold KTCompose.

Program Definition KT_KleisliCategory
        {C: Category}{T: C -> C}(kt: KT T)
: Category :=
  {| obj := obj C;
     arr X Y := X --> T Y;
     
     compose X Y Z f g := bind kt g • f;
     id X := ret kt |}.
Next Obligation.
  eapply transitivity;
  [ apply symmetry, compose_subst_snd, bind_assoc
  | apply compose_assoc ].
Qed.      
Next Obligation.
  by apply compose_subst; [| apply bind_subst ].
Qed.
Next Obligation.
  apply bind_f_ret_f.
Qed.
Next Obligation.
  eapply transitivity;
    [ apply compose_subst_snd; apply bind_ret_id | apply id_cod ].
Qed.

Program Definition KleisliCategory
        {C: Category}{T: Functor C C}(m: Monad T)
: Category := KT_KleisliCategory (MonadKT m).


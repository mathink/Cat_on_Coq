Require Import 
Ssreflect.ssreflect
Ssreflect.eqtype
Ssreflect.ssrbool
COC.Setoid COC.Category COC.Functor.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

Section Algebra.

  Variable (C: Category)(F: Functor C C).

  Structure Algebra :=
    { alg_obj:> C;
      alg_arr: F alg_obj --> alg_obj }.

  (* これはF-代数準同型 *)
  Structure Algebra_Map_base (X Y: Algebra) :=
    make_Algebra_Map_base
    { alg_map:> X --> Y;
      alg_map_commute:
        alg_arr Y•fmap F alg_map === alg_map•alg_arr X }.

  Definition eq_Algebra_Map {X Y: Algebra}(f g: Algebra_Map_base X Y) :=
    alg_map f ===  alg_map g.
  Hint Unfold eq_Algebra_Map.

  Program Definition Algebra_Map (X Y: Algebra): Setoid :=
    {| equal := @eq_Algebra_Map X Y |}.
  Next Obligation.
    split; rewrite /eq_Algebra_Map //=.
    move=> x //=; equiv_refl.
    move=> x y //=; equiv_symm.
    move=> x y z //=; equiv_trns.
  Defined.
  Canonical Structure Algebra_Map.

  Program Definition compose_Algebra_Map
          {X Y Z: Algebra}(f: Algebra_Map X Y)(g: Algebra_Map Y Z)
  : Algebra_Map X Z :=
    {| alg_map := g•f |}.
  Next Obligation.
    eapply transitivity;
      [ apply compose_subst_fst; apply symmetry, fmap_compose |].
    apply symmetry.
    eapply transitivity;
      [ eapply transitivity; [apply compose_assoc |];
        apply compose_subst_fst; apply symmetry, alg_map_commute |].
    eapply transitivity; [apply symmetry, compose_assoc |].
    apply symmetry;
      eapply transitivity; [apply symmetry, compose_assoc |].
    apply compose_subst_snd; apply alg_map_commute.
  Defined.
  Canonical Structure compose_Algebra_Map.

  Program Definition id_Algebra_Map (X: Algebra)
  : Algebra_Map X X :=
    {| alg_map := id |}.
  Next Obligation.
    eapply transitivity;
    [ apply compose_subst_fst; apply fmap_id |].
    eapply transitivity;
      [| apply symmetry, id_cod].
    apply id_dom.
  Defined.
  Canonical Structure id_Algebra_Map.

  Program Canonical Structure ALG: Category :=
    {| compose := @compose_Algebra_Map ;
       id := id_Algebra_Map |}.
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply compose_assoc.
  Defined.            
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply compose_subst.
  Defined.            
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply id_dom.
  Defined.            
  Next Obligation.
    by rewrite /eq_Algebra_Map //=; apply id_cod.
  Defined.            


  (* catamorphism とは F-代数の圏における始代数からの射 *)
  Definition catamorphism
             (I: Initial ALG)(X: Algebra)
  : alg_obj (initial_obj I) --> alg_obj X :=
    initial_arr I X.

  Lemma cata_refl:
    forall (I: Initial ALG),
      catamorphism I (initial_obj I) === id.
  Proof.
    move=> I; rewrite /catamorphism.
    apply (initiality (Initial_Spec:=I)).
  Defined.

  Lemma cata_fusion:
    forall (f g: Algebra)(h: alg_obj f --> alg_obj g)(I: Initial ALG),
      alg_arr g•fmap F h === h•alg_arr f  ->
      h•catamorphism I f === catamorphism I g.
  Proof.
    move=> f g h I Heq.
    move: (@initial_fusion ALG I f g {| alg_map_commute := Heq |}).
      by rewrite /= /eq_Algebra_Map /compose_Algebra_Map /=.
  Defined.
  
End Algebra.

(* 使わないけど、代数がちゃんと定義できているかの確認のために Lambek's lemma の証明をしてみる *)
Lemma Lambek_lemma:
  forall (C: Category)(F: Functor C C)(I: Initial (ALG F)),
    Iso (C:=C) (alg_obj (initial_obj I)) (F (alg_obj (initial_obj I))).
Proof.
  move=> C F I; rewrite /Iso /iso.
  exists
    (catamorphism I {| alg_arr := fmap F (alg_arr (initial_obj I)) |}).
  exists
    (alg_arr (initial_obj I)).
  split.
  - eapply transitivity; [| apply cata_refl ].
    apply 
      (@cata_fusion C _ {| alg_arr := fmap F (alg_arr (initial_obj I)) |}).
    equiv_refl.
  - eapply transitivity.
    apply symmetry.
    apply 
      (alg_map_commute (initial_arr I {| alg_arr := (fmap F) (alg_arr (initial_obj I)) |})).
    simpl.
    eapply transitivity; [apply fmap_compose |].
    eapply transitivity; [apply map_preserve_eq |].
    apply (@cata_fusion _ _ {| alg_arr := fmap F (alg_arr (initial_obj I)) |}).
    equiv_refl.
    apply transitivity with (fmap F id);
      [apply map_preserve_eq | apply fmap_id].
    apply cata_refl.
Defined.    


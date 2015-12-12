Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Structure.
Require Import COC.Construction.Universal.

Program Definition UATo_map
        (D C: Category)(c: C)(S: Functor D C)(r: D)(u: C c (S r))(d: D)
  : Map (D r d) (C c (S d)) :=
  [ f' :-> fmap S f' \o u].
Next Obligation.
  intros.
  intros f g Heq; apply Category.comp_subst; [apply reflexivity |].
  apply Map.substitute, Heq.
Qed.
Arguments UATo_map: clear implicits.
Arguments UATo_map {D C c S r}(u d).

Lemma UATo_bijective:
  forall (D C: Category)(c: C)(S: Functor D C)(r: D)(u: C c (S r)),
    UniversalArrow.To.spec u <-> forall d: D, bijective (UATo_map u d).
Proof.
  intros; split.
  {
    intros [H] d; split.
    - intros f g; simpl in *.
      destruct (H d (fmap S f \o u)) as [f' [Hf Hfu]].
      intros Heq.
      apply symmetry in Heq.
      generalize (Hfu _ Heq).
      apply transitivity.
      apply symmetry, Hfu, reflexivity.
    - intros f.
      destruct (H d f) as [f' [Hf Hfu]].
      exists f'; simpl.
      apply Hf.
  }
  {
    intros H; split.
    intros d f.
    destruct (H d) as [Hi Hs].
    destruct (Hs f) as [f' Hf']; simpl in *.
    exists f'; split.
    - apply Hf'.
    - intros g' Heq.
      apply Hi; simpl.
      apply transitivity with f.
      + apply Hf'.
      + apply symmetry, Heq.
  }
Qed.

(*  *)
Program Definition UATo_natrans
        {D C: Category}{c: C}{S: Functor D C}{r: D}(u: C c (S r))
  : Natrans Hom(r,-) (Hom(c,-) \o{Cat} S) :=
  Natrans.build _ _ (fun d: D => UATo_map u d).
Next Obligation.
  simpl; intros.
  eapply transitivity; [| apply Category.comp_assoc].
  apply Category.comp_subst; [apply reflexivity |].
  apply Functor.fmap_comp.
Qed.

Module Representation.
  Class spec (D: Category)(K: Functor D Setoids)(r: D)(phi: Natrans Hom(r,-) K)(psi: Natrans K Hom(r,-)) :=
    proof {
        iso_rd: forall d: D, psi d \o phi d == Id_ Setoids (D r d);
        iso_dr: forall d: D, phi d \o psi d == Id_ Setoids (K d)
      }.

  Structure type (D: Category)(K: Functor D Setoids) :=
    make {
        object: D;
        phi: Natrans Hom(object,-) K;
        psi: Natrans K Hom(object,-);

        prf: spec phi psi
      }.

  Notation build phi psi := (@make _ _ _ phi psi (@proof _ _ _ _ _ _ _)).

  Module Ex.
    Notation isRepresentation := spec.
    Notation Representation := type.
    Coercion object: type >-> Category.obj.
    Coercion prf: type >-> spec.
    Existing Instance prf.
  End Ex.

End Representation.
  
(** 
 ** 米田の補題
有名なアレ
 **)
(**
 *** 評価函手
 **)
Definition EvalFunctor_fobj (C B: Category): (Fun C B) [x] C -> B :=
  (fun FX: (Fun C B) [x] C => let (F,X) := FX in F X).
Arguments EvalFunctor_fobj C B / _.

Definition EvalFunctor_fmap (C B: Category)
  : Fmap ((Fun C B) [x] C) B
         (@EvalFunctor_fobj C B) :=
  (fun FX GY => let (F,X) := FX in
                let (G,Y) := GY in
                fun (Sf: Prod (Natrans.setoid F G) (C X Y)) =>
                  let (S,f) := Sf in
                  fmap (Prod.fst GY) f \o S (Prod.snd FX)).
Arguments EvalFunctor_fmap C B / X Y _.


Instance Eval_isFunctor (C B: Category)
  : @isFunctor ((Fun C B) [x] C) B
               (@EvalFunctor_fobj C B) (@EvalFunctor_fmap C B).
Proof.
  split; simpl.
  {
    intros [F X] [G Y]; simpl.
    intros [S f] [T g]; simpl in *.
    intros [HeqST Heqfg]; simpl in *.
    apply Category.comp_subst; simpl.
    - apply HeqST.
    - apply Map.substitute, Heqfg.
  }
  {
    intros [F X] [G Y] [H Z]; simpl.
    intros [S f] [T g]; simpl.
    unfold EvalFunctor_fmap; simpl.
    eapply transitivity.
    {
      apply Category.comp_subst; [apply reflexivity |].
      apply Functor.fmap_comp.
    }
    eapply transitivity; [apply Category.comp_assoc |].
    eapply transitivity.
    {
      apply Category.comp_subst; [| apply reflexivity].
      eapply transitivity; [apply symmetry, Category.comp_assoc |].
      apply Category.comp_subst; [apply reflexivity |].
      apply symmetry, Natrans.naturality.
    }
    eapply transitivity.
    {
      apply Category.comp_subst; [| apply reflexivity].
      apply Category.comp_assoc.
    }
    eapply transitivity; [| apply symmetry, Category.comp_assoc].
    apply reflexivity.
  }  
  {
    intros [F X]; simpl.
    unfold EvalFunctor_fobj, EvalFunctor_fmap; simpl.
    eapply transitivity; [apply Category.comp_id_dom |].
    apply Functor.fmap_id.
  }
Qed.

Definition EvalFunctor (C B: Category): Functor ((Fun C B) [x] C) B :=
  Functor.make (@Eval_isFunctor C B).

Program Definition NFunctor (C: Category)
  : Functor (Fun C Setoids [x] C) Setoids :=
  Functor.build (fun FX => let (F,X) := FX in (Fun C Setoids) Hom(X,-) F)
                (fun FX GY Sf => let (F,X) := FX in
                                 let (G,Y) := GY in
                                 let (S,f) := Sf in
                                 [alpha :->
                                        Natrans.build Hom(Y,-) G (fun X => S X \o alpha X \o fmap Hom(-,X) f )]).
Next Obligation.
  intros C [F X] [G Y] [S f]; simpl in *.
  intros T Z W h g; simpl in *.
  eapply symmetry, transitivity.
  {
    generalize (Natrans.naturality (natrans:=S)(f:=h) (T Z (g \o f))).
    intro H; apply symmetry, H.
  }
  simpl.
  apply Map.substitute.
  generalize (Natrans.naturality (natrans:=T)(f:=h) (g \o f)); simpl.
  intro H; apply symmetry.
  eapply transitivity; [| apply H].
  apply Map.substitute; simpl.
  apply Category.comp_assoc.
Qed.
Next Obligation.
  intros C [F X] [G Y] [S f]; simpl in *.
  intros T U Heq Z g; simpl in *.
  apply Map.substitute.
  apply (Heq Z (g \o f)).
Qed.
Next Obligation.
  intros C [F X] [G Y] [S f] [S' f'] [HeqS Heqf]; simpl in *.
  intros T Z g; simpl in *.
  eapply transitivity; [apply (HeqS Z _) | apply Map.substitute].
  apply Map.substitute; simpl.
  apply Category.comp_subst;
    [apply Heqf | apply reflexivity].
Qed.
Next Obligation.
  simpl.
  intros C [F X] [G Y] [H Z]; simpl.
  intros [S f] [T g]; simpl.
  intros U W h; simpl.
  do 3 apply Map.substitute; simpl.
  apply symmetry, Category.comp_assoc.
Qed.
Next Obligation.
  simpl.
  intros C [F X] S Y f; simpl in *.
  apply Map.substitute; simpl.
  apply Category.comp_id_dom.
Qed.


Program Definition yoneda (C: Category)
  : Natrans (@NFunctor C) (@EvalFunctor C Setoids) :=
  Natrans.build _ _ (fun FX => let (F, X) := FX in [alpha :-> alpha X (Id X)]).
Next Obligation.
  intros C [F X]; simpl.
  intros S T Heq.
  apply (Heq X (Id X)).
Qed.
Next Obligation.
  intros C [F X] [G Y] [S f] T; simpl in *.
  generalize (Natrans.naturality (natrans:=S) (f:=f) (T X (Id X))).
  simpl; intro Heq.
  eapply transitivity; [| apply Heq].
  clear Heq.
  apply Map.substitute.
  generalize (Natrans.naturality (natrans:=T) (f:=f) (Id X)).
  simpl; intro Heq.
  eapply transitivity; [| apply Heq].
  clear Heq.
  apply Map.substitute; simpl.
  eapply transitivity;
    [apply Category.comp_id_cod | apply symmetry, Category.comp_id_dom].
Qed.

Program Definition inv_yoneda (C: Category):
  Natrans (@EvalFunctor C Setoids) (@NFunctor C) :=
  Natrans.build (@EvalFunctor C Setoids) (@NFunctor C)
    (fun FX => let (F,X) := FX in
               [ x :-> Natrans.build Hom(X,-) F (fun Y => [f :-> fmap F f x])]).
Next Obligation.
  intros C [F X]; simpl.
  intros x Y f g Heq.
  assert (HeqF: fmap F f == fmap F g).
  {
    apply Map.substitute, Heq.
  }
  apply (HeqF x).
Qed.
Next Obligation.
  intros C [F X]; simpl.
  intros x Y Z g; simpl.
  intro f.
  apply (Functor.fmap_comp (fobj:=F)(f:=f)(g:=g) x).
Qed.
Next Obligation.
  intros C [F X]; simpl.
  intros x y Heq Y f; simpl.
  apply Map.substitute, Heq.
Qed.
Next Obligation.
  intros C [F X] [G Y] [S f]; simpl in *.
  intros x Z g.
  assert (Heq: fmap G g \o fmap G f \o S X == S Z \o fmap F (g \o f)).
  {
    eapply transitivity; [apply symmetry,Category.comp_assoc |].
    eapply transitivity; [apply symmetry,Category.comp_subst |].
    - apply reflexivity.
    - apply Functor.fmap_comp.
    - apply symmetry,Natrans.naturality.
  }
  apply (Heq x).
Qed.

(** 
 ** 射の同型とか
 **)
Instance yoneda_lemma:
  forall (C: Category), isNaturalIso (@yoneda C) (@inv_yoneda C).
Proof.
  intros C [F X]; simpl.
  apply Iso_def; simpl.
  - intros S Y f.
    apply symmetry.
    generalize (Natrans.naturality (natrans:=S)(f:=f)); simpl.
    intro Heq.
    eapply transitivity; [| apply (Heq (Id X))]; simpl.
    apply Map.substitute, symmetry; simpl.
    apply Category.comp_id_dom.
  - apply (Functor.fmap_id (fobj:=F)).
Qed.

(* Next: Grothendieck Functor *)
Program Definition HomNat {C: Category}(X Y: C)(f: C X Y)
  : Natrans Hom(Y,-) Hom(X,-) :=
  Natrans.build _ _ (fun Z => [ g :-> g \o f ]).
Next Obligation.
  intros C X Y f Z g g' Heq; simpl in *.
  apply Category.comp_subst; [apply reflexivity | apply Heq].
Qed.
Next Obligation.
  intros C X Y f Z W h g; simpl in *.
  apply Category.comp_assoc.
Qed.

Instance Grothendieck_isFunctor (C: Category)
  : @isFunctor (Category.op C) (Fun C Setoids)
               (fun (X: C) => Hom(X,-))
               (fun Y X (f: C X Y) => HomNat f).
Proof.
  split.
  {
    intros Y X f f' Heq Z g; simpl in *.
    apply Category.comp_subst; [apply Heq | apply reflexivity].
  }
  {
    intros Z Y X g f W h; simpl in *.
    apply symmetry, Category.comp_assoc.
  }
  {
    intros Y X f; simpl in *.
    apply Category.comp_id_dom.
  }
Qed.

Definition GrothFunctor (C: Category)
  : Functor (Category.op C) (Fun C Setoids) :=
  Functor.make (@Grothendieck_isFunctor C).


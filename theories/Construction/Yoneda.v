Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Structure.


(** 
 ** 米田の補題
有名なアレ
 **)
(**
 *** 評価函手
 **)
Definition EvalFunctor_fobj (C B: Category)
  : (Fun C B) [x] C -> B :=
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
    unfold EvalFunctor_fmap.
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

Definition EvalFunctor (C B: Category)
  : Functor ((Fun C B) [x] C) B :=
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
Lemma yoneda_lemma:
  forall (C: Category), NaturalIso (@yoneda C).
Proof.
  intros C [F X]; simpl.
  exists (@inv_yoneda C (F,X)); simpl.
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


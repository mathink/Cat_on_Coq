Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import
        COC.Setoid
        COC.Category
        COC.Construction
        
        COC.Constitution.Universal.

Program Definition UATo_map
        (D C: Category)(c: C)(S: Functor D C)(r: D)(u: C c (S r))(d: D)
  : Map (D r d) (C c (S d)) :=
  [ f' :-> fmap S f' \o u].
Next Obligation.
  now intros f g H; rewrite H.
Qed.
Arguments UATo_map: clear implicits.
Arguments UATo_map {D C c S r}(u d).


(*  *)
Program Definition UATo_natrans
        {D C: Category}{c: C}{S: Functor D C}{r: D}(u: C c (S r))
  : Natrans Hom(r,-) (Hom(c,-) \o{Cat} S) :=
  Natrans.build _ _ (fun d: D => UATo_map u d).
Next Obligation.
  now rewrite fnC, catCa.
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
    now rewrite Heqfg, (HeqST X).
  }
  {
    intros [F X] [G Y] [H Z]; simpl.
    intros [S f] [T g]; simpl.
    rewrite catCa, fnC, catCa.
    now rewrite <- (catCa (h:=fmap H f)), <- Natrans.naturality, catCa.
  }  
  {
    intros [F X]; simpl.
    now rewrite catC1f, fn1.
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
  revert C FX GY Sf alpha X Y f x.
  intros C [F X] [G Y] [S f]; simpl in *.
  intros T Z W h g; simpl in *.
  generalize (Natrans.naturality (natrans:=S)(f:=h)(T Z (g \o f))); simpl.
  intros H; rewrite <- H; clear H.
  apply Map.substitute.
  rewrite catCa.
  generalize (Natrans.naturality (natrans:=T)(f:=h) (g \o f)); simpl.
  now intros H; rewrite H.
Qed.
Next Obligation.
  revert FX GY Sf.
  intros [F X] [G Y] [S f]; simpl in *.
  intros T U Heq Z g; simpl in *.
  now rewrite (Heq Z (g \o f)).
Qed.
Next Obligation.
  revert X Y.
  intros [F X] [G Y] [S f] [S' f'] [HeqS Heqf]; simpl in *.
  intros T Z g; simpl in *.
  now rewrite (HeqS Z _), Heqf.
Qed.
Next Obligation.
  revert X Y Z f g x.
  intros [F X] [G Y] [H Z]; simpl.
  intros [S f] [T g]; simpl.
  intros U W h; simpl.
  now rewrite catCa.
Qed.
Next Obligation.
  revert X x.
  intros [F X] S Y f; simpl in *.
  now rewrite catC1f.
Qed.


Program Definition yoneda (C: Category)
  : Natrans (@NFunctor C) (@EvalFunctor C Setoids) :=
  Natrans.build _ _ (fun FX => let (F, X) := FX in [alpha :-> alpha X (Id X)]).
Next Obligation.
  destruct FX as [F X]; simpl.
  intros S T Heq.
  now rewrite (Heq _ _).
Qed.
Next Obligation.
  revert X Y f x.
  intros [F X] [G Y] [S f] T; simpl in *.
  rewrite catCf1.
  generalize (Natrans.naturality (natrans:=S) (f:=f) (T X (Id X))).
  simpl; intro Heq; rewrite <- Heq; clear Heq.
  generalize (Natrans.naturality (natrans:=T) (f:=f) (Id X)).
  simpl; intro Heq; rewrite <- Heq; clear Heq.
  now rewrite catC1f.
Qed.

Program Definition inv_yoneda (C: Category):
  Natrans (@EvalFunctor C Setoids) (@NFunctor C) :=
  Natrans.build (@EvalFunctor C Setoids) (@NFunctor C)
    (fun FX => let (F,X) := FX in
               [ x :-> Natrans.build Hom(X,-) F (fun Y => [f :-> fmap F f x])]).
Next Obligation.
  revert FX x Y.
  intros [F X] x Y f g Heq.
  assert (HeqF: fmap F f == fmap F g).
  {
    now rewrite Heq.
  }
  now rewrite (HeqF x).
Qed.
Next Obligation.
  revert C FX x X Y f x0.
  intros C [F X] x Y Z g f; simpl.
  now rewrite (Functor.fmap_comp (fobj:=F) f g x).
Qed.
Next Obligation.
  destruct FX as [F X]; simpl.
  intros x y Heq Y f; simpl.
  now apply Map.substitute.
Qed.
Next Obligation.
  revert X Y f x.
  intros [F X] [G Y] [S f] x Z g; simpl.
  assert (Heq: fmap G g \o fmap G f \o S X == S Z \o fmap F (g \o f)).
  {
    now rewrite <- catCa, <- fnC, <- Natrans.naturality.
  }
  now rewrite (Heq x).
Qed.

(** 
 ** 射の同型とか
 **)
Instance yoneda_lemma:
  forall (C: Category), isNaturalIso (@yoneda C) (@inv_yoneda C).
Proof.
  intros C [F X]; simpl.
  apply Iso_def; simpl.
  - intros S Y f; simpl.
    generalize (Natrans.naturality (natrans:=S)(f:=f)); simpl.
    intro Heq.
    now rewrite <- (Heq (Id X)), catC1f.
  - apply (Functor.fmap_id (fobj:=F)).
Qed.

(* Next: Grothendieck Functor *)
Program Definition HomNat {C: Category}(X Y: C)(f: C X Y)
  : Natrans Hom(Y,-) Hom(X,-) :=
  Natrans.build _ _ (fun Z => [ g :-> g \o f ]).
Next Obligation.
  intros g g' Heq; simpl in *.
  now rewrite Heq.
Qed.
Next Obligation.
  now rewrite catCa.
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


(** * Yoneda Lemma **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

(** simple ver. **)
(** Nat(Hom(X,-), F) -> F X **)
Program Definition yoneda_map (C: Category)(X: C)(F: C --> Setoids)
  : Map ((Setoids^C) Hom(X,-) F) (F X) :=
  [ S in Natrans Hom(X,-) F :-> S X (Id X) ].
Next Obligation.
  intros S T Heq; simpl in *.
  now rewrite (Heq X (Id X)).
Qed.

(** F X -> Nat(Hom(X,-), F) **)
Program Definition inv_yoneda_map_natrans_map
        (C: Category)(X: C)(F: C --> Setoids)
        (x: F X)(Y: C)
  : Map (C X Y) (F Y) :=
  [ f in C X Y :-> fmap F f x ].
Next Obligation.
  intros f f' Heq.
  now apply (fmap_proper (IsFunctor:=F) Heq x).
Qed.

Program Definition inv_yoneda_map_natrans
        (C: Category)(X: C)(F: C --> Setoids)(x: F X)
  : Hom(X,-) ==> F :=
  [ Y in C :=> inv_yoneda_map_natrans_map x Y].
Next Obligation.
  now rewrite (fmap_comp (F:=F) _ _ x).
Qed.

Program Definition inv_yoneda_map (C: Category)(X: C)(F: C --> Setoids)
  : Map (F X) ((Setoids^C) Hom(X,-) F) :=
  [ x in F X :-> inv_yoneda_map_natrans x].
Next Obligation.
  now intros x y Heq Y f; simpl; rewrite Heq.
Qed.

Definition injective (X Y: Setoid)(f: Map X Y) :=
  forall x y, f x == f y -> x == y.
Definition surjective (X Y: Setoid)(f: Map X Y) :=
  forall (y: Y), exists x: X, f x == y.
Definition bijective (X Y: Setoid)(f: Map X Y) :=
  injective f /\ surjective f.
Definition equiv (X Y: Setoid) :=
  exists f: Map X Y, bijective f.

Theorem yoneda_lemma:
  forall (C: Category)(X: C)(F: C --> Setoids),
    equiv ((Setoids^C) Hom(X,-) F) (F X).
Proof.
  intros; exists (yoneda_map X F).
  unfold bijective, injective, surjective; split; simpl.
  - intros S T Heq Y f.
    generalize (natrans_naturality (IsNatrans:=S) f (Id X)); simpl.
    rewrite cat_comp_id_dom; intros H; rewrite H; clear H.
    generalize (natrans_naturality (IsNatrans:=T) f (Id X)); simpl.
    rewrite cat_comp_id_dom; intros H; rewrite H; clear H.
    now rewrite Heq.
  - intros x.
    exists (inv_yoneda_map X F x); simpl.
    now rewrite (fmap_id (F:=F) X x).
Qed.


(** complex ver. **)
Require Import COC.Cons.Product.

Program Definition Eval_yoneda (C: Category): (product_category (Setoids^C) C) --> Setoids :=
  [Functor by (fun FX GY Sf => fmap GY.1 Sf.2 \o Sf.1 FX.2)
   with (fun FX => FX.1 FX.2)].
Next Obligation.
  - destruct X as [F X], Y as [G Y].
    intros [S f] [T g] [HeqST Heqfg] x; simpl in *.
    rewrite HeqST.
    assert (Heq: fmap G f == fmap G g).
    {
      now rewrite Heqfg.
    }
    now rewrite (Heq (T X x)).
  - rewrite (fmap_comp (F:=Z.1) _ _ (g.1 X.2 (f.1 X.2 x))); simpl.
    now rewrite (natrans_naturality (IsNatrans:=g.1) f.2 (f.1 X.2 x)).
  - now rewrite (fmap_id (F:=X.1) X.2 x).
Qed.


Program Definition N_yoneda_fmap_natrans  (C: Category)
        (FX GY: product_category (Setoids^C) C)
        (Sf: product_category (Setoids^C) C FX GY)
        (alpha: Hom(FX.2, -) ==> FX.1)
  : Hom(GY.2, -) ==> GY.1 :=
  [X :=> Sf.1 X \o alpha X \o fmap Hom(-,X) Sf.2].
Next Obligation.
  rename X into Z, Y into W, f into h, x into g.
  destruct FX as [F X], GY as [G Y], Sf as [S f]; simpl in *.
  rewrite <- (natrans_naturality (IsNatrans:=S) h (alpha Z (g \o f))); simpl.
  rewrite cat_comp_assoc.
  now rewrite <- (natrans_naturality (IsNatrans:=alpha) h (g \o f)); simpl.
Qed.

Program Definition N_yoneda_fmap (C: Category)
        (FX GY: product_category (Setoids^C) C)
        (Sf: product_category (Setoids^C) C FX GY)
  : Map (Natrans_setoid Hom(FX.2, -) FX.1)
        (Natrans_setoid Hom(GY.2, -) GY.1) := 
  [ alpha :-> N_yoneda_fmap_natrans Sf alpha ].
Next Obligation.
  destruct FX as [F X], GY as [G Y], Sf as [S f]; simpl in *.
  intros a b Heq Z g; simpl.
  now rewrite (Heq _ (g \o f)).
Qed.

Program Definition N_yoneda  (C: Category): (product_category (Setoids^C) C) --> Setoids :=
  [Functor by @N_yoneda_fmap C
   with (fun FX => (Fun C Setoids) Hom(FX.2,-) FX.1)].
Next Obligation.
  - destruct X as [F X], Y as [G Y]; simpl.
    intros [S f] [T g] [HeqST Heqfg] a Z h; simpl in *.
    now rewrite Heqfg, HeqST.
  - now rewrite cat_comp_assoc.
  - now rewrite cat_comp_id_dom.
Qed.

Program Definition yoneda_natrans (C: Category)
  : N_yoneda C ==> Eval_yoneda C :=
  [FX :=> yoneda_map FX.2 FX.1].
Next Obligation.
  destruct X as [F X], Y as [G Y], f as [S f]; simpl in *.
  rewrite cat_comp_id_cod.
  rewrite <- (natrans_naturality (IsNatrans:=S) f (x X (Id X))); simpl.
  rewrite <- (natrans_naturality (IsNatrans:=x) f (Id X)); simpl.
  now rewrite cat_comp_id_dom.
Qed.

Program Definition inv_yoneda_natrans (C: Category)
  : Eval_yoneda C ==> N_yoneda C :=
  [FX :=> inv_yoneda_map FX.2 FX.1].
Next Obligation.
  destruct X as [F X], Y as [G Y], f as [S f]; simpl in *.
  rename X0 into Z, x0 into g.
  rewrite (fmap_comp (F:=F) f g x); simpl.
  rewrite (natrans_naturality (IsNatrans:=S) g (fmap F f x)); simpl.
  now rewrite (natrans_naturality (IsNatrans:=S) f x).
Qed.

Program Instance yoneda_lemma' (C: Category)
  : NaturalIsomorphic (yoneda_natrans C) (inv_yoneda_natrans C).
Next Obligation.
  - destruct X as [F X]; rename X0 into Y, x0 into f; simpl in *.
    rewrite <- (natrans_naturality (IsNatrans:=x) f (Id X)); simpl.
    now rewrite cat_comp_id_dom.
  - now rewrite (fmap_id (F:=X.1) X.2 x).
Qed.

Fail Check yoneda_natrans Setoids.
(* The command has indeed failed with message: *)
(* The term "Setoids" has type "Category@{Top.3438 Top.3439}" *)
(* while it is expected to have type "Category@{Top.3437 Top.3437}". *)




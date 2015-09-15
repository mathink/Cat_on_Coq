Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Structure.

Module Monoidal.
  Notation bifmap F p := (fmap F (X:=(_,_))(Y:=(_,_)) p) (only parsing).
  Notation "x '[Bi' F ] y" := (fmap F (X:=(_,_))(Y:=(_,_)) (x,y)) (only parsing, at level 60, no associativity).

  Class spec (B: Category)(mult: Bifunctor B B B)(unit: B)
        (assoc: forall (a b c: B), B (mult (a, mult (b, c))) (mult (mult (a, b), c)))
        (assoc_inv: forall (a b c: B), B (mult (mult (a, b), c)) (mult (a, mult (b, c))))
        (lambda: forall (a: B), B (mult (unit, a)) a)
        (lambda_inv: forall (a: B), B a (mult (unit, a)))
        (rho: forall (a: B), B (mult (a, unit)) a)
        (rho_inv: forall (a: B), B a (mult (a, unit))) :=
    {
      assoc_naturality:
        forall (a a' b b' c c': B)(f: B a a')(g: B b b')(h: B c c'),
          (f [Bi mult] g)[Bi mult] h \o assoc a b c ==
          assoc a' b' c' \o f [Bi mult] (g [Bi mult] h);

      assoc_iso:
        forall (a b c: B), assoc_inv a b c \o assoc a b c == Id _;

      assoc_iso_inv:
        forall (a b c: B), assoc a b c \o assoc_inv a b c == Id _;

      associativity:
        forall (a b c d: B),
          assoc (mult (a, b)) c d \o assoc a b (mult (c, d)) ==
          (assoc a b c [Bi mult] Id d) \o assoc a (mult (b, c)) d \o (Id a [Bi mult] assoc b c d);

      lambda_naturality:
        forall (a a': B)(f: B a a'),
          f \o lambda a == lambda a' \o (Id unit [Bi mult] f);

      lambda_iso:
        forall (a: B), lambda_inv a \o lambda a == Id _;

      lambda_iso_inv:
        forall (a: B), lambda a \o lambda_inv a == Id _;

      rho_naturality:
        forall (a a': B)(f: B a a'),
          f \o rho a == rho a' \o (f [Bi mult] Id unit);

      rho_iso:
        forall (a: B), rho_inv a \o rho a == Id _;

      rho_iso_inv:
        forall (a: B), rho a \o rho_inv a == Id _;

      unit_law:
        forall (a c: B),
          (rho a [Bi mult] Id c) \o assoc a unit c == (Id a [Bi mult] lambda c);

      lambda_rho:
        lambda unit == rho unit
    }.

  Structure type :=
    make {
        cat: Category;
        mult: Bifunctor cat cat cat;
        unit: cat;

        assoc: forall (a b c: cat), cat (mult (a, mult (b, c))) (mult (mult (a, b), c));
        assoc_inv: forall (a b c: cat), cat (mult (mult (a, b), c)) (mult (a, mult (b, c)));
        lambda: forall (a: cat), cat (mult (unit, a)) a;
        lambda_inv: forall (a: cat), cat a (mult (unit, a));
        rho: forall (a: cat), cat (mult (a, unit)) a;
        rho_inv: forall (a: cat), cat a (mult (a, unit));

        prf: spec (@assoc) (@assoc_inv) (@lambda) (@lambda_inv) (@rho) (@rho_inv)
      }.

  Class frame (B: type) :=
    {
      _mult: Bifunctor (cat B) (cat B) (cat B)
    }.

  Instance frame_instance (B: type): frame B :=
    {
      _mult := mult B
    }.

  Module Ex.
    Notation isMonoidal := spec.
    Notation Monoidal := type.
    Coercion cat: Monoidal >-> Category.
    Coercion mult: Monoidal >-> Functor.
    Coercion prf: type >-> spec.
    Existing Instance prf.

    Notation Munit B := (unit B).
    Notation "x • y" := (mult _ (x, y)) (at level 60, no associativity).
    Notation "x [] y" := (x [Bi _mult] y) (at level 60, no associativity).
    Notation "'α'" := assoc.
    Notation "'α^-1'" := assoc_inv.
    Notation "'λ'" := lambda.
    Notation "'λ^-1'" := lambda_inv.
    Notation "'ρ'" := rho.
    Notation "'ρ^-1'" := rho_inv.
  End Ex.
  Import Ex.
  
  Lemma assoc_inv_naturality {B: Monoidal}:
    forall (a a' b b' c c': B)(f: B a a')(g: B b b')(h: B c c'),
      f [] (g [] h) \o assoc_inv a b c ==
       assoc_inv a' b' c' \o (f [] g) [] h.
  Proof.
    intros.
    eapply transitivity; [apply symmetry, Category.comp_id_cod |].
    eapply transitivity; [apply Category.comp_subst_cod, symmetry, assoc_iso |].
    eapply transitivity; [apply Category.comp_assoc |].
    eapply transitivity; [apply Category.comp_subst_dom, symmetry, Category.comp_assoc |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_subst_cod, symmetry, assoc_naturality |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_assoc |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_subst_dom, assoc_iso_inv |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_id_dom |].
    apply reflexivity.
  Qed.    

  Lemma lambda_inv_naturality {B: Monoidal}:
    forall (a a': B)(f: B a a'),
      (Id (unit B) [] f) \o lambda_inv a == lambda_inv a' \o f.
  Proof.
    intros.
    eapply transitivity; [apply symmetry, Category.comp_id_cod |].
    eapply transitivity; [apply Category.comp_subst_cod, symmetry, lambda_iso |].
    eapply transitivity; [apply Category.comp_assoc |].
    eapply transitivity; [apply Category.comp_subst_dom, symmetry, Category.comp_assoc |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_subst_cod, symmetry, lambda_naturality |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_assoc |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_subst_dom, lambda_iso_inv |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_id_dom |].
    apply reflexivity.
  Qed.

  Lemma rho_inv_naturality {B: Monoidal}:
    forall (a a': B)(f: B a a'),
      (f [] Id (unit B)) \o rho_inv a == rho_inv a' \o f.
  Proof.
    intros.
    eapply transitivity; [apply symmetry, Category.comp_id_cod |].
    eapply transitivity; [apply Category.comp_subst_cod, symmetry, rho_iso |].
    eapply transitivity; [apply Category.comp_assoc |].
    eapply transitivity; [apply Category.comp_subst_dom, symmetry, Category.comp_assoc |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_subst_cod, symmetry, rho_naturality |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_assoc |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_subst_dom, rho_iso_inv |].
    eapply transitivity; [apply Category.comp_subst_dom, Category.comp_id_dom |].
    apply reflexivity.
  Qed.

End Monoidal.
Export Monoidal.Ex.

Module Monoid.
  Class spec (B: Monoidal)(c: B)(mu: B (c•c) c)(eta: B (Munit B) c) :=
    proof {
        associativity:
          mu \o (mu [] Id c) \o Monoidal.assoc c c c == mu \o (Id c [] mu);
        unit_l:
          mu \o (eta [] Id c) == Monoidal.lambda c;
        unit_r:
          mu \o (Id c [] eta) == Monoidal.rho c
      }.

  Structure type (B: Monoidal) :=
    {
      obj: B;
      mu: B (obj•obj) obj;
      eta: B (Munit B) obj;

      prf: spec mu eta
    }.

  Module Ex.
    Notation isMonoid := spec.
    Notation Monoid := type.
    Coercion obj: type >-> Category.obj.
    Coercion prf: type >-> spec.
    Existing Instance prf.
  End Ex.
  Import Ex.

  Module morphism.
    Class spec (B: Monoidal)(c c': Monoid B)(f: B c c') :=
      proof {
          mu_law:
            f \o mu c == mu c' \o (f [] f);

          eta_law:
            f \o eta c == eta c'
        }.

    Class type (B: Monoidal)(c c': Monoid B) :=
      make {
          arr: B c c';
          
          prf: spec arr
        }.

    Notation build f := (@make _ _ _ f (@proof _ _ _ f _ _)).

    Module Ex.
      Notation ismorph := spec.
      Notation morph := type.
      Coercion arr: type >-> Setoid.carrier.
      Coercion prf: type >-> spec.
      Existing Instance prf.
    End Ex.
    Import Ex.

    Program Definition compose (B: Monoidal)(c d e: Monoid B)(f: morph c d)(g: morph d e): morph c e :=
      build (g \o f).
    Next Obligation.
      intros; simpl.
      eapply transitivity; [apply Category.comp_assoc |].
      eapply transitivity; [apply Category.comp_subst_dom, mu_law |].
      eapply transitivity; [apply symmetry, Category.comp_assoc |].
      eapply transitivity; [apply Category.comp_subst_cod, mu_law |].
      eapply transitivity; [apply Category.comp_assoc |]; simpl.
      eapply transitivity; [apply Category.comp_subst_dom, symmetry, Functor.fmap_comp |]; simpl.
      unfold Prod.compose; simpl.
      apply reflexivity.
    Qed.
    Next Obligation.
      intros; simpl.
      eapply transitivity; [apply Category.comp_assoc |].
      eapply transitivity; [apply Category.comp_subst_dom, eta_law |].
      apply eta_law.
    Qed.

    Program Definition id (B: Monoidal)(c: Monoid B): morph c c :=
      build (Id c).
    Next Obligation.
      simpl; intros.
      eapply transitivity; [apply Category.comp_id_cod |].
      generalize (Functor.fmap_id (spec:=Monoidal.mult B) (X:=(obj c,obj c))); simpl.
      unfold Prod.id; simpl; intros H.
      eapply transitivity; [| apply Category.comp_subst_dom, symmetry, H].
      apply symmetry, Category.comp_id_dom.
    Qed.
    Next Obligation.
      intros; apply Category.comp_id_cod.
    Qed.

    Definition equal (B: Monoidal)(c d: Monoid B)(f g: morph c d) := f == g.
    Arguments equal B c d f g /.

    Program Definition setoid (B: Monoidal)(c d: Monoid B) :=
      Setoid.build (@equal B c d).
    Next Obligation.
      intros B c d f; simpl; apply reflexivity.
    Qed.
    Next Obligation.
      intros B c d f g; simpl; apply symmetry.
    Qed.
    Next Obligation.
      intros B c d f g h; simpl; apply transitivity.
    Qed.
  End morphism.
  Import morphism.
  Import morphism.Ex.
  
  Program Definition category (B: Monoidal): Category :=
    Category.build (@setoid B)
                   (@compose B)
                   (@id B).
  Next Obligation.
    simpl; intros; apply Category.comp_subst; assumption.
  Qed.
  Next Obligation.
    simpl; intros; apply Category.comp_assoc.
  Qed.
  Next Obligation.
    simpl; intros; apply Category.comp_id_dom.
  Qed.
  Next Obligation.
    simpl; intros; apply Category.comp_id_cod.
  Qed.


  Instance forgetful_isF (B: Monoidal):
    @isFunctor (category B) B
               (fun (c: category B) => obj c)
               (fun (c d: category B)(f: morph c d) => arr (type:=f)).
  Proof.
    split; simpl.
    - intros X Y f g; auto.
    - intros; apply reflexivity.
    - intros; apply reflexivity.
  Qed.

  Definition forgetful (B: Monoidal) := Functor.make (forgetful_isF B).
  

  Module mEx.
    Module Monoid := morphism.Ex.
  End mEx.
End Monoid.
Export Monoid.Ex.
Export Monoid.mEx.


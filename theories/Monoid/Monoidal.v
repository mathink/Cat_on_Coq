Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Structure.

Notation bifmap F p := (fmap F (X:=(_,_))(Y:=(_,_)) p) (only parsing).
Notation "x '[Bi' F ] y" := (fmap F (X:=(_,_))(Y:=(_,_)) (x,y)) (at level 60, no associativity, format "x  [Bi  F  ]  y").

Module Monoidal.
  Class spec (B: Category)(mult: Bifunctor B B B)(unit: B)
        (assoc: forall (a b c: B), B (mult (a, mult (b, c))) (mult (mult (a, b), c)))
        (assoc_inv: forall (a b c: B), B (mult (mult (a, b), c)) (mult (a, mult (b, c))))
        (lambda: forall (a: B), B (mult (unit, a)) a)
        (lambda_inv: forall (a: B), B a (mult (unit, a)))
        (rho: forall (a: B), B (mult (a, unit)) a)
        (rho_inv: forall (a: B), B a (mult (a, unit))) :=
    {
      assoc_naturality:
        (* 
          a(bc)  -- assoc ->  (ab)c
            |                   |
          f(gh)               (fg)h
            V                   V
        a'(b'c') -- assoc -> (a'b')c'
         *)
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
          (rho a [Bi mult] Id c) \o assoc a unit c == (Id a [Bi mult] lambda c)
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
    etrans; [apply symmetry, catCf1 |].
    etrans; [apply catCsc, symmetry, assoc_iso |].
    etrans; [apply catCa |].
    etrans; [apply catCsd, symmetry, catCa |].
    etrans; [apply catCsd, catCsc, symmetry, assoc_naturality |].
    etrans; [apply catCsd, catCa |].
    etrans; [apply catCsd, catCsd, assoc_iso_inv |].
    etrans; [apply catCsd, catC1f |].
    apply reflexivity.
  Qed.    

  Lemma lambda_inv_naturality {B: Monoidal}:
    forall (a a': B)(f: B a a'),
      (Id (unit B) [] f) \o lambda_inv a == lambda_inv a' \o f.
  Proof.
    intros.
    etrans; [apply symmetry, catCf1 |].
    etrans; [apply catCsc, symmetry, lambda_iso |].
    etrans; [apply catCa |].
    etrans; [apply catCsd, symmetry, catCa |].
    etrans; [apply catCsd, catCsc, symmetry, lambda_naturality |].
    etrans; [apply catCsd, catCa |].
    etrans; [apply catCsd, catCsd, lambda_iso_inv |].
    etrans; [apply catCsd, catC1f |].
    apply reflexivity.
  Qed.

  Lemma rho_inv_naturality {B: Monoidal}:
    forall (a a': B)(f: B a a'),
      (f [] Id (unit B)) \o rho_inv a == rho_inv a' \o f.
  Proof.
    intros.
    etrans; [apply symmetry, catCf1 |].
    etrans; [apply catCsc, symmetry, rho_iso |].
    etrans; [apply catCa |].
    etrans; [apply catCsd, symmetry, catCa |].
    etrans; [apply catCsd, catCsc, symmetry, rho_naturality |].
    etrans; [apply catCsd, catCa |].
    etrans; [apply catCsd, catCsd, rho_iso_inv |].
    etrans; [apply catCsd, catC1f |].
    apply reflexivity.
  Qed.

  Lemma left_id_functor_injective (B: Monoidal):
    forall (a b: B)(f g: B a b),
      Id (unit B) [] f == Id (unit B) [] g -> f == g.
  Proof.
    simpl; intros a b f g Heq.
    assert (H: f \o lambda a == g \o lambda a).
    {
      etrans; [apply lambda_naturality |].
      etrans; [| apply symmetry, lambda_naturality].
      apply catCsd, Heq.
    }
    etrans; [| apply catC1f].
    etrans; [apply symmetry, catC1f |].
    etrans; [apply catCsd, symmetry, lambda_iso_inv |].
    etrans; [| apply symmetry, catCsd, symmetry, lambda_iso_inv].
    etrans; [| apply catCa].
    etrans; [apply symmetry, catCa |].
    apply catCsc, H.
  Qed.    
      
  Lemma kelly_lambda {B: Monoidal}:
    forall (b c: B),
      lambda (b•c) == (lambda b [] Id c) \o assoc (unit B) b c.
  Proof.
    intros b c; set (e := unit B).
    assert (H: assoc e b c \o Id e [] lambda(b•c)
               == assoc e b c \o Id e [] (lambda b [] Id c) \o  Id e [] assoc e b c).
    {
      apply symmetry.
      etrans; [apply symmetry, catCa |].
      etrans; [apply catCsc, symmetry, assoc_naturality |].
      etrans; [(do 2 apply catCsc) |].
      - instantiate (1 := (rho e [] Id b) [] Id c \o assoc e e b [] Id c).
        etrans; [| apply fnC].
        simpl; apply Map.substitute; simpl.
        split; [| apply symmetry, catC1f].
        apply symmetry, unit_law.
      - apply symmetry.
        etrans; [apply catCsd, symmetry, unit_law |].
        etrans; [apply symmetry, catCa |].
        etrans; [apply catCsc |].
        simpl.
        + etrans; [apply catCsd |]; simpl.
          * instantiate (1 := ρ (t:=B) e [] (Id b [] Id c)).
            simpl; apply Map.substitute; simpl.
            split; [apply reflexivity |]; simpl.
            etrans; [apply symmetry, fn1 | apply Map.substitute].
            simpl; split; apply reflexivity.
          * apply symmetry, assoc_naturality.
        + etrans; [apply catCa |].
          etrans; [apply catCsd, associativity |].
          etrans; [apply symmetry, catCa |].
          etrans; [apply symmetry, catCa |].
          apply reflexivity.
    }
    assert (H': Id e [] lambda (b•c) ==
                (Id e [] (lambda b [] Id c)) \o Id e [] assoc e b c).
    {
      etrans; [apply symmetry, catCf1 |].
      etrans; [apply catCsc, symmetry, assoc_iso |].
      etrans; [apply catCa |].
      etrans; [apply catCsd, H |].
      etrans; [apply symmetry, catCa |].
      etrans; [apply catCsc, assoc_iso |].
      apply catCf1.
    }
    simpl in H'.
    assert (H'': Id e [] lambda (b•c) ==
                 (Id e [] (lambda b [] Id c \o assoc e b c))).
    {
      etrans; [apply H' |].
      etrans; [apply symmetry, fnC |].
      simpl; unfold Prod.compose; simpl.
      apply Map.substitute; simpl.
      split; [apply catC1f |].
      apply reflexivity.
    }
    simpl in H''.
    apply left_id_functor_injective in H''.
    apply H''.
  Qed.    
    

  Lemma right_id_functor_injective (B: Monoidal):
    forall (a b: B)(f g: B a b),
      f [] Id (unit B) == g [] Id (unit B) -> f == g.
  Proof.
    simpl; intros a b f g Heq.
    assert (H: f \o rho a == g \o rho a).
    {
      etrans; [apply rho_naturality |].
      etrans; [| apply symmetry, rho_naturality].
      apply catCsd, Heq.
    }
    etrans; [| apply catC1f].
    etrans; [apply symmetry, catC1f |].
    etrans; [apply catCsd, symmetry, rho_iso_inv |].
    etrans; [| apply symmetry, catCsd, symmetry, rho_iso_inv].
    etrans; [| apply catCa].
    etrans; [apply symmetry, catCa |].
    apply catCsc, H.
  Qed.    
      
  Lemma kelly_rho {B: Monoidal}:
    forall (a b: B),
      (Id a [] rho b) ==  rho (a•b) \o assoc a b (unit B).
  Proof.
    intros a b; set (e := unit B).
    assert (H: (Id a [] rho b) [] Id e \o assoc a (b•e) e \o Id a [] assoc b e e
               ==
               (rho (a•b) \o assoc a b (unit B)) [] Id e \o assoc a (b•e) e \o Id a [] assoc b e e ).
    {
      etrans; [apply symmetry, catCa |].
      etrans; [apply catCsc, assoc_naturality |].
      etrans; [apply catCa |].
      etrans; [apply catCsd, symmetry, fnC |]; simpl; unfold Prod.compose; simpl.
      etrans; [apply catCsd, Map.substitute |].
      - instantiate (1 := (Id a, (Id b [] lambda e))); simpl.
        split; [apply catCf1 | apply unit_law].
      - etrans; [apply symmetry, assoc_naturality |].
        etrans; [apply catCsc |].
        + instantiate (1 := Id (a•b) [] lambda e).
          apply Map.substitute; split; [| apply reflexivity]; simpl.
          etrans; [| apply fn1]; simpl.
          apply Map.substitute; simpl; split; apply reflexivity.
        + etrans; [apply catCsc, symmetry, unit_law |].
          etrans; [apply catCa |].
          etrans; [apply catCsd, associativity |].
          etrans; [apply symmetry, catCa |].
          etrans; [apply symmetry, catCa |].
          etrans; [| apply catCa ].
          apply catCsc, catCsc.
          etrans; [apply symmetry, fnC |].
          apply Map.substitute; simpl; split; [apply reflexivity | apply catC1f].
    }
    apply right_id_functor_injective.
    assert (H': (assoc a (b•e) e \o Id a [] assoc b e e) \o (Id a [] assoc_inv b e e \o assoc_inv a (b•e) e) == Id _).
    {
      etrans; [apply catCa |].
      etrans; [apply catCsd, symmetry, catCa |].
      etrans; [apply catCsd, catCsc; instantiate (1 := Id _) |].
      - etrans; [apply symmetry, fnC |].
        etrans; [| apply fn1].
        apply Map.substitute; simpl; split; [apply catCf1 | apply assoc_iso_inv].
      - etrans; [apply catCsd, catCf1 | apply assoc_iso_inv].
    }
    etrans; [apply symmetry, catC1f |].
    etrans; [apply catCsd, symmetry, H' |].
    etrans; [apply symmetry, catCa |].
    etrans; [apply catCsc, H |].
    etrans; [apply catCa |].
    etrans; [apply catCsd, H' |].
    apply catC1f.
  Qed.    

  Lemma kelly_unit (B: Monoidal):
    let e := unit B in lambda e == rho e.
  Proof.
    intros.
    apply right_id_functor_injective.
    assert (Hl: lambda e [] Id e == lambda (e•e) \o assoc_inv e e e).
    {
      etrans; [apply symmetry, catC1f |].
      etrans; [apply catCsd, symmetry, assoc_iso_inv |].
      etrans; [apply symmetry, catCa |].
      apply catCsc, symmetry, (kelly_lambda e e).
    }
    assert (Hr: rho e [] Id e == (Id e [] lambda e) \o assoc_inv e e e).
    {
      etrans; [apply symmetry, catC1f |].
      etrans; [apply catCsd, symmetry, assoc_iso_inv |].
      etrans; [apply symmetry, catCa |].
      apply catCsc, unit_law.
    }
    etrans; [apply Hl |].
    etrans; [| apply symmetry, Hr].
    apply catCsc.
    etrans; [apply symmetry, catC1f |].
    assert (H: Id e [] lambda_inv e \o Id e [] lambda e == Id _).
    {
      etrans; [apply symmetry, fnC |].
      etrans; [| apply fn1].
      apply Map.substitute; simpl; split; [apply catC1f | apply lambda_iso].
    }
    etrans; [apply catCsd, symmetry, H |].
    etrans; [apply symmetry, catCa |].
    etrans; [apply catCsc, symmetry, lambda_naturality |].
    etrans; [apply catCsc, lambda_iso | apply catCf1].
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
      etrans; [apply catCa |].
      etrans; [apply catCsd, mu_law |].
      etrans; [apply symmetry, catCa |].
      etrans; [apply catCsc, mu_law |].
      etrans; [apply catCa |]; simpl.
      etrans; [apply catCsd, symmetry, fnC |]; simpl.
      unfold Prod.compose; simpl.
      apply reflexivity.
    Qed.
    Next Obligation.
      intros; simpl.
      etrans; [apply catCa |].
      etrans; [apply catCsd, eta_law |].
      apply eta_law.
    Qed.

    Program Definition id (B: Monoidal)(c: Monoid B): morph c c :=
      build (Id c).
    Next Obligation.
      simpl; intros.
      etrans; [apply catCf1 |].
      generalize (fn1 (spec:=Monoidal.mult B) (X:=(obj c,obj c))); simpl.
      unfold Prod.id; simpl; intros H.
      etrans; [| apply catCsd, symmetry, H].
      apply symmetry, catC1f.
    Qed.
    Next Obligation.
      intros; simpl; apply catCf1.
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
    simpl; intros; apply catCs; assumption.
  Qed.
  Next Obligation.
    simpl; intros; apply catCa.
  Qed.
  Next Obligation.
    simpl; intros; apply catC1f.
  Qed.
  Next Obligation.
    simpl; intros; apply catCf1.
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


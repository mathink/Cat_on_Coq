Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Construction.

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
    rewrite <- catCf1, <- assoc_iso, !catCa.
    generalize (catCa (h:=α (t:=B) a' b' c')(g:=f [] (g [] h))(f:=α^-1 (t:=B) a b c)).
    intros H; rewrite <- H.
    rewrite <- assoc_naturality, catCa.
    now rewrite assoc_iso_inv, catC1f. 
  Qed.    

  Lemma lambda_inv_naturality {B: Monoidal}:
    forall (a a': B)(f: B a a'),
      (Id (unit B) [] f) \o lambda_inv a == lambda_inv a' \o f.
  Proof.
    intros.
    rewrite <- catCf1.
    rewrite <- lambda_iso, catCa.
    rewrite <- (catCa (g:=(Id Munit B [] f))).
    rewrite <- lambda_naturality.
    rewrite catCa.
    now rewrite lambda_iso_inv, catC1f.
  Qed.

  Lemma rho_inv_naturality {B: Monoidal}:
    forall (a a': B)(f: B a a'),
      (f [] Id (unit B)) \o rho_inv a == rho_inv a' \o f.
  Proof.
    intros.
    rewrite <- catCf1.
    rewrite <- rho_iso, catCa.
    rewrite <- (catCa (g:=(f [] Id Munit B))).
    rewrite <- rho_naturality.
    rewrite catCa.
    now rewrite rho_iso_inv, catC1f.
  Qed.

  Lemma left_id_functor_injective (B: Monoidal):
    forall (a b: B)(f g: B a b),
      Id (unit B) [] f == Id (unit B) [] g -> f == g.
  Proof.
    intros.
    assert (H': f \o lambda a == g \o lambda a).
    {
      now rewrite lambda_naturality, H, <- lambda_naturality.
    }
    now rewrite <- catC1f, <- lambda_iso_inv, <- catCa, H', catCa, lambda_iso_inv, catC1f.
  Qed.
      
  Lemma kelly_lambda {B: Monoidal}:
    forall (b c: B),
      lambda (b•c) == (lambda b [] Id c) \o assoc (unit B) b c.
  Proof.
  Admitted.

  Lemma right_id_functor_injective (B: Monoidal):
    forall (a b: B)(f g: B a b),
      f [] Id (unit B) == g [] Id (unit B) -> f == g.
  Proof.
    intros.
    rewrite <- (catC1f (f:=f)).
    rewrite <- (catC1f (f:=g)).
    rewrite <- rho_iso_inv.
    rewrite <- !catCa.
    now rewrite !rho_naturality, H; simpl.
  Qed.
      
  Lemma kelly_rho {B: Monoidal}:
    forall (a b: B),
      (Id a [] rho b) ==  rho (a•b) \o assoc a b (unit B).
  Proof.
  Admitted.

  Lemma kelly_unit (B: Monoidal):
    let e := unit B in lambda e == rho e.
  Proof.
  Admitted.
  (*   intros. *)
  (*   apply right_id_functor_injective. *)
  (*   assert (Hl: lambda e [] Id e == lambda (e•e) \o assoc_inv e e e). *)
  (*   { *)
  (*     etrans; [apply symmetry, catC1f |]. *)
  (*     etrans; [apply catCsd, symmetry, assoc_iso_inv |]. *)
  (*     etrans; [apply symmetry, catCa |]. *)
  (*     apply catCsc, symmetry, (kelly_lambda e e). *)
  (*   } *)
  (*   assert (Hr: rho e [] Id e == (Id e [] lambda e) \o assoc_inv e e e). *)
  (*   { *)
  (*     etrans; [apply symmetry, catC1f |]. *)
  (*     etrans; [apply catCsd, symmetry, assoc_iso_inv |]. *)
  (*     etrans; [apply symmetry, catCa |]. *)
  (*     apply catCsc, unit_law. *)
  (*   } *)
  (*   etrans; [apply Hl |]. *)
  (*   etrans; [| apply symmetry, Hr]. *)
  (*   apply catCsc. *)
  (*   etrans; [apply symmetry, catC1f |]. *)
  (*   assert (H: Id e [] lambda_inv e \o Id e [] lambda e == Id _). *)
  (*   { *)
  (*     etrans; [apply symmetry, fnC |]. *)
  (*     etrans; [| apply fn1]. *)
  (*     apply Map.substitute; simpl; split; [apply catC1f | apply lambda_iso]. *)
  (*   } *)
  (*   etrans; [apply catCsd, symmetry, H |]. *)
  (*   etrans; [apply symmetry, catCa |]. *)
  (*   etrans; [apply catCsc, symmetry, lambda_naturality |]. *)
  (*   etrans; [apply catCsc, lambda_iso | apply catCf1]. *)
  (* Qed. *)

  
End Monoidal.
Export Monoidal.Ex.

Module MonoidObject.
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
    Notation isMonoidObject := spec.
    Notation MonoidObject := type.
    Coercion obj: type >-> Category.obj.
    Coercion prf: type >-> spec.
    Existing Instance prf.
  End Ex.
  Import Ex.

  Module morphism.
    Class spec (B: Monoidal)(c c': MonoidObject B)(f: B c c') :=
      proof {
          mu_law:
            f \o mu c == mu c' \o (f [] f);

          eta_law:
            f \o eta c == eta c'
        }.

    Class type (B: Monoidal)(c c': MonoidObject B) :=
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

    Program Definition compose (B: Monoidal)(c d e: MonoidObject B)(f: morph c d)(g: morph d e): morph c e :=
      build (g \o f).
    Next Obligation.
      now rewrite catCa, mu_law, <-catCa, mu_law, catCa, <- fnC; simpl.
    Qed.
    Next Obligation.
      now rewrite catCa, !eta_law.
    Qed.

    Program Definition id (B: Monoidal)(c: MonoidObject B): morph c c :=
      build (Id c).
    Next Obligation.
      rewrite catCf1.
      generalize (fn1 (spec:=Monoidal.mult B) ((obj c, obj c))); simpl.
      unfold Prod.id; simpl; intros H.
      now rewrite H, catC1f.
    Qed.
    Next Obligation.
      intros; simpl; apply catCf1.
    Qed.

    Definition equal (B: Monoidal)(c d: MonoidObject B)(f g: morph c d) := f == g.
    Arguments equal B c d f g /.

    Program Definition setoid (B: Monoidal)(c d: MonoidObject B) :=
      Setoid.build (@equal B c d).
    Next Obligation.
      intros f; simpl; reflexivity.
    Qed.
    Next Obligation.
      now intros f g; simpl; symmetry.
    Qed.
    Next Obligation.
      now intros f g h; simpl; transitivity g.
    Qed.
  End morphism.
  Import morphism.
  Import morphism.Ex.
  
  Program Definition category (B: Monoidal): Category :=
    Category.build (@setoid B)
                   (@compose B)
                   (@id B).
  Next Obligation.
    now intros f f' Hf g g' Hg; simpl; apply catCs.
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
    - reflexivity.
    - reflexivity.
  Qed.

  Definition forgetful (B: Monoidal) := Functor.make (forgetful_isF B).
  
  Module mEx.
    Module MonoidObject := morphism.Ex.
  End mEx.
End MonoidObject.
Export MonoidObject.Ex.
Export MonoidObject.mEx.


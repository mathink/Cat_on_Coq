Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.


Module Comma.
  (* 
      E -- T -> C <- S -- D
   *)
  Record obj (E C D: Category)(T: Functor E C)(S: Functor D C) :=
    triple { dom: E; cod: D; morph: C (T dom) (S cod)}.

  Module Ex.
    Arguments morph: clear implicits.
    Arguments morph {E C D T S}(o).
    Coercion morph: obj >-> Setoid.carrier.
  End Ex.    
  Import Ex.
  
  Class spec (E C D: Category)(T: Functor E C)(S: Functor D C)
        (f g: obj T S)(k: E (dom f) (dom g))(h: D (cod f) (cod g)) :=
    proof {
        comm: g \o fmap T k == fmap S h \o f
      }.

  Structure type (E C D: Category)(T: Functor E C)(S: Functor D C)(f g: obj T S) :=
    make {
        dmorph: E (dom f) (dom g);
        cmorph: D (cod f) (cod g);

        prf: spec dmorph cmorph
      }.

  Module MorphEx.
    Coercion prf: type >-> spec.
    Existing Instance prf.

    Notation build f g := (@make _ _ _ _ _ _ _ f g (@proof _ _ _ _ _ _ _ _ _ _)).
  End MorphEx.
  Import MorphEx.

  
  Program Definition compose {E C D: Category}(T: Functor E C)(S: Functor D C)
          (f g h: obj T S)(kh1: type f g)(kh2: type g h): type f h :=
    build (dmorph kh2 \o dmorph kh1) (cmorph kh2 \o cmorph kh1).
  Next Obligation.
    intros.
    now rewrite fnC, <- catCa, comm, catCa, comm, fnC, catCa.
  Qed.

  Program Definition id {E C D: Category}(T: Functor E C)(S: Functor D C)(f: obj T S): type f f :=
    build (Id (dom f)) (Id (cod f)).
  Next Obligation.
    now rewrite !fn1, catCf1, catC1f.
  Qed.

  Definition equal {E C D: Category}(T: Functor E C)(S: Functor D C)(f g: obj T S): relation (type f g) :=
    fun kh1 kh2 =>
       (dmorph kh1) == (dmorph kh2) /\ (cmorph kh1) == (cmorph kh2).
  Arguments equal E C D T S f g kh1 kh2 /.

  Program Definition setoid {E C D: Category}(T: Functor E C)(S: Functor D C)(f g: obj T S) :=
    Setoid.build (@equal _ _ _ T S f g).
  Next Obligation.
    intros; split; apply reflexivity.
  Qed.
  Next Obligation.
    intros; split; apply symmetry; apply H.
  Qed.
  Next Obligation.
    intros; split; eapply transitivity; try (apply H || apply H0).
  Qed.
  
  Program Definition category {E C D: Category}(T: Functor E C)(S: Functor D C): Category :=
    Category.build (@setoid _ _ _ T S)
                   (@compose _ _ _ T S)
                   (@id _ _ _ T S).
  Next Obligation.
    intros f f' [Hfd Hfc] g g' [Hgd Hgc]; simpl in *.
    now rewrite Hfd, Hfc, Hgd, Hgc.
  Qed.
  Next Obligation.
    now rewrite !catCa.
  Qed.
  Next Obligation.
    now rewrite !catC1f.
  Qed.
  Next Obligation.
    now rewrite !catCf1.
  Qed.
End Comma.
Export Comma.MorphEx.

Definition CommaTo (C D: Category)(c: C)(S: Functor D C): Category :=
  Comma.category (ConstFunctor C c) S.

Definition CommaFrom (C D: Category)(S: Functor D C)(c: C): Category :=
  Comma.category S (ConstFunctor C c).

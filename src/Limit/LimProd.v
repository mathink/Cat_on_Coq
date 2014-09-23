(* -*- mode: coq -*- *)
(* Time-stamp: <2014/9/24 2:6:44> *)
(*
  LimProd.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Require Import Category Functor Cone Discrete.

(** * 例： 直積は圏 2 からの函手の極限である  *)

Section ProdAsLim.

  Context (C: Category)(X Y: C).
  (** ** 圏 2 構成 *)
  Let DC2 := Discr_Category 2.

  (**
      これら二つの証明がそれぞれ圏 2 の対象である。
   *)
  Lemma ltb02: ltb 0 2 = true.
  Proof. reflexivity. Qed.

  Lemma ltb12: ltb 1 2 = true.
  Proof. reflexivity. Qed.


  (** ** 圏 2 から圏 C への函手の構成
      構成そのものは比較的容易である。
   *)
  Program Definition fobj_prod (k: DC2): C :=
    let (n, H) := k in
    match n with
      | 0 => X
      | 1 => Y
      | _ => _
    end.
  Next Obligation.
    simpl.
    assert (ltb n 2 = false).
    { destruct n; try tauto.
      destruct n; try tauto.
      unfold ltb; simpl; destruct n; simpl; tauto. }
    rewrite H2 in H; discriminate.
  Qed.

  (** 射函数の定義そのものはあまり重要ではないので、証明モードを利用する *)
  Definition fmap_prod_body (n m: DC2)(k: DC2 n m): C (fobj_prod n) (fobj_prod m).
    revert k.
    destruct n as [n Hn].
    destruct m as [m Hm].
    destruct n as [| [| n]];
      destruct m as [| [| m]];
      simpl; intro k; try now inversion k.
    - exact (Id X).
    - exact (Id Y).
    - destruct n; simpl in Hn; discriminate.
  Defined.

  Definition fmap_prod: Fmap DC2 C fobj_prod :=
    fun (n m: DC2) => [ k :-> fmap_prod_body k ].

  Instance prod_IsFunctor: isFunctor fmap_prod.
  Proof.
    split; simpl; intros; subst.
    - destruct Z as [[| [| n]] Hn]; simpl;
      try (destruct n; simpl in Hn; discriminate);
      now symmetry; apply identity_dom.
    - destruct X0 as [[| [| n]] Hn]; simpl;
      try (destruct n; simpl in Hn; discriminate);
      reflexivity.
  Qed.

  Definition prod_Functor: Functor DC2 C :=
    Build_Functor  prod_IsFunctor.

  (** ** 極限が直積であることの証明  *)
  (** まずは任意の X <- Q -> Y から、上で定義した函手への錐を構成する。 *)
  Program Definition PUniq
           (Q: C)(qX: C Q X)(qY: C Q Y)(i: DC2)
  : C Q (prod_Functor i).
  revert i; intros [[| [| n]] Hn];
  try (destruct n; simpl in Hn; discriminate); simpl;
  [exact qX | exact qY].
  Defined.

  Lemma Q_IsICone (Q: C)(qX: C Q X)(qY: C Q Y)
  : isICone (PUniq qX qY).
  Proof.
    intros [[| [| n]] Hn];
    try (destruct m; simpl in Hn; discriminate);
    intros [[| [| m]] Hm];
    try (destruct m; simpl in Hn; discriminate);
    intro Heq; simpl;
    try (now inversion Heq);
    now apply identity_cod.
  Qed.

  (** 錐の圏が構成できた。
      これは任意の X <- Q -> Y について構成でき、この圏の終対象が X と Y の直積となる。
   *)
  Canonical Structure QICone
            (Q: C)(qX: C Q X)(qY: C Q Y)
  : ICone prod_Functor := Build_ICone (Q_IsICone qX qY).

  (** その証明  *)
  Program Instance lim_is_prod (P: Limit prod_Functor)
  : isProd (igen (term P) (Elem ltb02))
           (igen (term P) (Elem ltb12))
           (fun Q qX qY => terminal P (QICone qX qY)).
  Next Obligation.
    now rewrite (icmap_commute (f := terminal P (QICone (Q:=Q) qX qY)) {| dbody := 0; prf_Elem := ltb02 |}); simpl.
  Qed.
  Next Obligation.
    now rewrite (icmap_commute (f := terminal P (QICone (Q:=Q) qX qY)) {| dbody := 1; prf_Elem := ltb12 |}); simpl.
  Qed.
  Next Obligation.
    simpl.
    generalize (terminal_uniqueness (terminal:= terminal P)); simpl; intro.
    assert (@isICMap _ _ _ (QICone qX qY) (term P) f).
    { intros [[| [| n]] Hn]; simpl;
        try (destruct n; simpl in Hn; discriminate).
      - rewrite (prf_Elem_unique Hn ltb02); exact H.
      - rewrite (prf_Elem_unique Hn ltb12); exact H0. }
    generalize (H1 _ (Build_ICMap H2)); simpl.
    unfold equal_ICMap; simpl.
    now intro Heq; rewrite Heq.
  Qed.

  Definition LimProd (P: Limit prod_Functor): Prod X Y := 
    Build_Prod (lim_is_prod P).

End ProdAsLim.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Category.

Module UniversalArrow.
  Module To.
    (* 
          Sr    r
       u/  |    |
      c   Sf'   f'
       f\  V    V  
          Sd    d
     *)
    (* TODO *)
    Class spec {C D: Category}(c: C)(S: Functor D C)(r: D)(u: C c (S r))(univ: forall {d}, (C c (S d)) -> (D r d)): Prop :=
      proof {
          univ_subst:> forall d, Proper ((==) ==> (==)) (@univ d);
          ump: forall d (f: C c (S d)),
            fmap S (univ f) \o u == f;
          uniq:
            forall (d: D)(f: C c (S d))(f': D r d),
              fmap S f' \o u == f -> f' == univ f
        }.

    Structure type {C D: Category}(c: C)(S: Functor D C) :=
      make {
          obj: D;
          arrow: C c (S obj);
          univ: forall {d}, (C c (S d)) -> (D obj d);
          prf: spec arrow (@univ)
        }.

    Notation build arrow univ := (@make _ _ _ _ _ arrow univ (@proof _ _ _ _ _ _ _ _ _ _)).

    Module Ex.
      Notation "'[UA' c ':=>' F ]" := (type c F) (no associativity).
    End Ex.
  End To.

  Module From.
    (* 
      d    Sd
      |     | \f
      f'   Sf'  c
      V     V /v
      r    Sr
     *)

    Class spec {C D: Category}(S: Functor D C)(c: C)(r: D)(v: C (S r) c)(univ: forall {d}, (C (S d) c) -> (D d r)): Prop :=
      proof {
          univ_subst:> forall d, Proper ((==) ==> (==)) (@univ d);
          ump: forall d (f: C (S d) c), v \o fmap S (univ f) == f;
          universality:
            forall (d: D)(f: C (S d) c)(f': D d r),
              v \o fmap S f' == f -> f' == univ f
        }.

    Structure type {C D: Category}(S: Functor D C)(c: C) :=
      make {
          obj: D;
          arrow: C (S obj) c;
          univ: forall {d}, (C (S d) c) -> (D d obj);

          prf: spec arrow (@univ)
        }.

    Notation build arrow univ := (@make _ _ _ _ _ arrow univ (@proof _ _ _ _ _ _ _ _ _ _)).

    Module Ex.
      Notation "'[UA' c '<=:' F ]" := (type F c) (no associativity).
    End Ex.
  End From.

End UniversalArrow.
Export UniversalArrow.To.Ex.
Export UniversalArrow.From.Ex.

Module UATo := UniversalArrow.To.
Module UAFrom := UniversalArrow.From.

Require Import COC.Structure.

(* Program Definition CommaInitUA (C D: Category)(S: Functor D C)(c: C)(i: Initial (CommaTo c S)): [UA c :=> S] := *)
(*   let r := (Comma.cod (@Initial.obj _ i)) in *)
(*   let u := (Comma.morph (@Initial.obj _ i)) in *)
(*   UATo.build u (fun d (f: C c (S d)) => *)
(*                   Comma.cmorph (Initial.univ i (Comma.triple (T:=ConstFunctor C c)(dom:=c) f))). *)
(* Next Obligation. *)
(*   intros f f' Heq; simpl. *)
(*   generalize (@Initial.ump _ _ _ i ); simpl; intro. *)

(*   destruct Setoid.equal. *)
(*   Check (H0 ). *)
(*   apply  *)
(* Next Obligation. *)
  
(*   intros; simpl in *. *)
(*   set (df := (Comma.triple (T:=ConstFunctor c)(dom:=c) f)). *)
(*   set (m:=(@Initial.univ _ i df)). *)
(*   generalize (@Comma.comm _ _ _ _ _ _ _ _ _ m). *)
(*   set (f':= Comma.cmorph m). *)
(*   intros H; simpl in *. *)
(*   exists f'; split. *)
(*   - eapply transitivity; [| apply Category.comp_id_dom]. *)
(*     apply symmetry, H. *)
(*   - intros g' Heq. *)
(*     assert (H': f \o Id c == fmap S g' \o Comma.morph (Initial.obj i)). *)
(*     { *)
(*       eapply transitivity; [apply Category.comp_id_dom |]. *)
(*       apply symmetry, Heq. *)
(*     } *)
(*     set (spec := @Comma.proof _ _ _ (ConstFunctor c) S (Initial.obj i) df (Comma.dmorph m) g' H'). *)
(*     set (dg' := Comma.make spec); simpl in *. *)
(*     generalize  (@Initial.ump _ _ _ i _ dg'); simpl; intros [Heq' Heqg']. *)
(*     eapply transitivity; [| apply symmetry, Heqg']. *)
(*     apply reflexivity. *)
(* Qed. *)

(* Program Definition CommaTermUA (C D: Category)(c: C)(S: Functor D C)(t: Terminal (CommaFrom S c)): [UA c <=: S] := *)
(*   let r := (Comma.cod (Terminal.obj t)) in *)
(*   let u := (Comma.morph (Terminal.obj t)) in *)
(*   UAFrom.build u. *)
(* Next Obligation. *)
(*   intros; simpl in *. *)
(*   set (df := (Comma.triple (S:=ConstFunctor c)(cod:=c) f)). *)
(*   set (m:=(@Terminal.univ _ t df)). *)
(*   generalize (@Comma.comm _ _ _ _ _ _ _ _ _ m). *)
(*   set (f':=(Comma.dmorph m)) in *. *)
(*   intros H; simpl in *. *)
(*   exists f'; split. *)
(*   - eapply transitivity; [| apply Category.comp_id_cod]. *)
(*     apply H. *)
(*   - intros g' Heq. *)
(*     assert (H': Comma.morph (Terminal.obj t) \o fmap S g' == Id c \o f). *)
(*     { *)
(*       eapply transitivity; [apply Heq | apply symmetry, Category.comp_id_cod ]. *)
(*     } *)
(*     set (spec := Comma.proof (T:=S)(S:=ConstFunctor c)(f:=df)(k:=g')(h:=Comma.cmorph m) H').  *)
(*     set (dg' := Comma.make spec); simpl in *. *)
(*     generalize  (@Terminal.ump _ _ _ t _ dg'); simpl; intros [Heqg' Heq']. *)
(*     eapply transitivity; [| apply symmetry, Heqg']. *)
(*     apply reflexivity. *)
(* Qed. *)

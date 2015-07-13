(* -*- mode: coq -*- *)
(* Time-stamp: <2014/11/30 15:34:59> *)
(*
  TAlgebra.v
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Generalizable All Variables.


Require Import Category Functor Natrans Monad.

(** T-Algebra  *)
Class isTAlg `(m: Monad C)(X: C)(h: C (m X) X) :=
  {
    talg_mu:
      h \o monad_mu m X == h \o fmap m h;

    talg_eta:
      h \o monad_eta m X == Id X
  }.

Structure TAlg `(m: Monad C) :=
  {
    talg_obj:> C;
    talg_arr:> C (m talg_obj) talg_obj;

    prf_TAlg:> isTAlg talg_arr
  }.
Existing Instance prf_TAlg.

(** morphism between T-Algebra  *)
Class isTAlgMap `{m: Monad C}(X Y: TAlg m)(f: C X Y) :=
  {
    talg_map_comm:
      f \o X == Y \o fmap m f
  }.

Structure TAlgMap `{m: Monad C}(X Y: TAlg m) :=
  {
    talg_map:> C X Y;
    prf_TAlgMap:> isTAlgMap talg_map
  }.
Existing Instance prf_TAlgMap.

(** composition *)
Program Definition compose_TAlgMap `{m: Monad C}
        (X Y Z: TAlg m)
        (f: TAlgMap X Y)(g: TAlgMap Y Z): TAlgMap X Z :=
  {|
    talg_map := g \o f
  |}.
Next Obligation.
  split.
  rewrite (fmap_comp m), compose_assoc,
  talg_map_comm, <- compose_assoc, talg_map_comm, compose_assoc.
  reflexivity.
Qed.
Arguments compose_TAlgMap C m X Y Z / f g.

(** identity  *)
Program Definition id_TAlgMap `{m: Monad C}(X: TAlg m): TAlgMap X X :=
  {|
    talg_map := ident (c:=C) X
  |}.
Next Obligation.
  split.
  rewrite (fmap_ident m); rewrite identity_dom; apply identity_cod.
Qed.

Definition equal_TAlgMap `{m: Monad C}(X Y: TAlg m)(f g: TAlgMap X Y)
  := (f: C X Y) == (g: C X Y).
Arguments equal_TAlgMap C m X Y / f g.

Instance equal_TAlgMap_Equiv `{m: Monad C}(X Y: TAlg m)
: Equivalence (equal_TAlgMap (X:=X)(Y:=Y)).
Proof.
  split; simpl.
  - now intros f; simpl.
  - now intros f g Heq.
  - now intros f g h Heqfg Heqgh; rewrite Heqfg.
Qed.

Canonical Structure Setoid_TAlgMap `{m: Monad C}(X Y: TAlg m)
  := Build_Setoid (equal_TAlgMap_Equiv X Y).

Instance Compose_TAlgMap `(m: Monad C): Compose (@Setoid_TAlgMap _ m) :=
  { compose X Y Z f g := @compose_TAlgMap C m X Y Z f g }.
Proof.
  now intros X Y Z f f' Heqf g g' Heqg; simpl in *; rewrite Heqf, Heqg.
Defined.

Instance Identity_TAlgMap `(m: Monad C): Identity (@Setoid_TAlgMap _ m) :=
  { identity := @id_TAlgMap C m }.

Program Instance TAlg_IsCategory `(m: Monad C)
: isCategory (Compose_TAlgMap m) (Identity_TAlgMap m).
Next Obligation.
  now apply compose_assoc.
Qed.
Next Obligation.
  now apply identity_dom.
Qed.
Next Obligation.
  now apply identity_cod.
Qed.

Canonical Structure TALG `(m: Monad C): Category :=
  Build_Category (TAlg_IsCategory m).



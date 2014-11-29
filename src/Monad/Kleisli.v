(* -*- mode: coq -*- *)
(* Time-stamp: <2014/11/29 15:25:14> *)
(*
  Kleisli.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Require Import Category Functor.

(** * クライスリトリプル  *)
Class isKT (C: Category)(T: C -> C)
      (emb: forall X: C, C X (T X))
      (bind: forall {X Y: C}, Map (C X (T Y)) (C (T X) (T Y))): Prop :=
  { bind_emb:
      forall X: C,
        bind (emb X) == Id (T X);

    emb_bind:
      forall (X Y: C)(f: C X (T Y)),
        bind f \o emb X == f;

    bind_assoc:
      forall (X Y Z: C)(f: C X (T Y))(g: C Y (T Z)),
        bind g \o bind f == bind (bind g \o f) }.

Structure KT (C: Category) :=
  { kt_fun:> C -> C;
    emb: forall X: C, C X (kt_fun X);
    bind: forall {X Y: C}, Map (C X (kt_fun Y)) (C (kt_fun X) (kt_fun Y));
    
    prf_KT: isKT emb (@bind) }.
Existing Instance prf_KT.




(* -*- mode: coq -*- *)
(*
  MonoidObj.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable All Variables.

Require Import Category Functor Natrans Monoidal.

Class isMonoid `(V: MonoidalCategory)
      (M: V)(mul: V (mcX V (M,M)) M)(uni: V (mcI V) M) :=
  {
    mon_assoc:
      mul \o (mul [x V] Id M) == mul \o (Id M [x V] mul) \o mcA V;

    mon_unit_l:
      mc1X V M == mul \o (uni [x V] Id M);
    mon_unit_r:
      mcX1 V M == mul \o (Id M [x V] uni)
  }.

Structure Monoid `(V: MonoidalCategory) :=
  {
    mon_obj:> V;
    mon_mul: V (mcX V (mon_obj, mon_obj)) mon_obj;
    mon_uni: V (mcI V) mon_obj;

    prf_Monoid:> isMonoid mon_mul mon_uni
  }.



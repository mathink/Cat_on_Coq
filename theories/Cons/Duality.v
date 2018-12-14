(** * Terminal Object **)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.
From COC.Cons Require Import Initial Terminal Product Coproduct Equalizer Coequalizer.

(** Initial and Terminal **)
Program Definition terminal_from_initial (C: Category)(i: Initial C): Terminal C^op :=
  [Terminal by (initial_univ i)].
Next Obligation.
  now apply initial_uniqueness.
Qed.

Program Definition initial_from_terminal (C: Category)(t: Terminal C): Initial C^op :=
  [Initial by (terminal_univ t)].
Next Obligation.
  now apply terminal_uniqueness.
Qed.

(** Product and Coproduct **)
Program Definition coproduct_from_product (C: Category)(X Y: C)(P: Product C X Y)
  : Coproduct C^op X Y :=
  [Coproduct by (fun (Z: C) f g => [f , g to P])
   with pi1_{P}, pi2_{P}].
Next Obligation.
  - now apply product_universality_1.
  - now apply product_universality_2.
  - now apply product_uniqueness.
Qed.

Program Definition product_from_coproduct (C: Category)(X Y: C)(CP: Coproduct C X Y)
  : Product C^op X Y :=
  [Product by (fun (Z: C) f g => [f , g from CP])
   with in1_{CP}, in2_{CP}].
Next Obligation.
  - now apply coproduct_universality_1.
  - now apply coproduct_universality_2.
  - now apply coproduct_uniqueness.
Qed.

(** Equalizer and Coequalizer **)
Program Definition coequalizer_from_equalizer (C: Category)(X Y: C)(f g: C X Y)(eq: Equalizer f g)
  : Coequalizer (C:=C^op) f g :=
  [Coequalizer by fun (Z: C)(h: C Z X)(Heq: f \o h == g \o h) =>
                    equalizer_univ eq Heq
   with equalizer_map eq].
Next Obligation.
  - now apply equalize.
  - now apply equalizer_universality.
  - now apply equalizer_uniqueness.
Qed.

Program Definition equalizer_from_coequalizer (C: Category)(X Y: C)(f g: C X Y)(coeq: Coequalizer f g)
  : Equalizer (C:=C^op) f g :=
  [Equalizer by fun (Z: C)(k: C Y Z)(Heq: k \o f == k \o g) =>
                    coequalizer_univ coeq Heq
   with coequalizer_map coeq].
Next Obligation.
  - now apply coequalize.
  - now apply coequalizer_universality.
  - now apply coequalizer_uniqueness.
Qed.

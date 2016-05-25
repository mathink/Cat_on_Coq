Set Implicit Arguments.
Unset Strict Implicit.
Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Category.
Require Import COC.Constitution.Equalizer.

(* Module Kernel. *)
  
(*   Class spec (C: Category)(z: Zero C)(X Y: C)(f: C X Y)(Kerf: C)(kerf: C Kerf X) := *)
(*     proof { *)
(*         null: f \o kerf == zero z Kerf Y; *)
(*         ump: forall K (k: C K X), f \o k == zero z K Y -> *)
(*                                   exists!_ k': C K Kerf, kerf \o k' == k *)
(*       }. *)
 
(*   Structure type (C: Category)(z: Zero C)(X Y: C)(f: C X Y) := *)
(*     make { *)
(*         obj: C; *)
(*         arr: C obj X; *)

(*         prf: spec z f arr *)
(*       }. *)

(*   Module Ex. *)
(*     Notation isKernel := spec. *)
(*     Notation Kernel := type. *)

(*     Coercion obj: Kernel >-> Category.obj. *)
(*     Coercion arr: Kernel >-> Setoid.carrier. *)
(*     Coercion prf: Kernel >-> isKernel. *)

(*     Existing Instance prf. *)
(*     Arguments ump {C}(z){X Y}(f){Kerf kerf}(spec){K}(k) _: clear implicits. *)
(*   End Ex. *)

(* End Kernel. *)
(* Export Kernel.Ex. *)

(* Program Instance Kernel_is_equalizer `(z: Zero C)`(f: C X Y)(kerf: Kernel z f): *)
(*   isEqualizer f (zero z X Y) kerf. *)
(* Next Obligation. *)
(*   intros; simpl. *)
(*   eapply transitivity. *)
(*   now apply Kernel.null. *)
(*   apply symmetry, zero_comp_zero_dom. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros; rename z into zr, z0 into z. *)
(*   assert (H': f \o z == zero zr Z Y). *)
(*   { *)
(*     eapply transitivity; [apply H |]. *)
(*     now apply zero_comp_zero_dom. *)
(*   } *)
(*   apply (Kernel.ump zr f kerf z H'). *)
(* Qed. *)
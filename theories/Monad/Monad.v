Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Universe Polymorphism.

Require Import COC.Base.Main.


Class IsMonad (C: Category)
      (T: C --> C)
      (unit: Id C ==> T)
      (mult: (T \o T) ==> T) :=
  {
    monad_mult_mult:
      mult \o (mult o> T) == mult \o (T <o mult) \o Nassoc_inv;

    monad_mult_unit_T:
      mult \o (unit o> T) \o [* ==> 1 \o *] == Id T;
    
    monad_mult_T_unit:
      mult \o (T <o unit) \o [* ==> * \o 1] == Id T
  }.

Structure Monad (C: Category) :=
  {
    monad_functor:> C --> C;
    monad_unit: Id C ==> monad_functor;
    monad_mult: (monad_functor \o monad_functor) ==> monad_functor;

    monad_prf:> IsMonad monad_unit monad_mult
  }.
Existing Instance monad_prf.
Notation "[ 'Monad' 'by' T , u , m ]" := (@Build_Monad _ T u m _).




Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Generalizable All Variables.

(** * プログラミング用
    モナドとかな。
 *)

Require Import Category Functor Natrans.

Class isMonad (C: Category)(T: Functor C C)
      (emb: forall {X: C}, C X (T X))
      (bind: forall {X Y: C}, Map (C X (T Y)) (C (T X) (T Y))) :=
  {
    monad_emb_bind:
      forall (X Y: C)(f: C X (T Y)),
        bind f \o emb == f;

    monad_bind_emb:
      forall (X: C),
        bind (emb (X:=X)) == ident (T X);

    monad_bind_assoc:
      forall (X Y Z: C)(f: C X (T Y))(g: C Y (T Z)),
        bind g \o bind f == bind (bind g \o f)
  }.

Class Monad {C: Category}(T: Functor C C) :=
  {
    monad_emb: forall {X: C}, C X (T X);
    monad_bind: forall {X Y: C}, Setoids (C X (T Y)) (C (T X) (T Y));

    prf_Monad: isMonad (@monad_emb) (@monad_bind)
  }.

Section Playground.

  Require Import ListFunctor.

  (* option as Functor  *)
  Program Definition fmap_option: Fmap Sets Sets option :=
    fun X Y => [ f :-> fun m => match m with
                                         | Some x => Some (f x)
                                         | None   => None
                                       end ].
  Next Obligation.
    now intros f f' Heqf [x|]; [rewrite Heqf |].
  Qed.

  Instance option_isFunctor: isFunctor fmap_option.
  Proof.
    now split; intros; intros [x|]; simpl.
  Defined.

  Definition option_Functor: Functor Sets Sets := 
    Build_Functor option_isFunctor.


  (* option as Monad *)
  Definition option_emb (X: Sets): Sets X (option X) := Some (A:=X).
  Program Definition option_bind (X Y: Sets)
  : Map (Sets X (option Y)) (Sets (option X) (option Y)) :=
    [ f :-> fun m => match m with Some x => f x | None => None end ].
  Next Obligation.
    now intros f f' Heqf [x|]; try apply Heqf.
  Qed.

  Instance option_isMonad: isMonad (T:=option_Functor) option_emb option_bind.
  Proof.
    now split; intros; try (now idtac); intros [x|]; simpl.
  Defined.

  Definition option_Monad: Monad option_Functor :=
    Build_Monad option_isMonad.

  Notation "m >>= f" := (monad_bind (C:=Sets) f m) (at level 57, left associativity).
  Notation "x <- m ; p" := (m >>= fun x => p) (at level 60, right associativity).
  Eval compute in (x <- monad_emb (Monad:=option_Monad) 1;
                   monad_emb (Monad:=option_Monad) (x + 1)).
  Compute (x <- monad_emb (C:=Sets)(Monad:=option_Monad) 1; monad_emb (Monad:=option_Monad)x).
  Eval compute in x <- Some 1; monad_emb (C:=Sets) (x + 1).
  Compute (monad_bind option_Monad (fun x => Some (x + 1)) (monad_emb option_Monad 1)).
  Check (monad_bind option_Monad (fun x => Some (x + 1)) (monad_emb option_Monad 1)).
  Compute x <- Some 1; monad_emb option_Monad (x + 1).
  Eval compute in monad_emb option_Monad 1 >>= (fun x => Some (x + 1)).

  
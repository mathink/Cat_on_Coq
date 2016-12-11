Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main
        COC.Cons.Main
        COC.Adj.Main
        COC.Monad.Main.


Class IsKt (C: Category)(T: C -> C)
      (ret: forall (X: C), C X (T X))
      (bind: forall {X Y: C}, (C X (T Y)) -> (C (T X) (T Y))) :=
  {
    kt_bind_proper:> forall (X Y: C), Proper ((==) ==> (==)) (@bind X Y);
    kt_ret_bind:
      forall (X: C), bind (ret X) == Id (T X);

    kt_bind_ret:
      forall (X Y: C)(f: C X (T Y)),
        bind f \o ret X == f;

    kt_bind_comp:
      forall (X Y Z: C)(f: C X (T Y))(g: C Y (T Z)),
        bind g \o bind f == bind (bind g \o f)
  }.

Class Kt (C: Category)(T: C -> C) :=
  {
    ret: forall {X: C}, C X (T X);
    bind: forall (X Y: C), C X (T Y) -> C (T X) (T Y);

    kt_prf:> IsKt (@ret) bind
  }.
Existing Instance kt_prf.
Notation "[ 'Kt' 'by' ret , bind ]" := (@Build_Kt _ _ ret bind _).

Definition kt_fobj {C: Category}{T: C -> C}(kt: Kt C T) := T.

Program Definition Kt_from_Monad (C: Category)(T: Monad C)
  : Kt C T :=
  [Kt by monad_unit T,
         fun (X Y: C)(f: C X (T Y)) =>
           monad_mult T Y \o fmap T f].
Next Obligation.
  - now intros f g Heq; rewrite Heq.
  - generalize (monad_mult_T_unit (IsMonad:=T) X); simpl.
    now rewrite fmap_id, cat_comp_id_dom.
  - rewrite cat_comp_assoc.
    rewrite <- (natrans_naturality (IsNatrans:=monad_unit T) f); simpl.
    generalize (monad_mult_unit_T (IsMonad:=T) Y); simpl.
    rewrite cat_comp_id_dom, <- cat_comp_assoc; intros H; rewrite H.
    now rewrite cat_comp_id_cod.
  - generalize (monad_mult_mult (IsMonad:=T) Z); simpl; intros Heq.
    rewrite !fmap_comp, <- !cat_comp_assoc.
    rewrite cat_comp_id_dom in Heq; rewrite <- Heq, !cat_comp_assoc.
    rewrite <- (cat_comp_assoc (fmap T f)).
    rewrite <- (natrans_naturality (IsNatrans:=monad_mult T) g).
    now rewrite cat_comp_assoc.
Qed.

Program Definition Monad_from_Kt (C: Category)(T: C -> C)(kt: Kt C T) :=
  [Monad by [Functor by f :-> bind (ret \o f) with X :-> T X],
            [X :=> ret],
            [X :=> bind (Id (T X))]].
Next Obligation.
  - now intros f g Heq; rewrite Heq.
  - now rewrite kt_bind_comp, <- !cat_comp_assoc, kt_bind_ret.
  - now rewrite cat_comp_id_dom, kt_ret_bind.
Qed.
Next Obligation.
  now rewrite kt_bind_ret.
Qed.
Next Obligation.
  rewrite kt_bind_comp.
  rewrite <- cat_comp_assoc, kt_bind_ret, cat_comp_id_cod.
  now rewrite kt_bind_comp, cat_comp_id_dom.
Qed.
Next Obligation.
  - rewrite kt_bind_comp, !cat_comp_id_dom.
    rewrite kt_bind_comp.
    now rewrite <- cat_comp_assoc, kt_bind_ret, cat_comp_id_cod.
  - now rewrite cat_comp_id_dom, kt_bind_ret.
  - rewrite kt_bind_comp, cat_comp_id_dom.
    rewrite kt_bind_ret, kt_bind_comp.
    now rewrite <- cat_comp_assoc, kt_bind_ret, cat_comp_id_cod, kt_ret_bind.
Qed.

(** Equality **)
Program Definition Monad_setoid (C: Category) :=
  [Setoid by (fun (M N: Monad C) =>
                (monad_functor M == monad_functor N)
                /\(forall X: C, monad_unit M X =H monad_unit N X)
                /\(forall X: C, monad_mult M X =H monad_mult N X))].
Next Obligation.
  - intros M N [H [H' H'']]; repeat split; intros.
    + now apply hom_eq_sym, H.
    + now apply hom_eq_sym, H'.
    + now apply hom_eq_sym, H''.
  - intros M N L [Hmn [Hmn' Hmn'']] [Hnl [Hnl' Hnl'']]; repeat split; intros.
    + now apply hom_eq_trans with _ _ (fmap N f).
    + now apply hom_eq_trans with _ _ (monad_unit N X).
    + now apply hom_eq_trans with _ _ (monad_mult N X);
        [apply Hmn'' | apply Hnl''].
Qed.

Program Definition Kt_setoid (C: Category)(T: C -> C) :=
  [Setoid by (fun (k k': Kt C T) =>
                (forall X: C, ret (Kt:=k)(X:=X) == ret (Kt:=k'))
                /\(forall (X Y: C)(f: C X (T Y)),
                      bind (Kt:=k) f == bind (Kt:=k') f))].
Next Obligation.
  intros k k' k'' [Hr Hb] [Hr' Hb']; split; intros.
  - now transitivity (ret (Kt:=k')(X:=X)).
  - now transitivity (bind (Kt:=k') f).
Qed.

Lemma Monad_Kt_Monad_eq:
  forall (C: Category)(T: Monad C),
    T == Monad_from_Kt (Kt_from_Monad T) in Monad_setoid C.
Proof.
  intros; repeat split; simpl; try reflexivity.
  - rewrite fmap_comp, <- cat_comp_assoc.
    generalize (monad_mult_T_unit (IsMonad:=T) Y); simpl.
    rewrite fmap_id, cat_comp_id_dom.
    now intros Heq; rewrite Heq, cat_comp_id_cod.
  - now rewrite fmap_id, cat_comp_id_dom.
Qed.

Lemma Kt_Monad_Kt_eq:
  forall (C: Category)(T: C -> C)(kt: Kt C T),
    kt == Kt_from_Monad (Monad_from_Kt kt) in Kt_setoid C T.
Proof.
  simpl; intros; split; intros; [reflexivity |].
  now rewrite kt_bind_comp, <- cat_comp_assoc, kt_bind_ret, cat_comp_id_cod.
Qed.


(** Special Notation for Kt on Types **)
Notation "m >>= f" := (bind (C:=Types) f m) (at level 53, left associativity).
Notation "[ 'do' M 'in' K ]" := (let _kt := K: Kt Types _ in M). 
Notation "[ 'do' M ]" := [do M in _].
Notation "x <- m ; p" := (m >>= (fun x => p)) (at level 60, right associativity).
Notation ":- x ; m" := (_ <- x ; m) (at level 61, right associativity, x at next level).
Notation "x <-: m ; p" := (x <- ret m ; p) (at level 60, right associativity).
Notation "f >> g" := (bind (C:=Types) g \o f) (at level 42, right associativity).


Require Import List.
Import List.ListNotations.
(** Maybe **)
Program Instance Maybe: Kt Types option :=
  {
    ret X x := Some x;
    bind X Y f m := match m with
                    | Some x => f x
                    | None => None
                    end
  }.
Next Obligation.
  - now intros f g Heq [x |].
  - now destruct x as [x |].
  - now destruct x as [x |].
Qed.

Eval compute in
    [do x <-: 0;
       y <-: hd_error [1;2];
       ret (x, y) in Maybe].
(* = Some (0, Some 1) *)
(* : option (product nat (option nat)) *)

(** List **)
Lemma flat_map_app:
  forall (X Y: Type)(f: X -> list Y)(l1 l2: list X),
    flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  induction l1 as [| x l1 IHl1]; simpl; [reflexivity |].
  now intros l2; rewrite IHl1, app_assoc.
Qed.

Program Instance List: Kt Types list :=
  {
    ret X x := [x];
    bind X Y f l := flat_map f l
  }.
Next Obligation.
  - intros f g Heq l.
    now rewrite !flat_map_concat_map, (map_ext _ _ Heq).
  - now induction x as [| x l IHl]; simpl; [| rewrite IHl].
  - now rewrite app_nil_r.
  - induction x as [| x l IHl]; simpl; [reflexivity |].
    now rewrite flat_map_app, IHl.
Qed.

Definition guard {X: Type}(b: X -> bool)(x: X): list X :=
  if b x then [x] else [].

Fixpoint evenb (n: nat): bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Eval compute in
    [do x <- [0;1;2;3] ;
       :-guard evenb x ;
       z <-: S x;
       ret z in List].

(* = [1; 3] *)
(* : list nat *)

(** State **)
Module DirectDefinitionOfState.
  Require Import FunctionalExtensionality.
  Definition state (S: Type) := (fun (A: Type) => S -> product A S).
  Program Instance State (S: Type): Kt Types (state S) :=
    {
      ret X x s := (x, s);
      bind X Y f m s := let (x, s') := m s in f x s'
    }.
  Next Obligation.
    - intros f g Heq m.
      extensionality s.
      destruct (m s) as [x s'].
      now rewrite (Heq x).
    - extensionality s.
      now destruct (x s) as [x' s'].
    - extensionality s.
      now destruct (x s) as [x' s'].
  Qed.

  Definition put {S: Type}(s: S): state S unit :=
    (fun _: S => (tt, s)).

  Definition get {S: Type}: state S S :=
    (fun s: S => (s, s)).

  Definition modify {S: Type}(f: S -> S): state S unit :=
    [do s <- get ; put (f s) in State S].

  Definition evalState {S: Type}(X: Type)(m: state S X)(s: S) := m s.

  Eval compute in
      [do x <-: 0;
         y <-: 1;
         ret (x, y) in State nat].
  (* let _kt := State nat in x <-: 0; y <-: 1; ret (x, y) *)
  (*      : state nat (product nat nat) *)

  Eval compute in
      [do x <-: 0;
         y <-: 1;
         ret (x, y) in Maybe].
  (* = Some (0, 1) *)
  (* : option (product nat nat) *)

  Eval compute in
      [do x <-: 2;
         y <-: (evalState [do x <-: 1;
                             modify (plus x) in State nat]
                          x);
         ret (x, y.2) in Maybe].
  (* = Some (2, 3) *)
  (* : option (product nat nat) *)

  Eval compute in
      [do x <-: 2;
         y <-: (evalState [do x <-: 1;
                             modify (plus x) in State nat]
                          x);
         ret (x, y.2) in State bool].
  (* = fun s : bool => ((2, 3), s) *)
  (* : state bool (product nat nat) *)
End DirectDefinitionOfState.

Module StateFromAdjunction.
  Require Import FunctionalExtensionality.

  Program Definition exponential_of_Types (Y Z: Type)
  : Exponential (C:=Types) product_of_Types Y Z :=
  [Exp (Y -> Z)
    by (fun (X: Type) f x y => f (x, y))
   with (fun gy => gy.1 gy.2)].
  Next Obligation.
    - now destruct x.
    - now extensionality y; rewrite H.
  Qed.
  
  Program Instance State (S: Type): Kt Types _ :=
    Kt_from_Monad
      (Monad_from_adj
         (prod_exp_adjunction exponential_of_Types S)).

  Definition state (S: Type) := kt_fobj (State S).
  
  Definition put {S: Type}(s: S): state S unit :=
    (fun _: S => (tt, s)).

  Definition get {S: Type}: state S S :=
    (fun s: S => (s, s)).

  Definition modify {S: Type}(f: S -> S): state S unit :=
    [do s <- get ; put (f s) in State S].

  Definition evalState {S: Type}(X: Type)(m: state S X)(s: S) := m s.

  Eval compute in
      [do x <-: 0;
         y <-: 1;
         ret (x, y) in State nat].
  (* = fun y : nat => ((0, 1), y) *)
  (* : (Monad_from_adj (prod_exp_adjunction exponential_of_Types nat)) *)
  (*     (product nat nat) *)

  Eval compute in
      [do x <-: 0;
         y <-: 1;
         ret (x, y) in Maybe].
  (* = Some (0, 1) *)
  (* : option (product nat nat) *)

  Eval compute in
      [do x <-: 2;
         y <-: (evalState [do x <-: 1;
                             modify (plus x) in State nat]
                          x);
         ret (x, y.2) in Maybe].
  (* = Some (2, 3) *)
  (* : option (product nat nat) *)

  Eval compute in
      [do x <-: 2;
         y <-: (evalState [do x <-: 1;
                             modify (plus x) in State nat]
                          x);
         ret (x, y.2) in State bool].
  (* = fun y : bool => ((2, 3), y) *)
  (* : (Monad_from_adj (prod_exp_adjunction exponential_of_Types bool)) *)
  (*     (product nat nat) *)
End StateFromAdjunction.
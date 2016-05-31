Set Implicit Arguments.
Unset Strict Implicit.

Set Primitive Projections.
Set Universe Polymorphism.

Generalizable All Variables.

Require Import COC.Setoid COC.Category.

(** * 半順序 **)
Class PartialOrder {A: Type}(eq: relation A){equiv: Equivalence eq}(R: relation A) :=
  {
    PartialOrder_Reflexive: Reflexive R;
    PartialOrder_Transitive: Transitive R;
    PartialOrder_Antisymmetric: Antisymmetric A eq R
  }.
Existing Instance PartialOrder_Reflexive.
Existing Instance PartialOrder_Transitive.
Existing Instance PartialOrder_Antisymmetric.
Arguments PartialOrder A eq {equiv} R: clear implicits.

(** * 半順序集合 **)
Module Poset.
  Class spec (X: Setoid)(pord: relation X) :=
    proof {
        subst:> Proper ((==) ==> (==) ==> flip impl) pord;
        partialorder:> PartialOrder X (==:> X) pord
      }.

  Structure type :=
    make {
        setoid: Setoid;
        pord: relation setoid;

        prf: spec pord
      }.

  Notation build X pord :=
    (@make X pord (@proof _ _ _ _)).
  
  Module Ex.
    Notation isPoset := spec.
    Notation Poset := type.

    Coercion setoid: Poset >-> Setoid.
    Coercion prf: Poset >-> isPoset.

    Existing Instance subst.
    Existing Instance partialorder.
    Existing Instance prf.

    Delimit Scope poset_scope with poset.
    
    Notation "(<=p)" := (@pord _): poset_scope.
    Infix "<=p" := (pord ) (at level 80, no associativity): poset_scope.
  End Ex.

  Import Ex.

  Open Scope poset_scope.

  Lemma subst_l (P: Poset)(x y z: P):
    x == y -> x <=p z -> y <=p z.
  Proof.
    now intros Heq Hle; rewrite <- Heq.
  Qed.  

  Lemma subst_r (P: Poset)(x y z: P):
    y == z -> x <=p y -> x <=p z.
  Proof.
    now intros Heq Hle; rewrite <- Heq.
  Qed.
  
End Poset.  
Export Poset.Ex.


(** * 単調函数 **)
Module Monotone.
  Open Scope poset_scope.
  
  Class spec (P Q: Poset)(f: Map P Q) :=
    preserve:> Proper ((<=p) ==> (<=p)) f.

  Structure type (P Q: Poset) :=
    make {
        map: Map P Q;

        prf: spec P Q map
      }.

  Notation build map := (@make _ _ map _).

  Module Ex.
    Notation isMonotone := spec.
    Notation Monotone := type.

    Coercion map: Monotone >-> Map.
    Coercion prf: Monotone >-> isMonotone.
    
    Existing Instance preserve.
    Existing Instance prf.
  End Ex.

  Import Ex.
  
  Definition equal (P Q: Poset): relation (Monotone P Q) :=
    fun f g => f == g :> Map.setoid P Q.
  Arguments equal P Q f g /.

  Program Definition setoid (P Q: Poset) :=
    Setoid.build (@equal P Q).
  Next Obligation.
    intros f x; reflexivity.
  Qed.
  Next Obligation.
    now intros f g Heq x; symmetry; apply Heq.
  Qed.
  Next Obligation.
    now intros f g h H H' x; transitivity (g x); [apply H | apply H'].
  Qed.

  Program Definition compose {P Q R: Poset}(f: Monotone P Q)(g: Monotone Q R): Monotone P R :=
    Monotone.build (Map.compose f g).
  Next Obligation.
    intros p q H; simpl.
    now rewrite H.
  Qed.

  Program Definition id (P: Poset): Monotone P P :=
    Monotone.build (@Map.id P).
  Next Obligation.
    now intros p q H.
  Qed.
End Monotone.
Export Monotone.Ex.

Program Definition Posets: Category :=
  Category.build Monotone.setoid
                 (@Monotone.compose)
                 (@Monotone.id).
Next Obligation.
  intros f f' Heqf g g' Heqg; simpl in *; intros.
  now rewrite Heqf, Heqg.
Qed.
Next Obligation.
  simpl; intros; reflexivity.
Qed.
Next Obligation.
  simpl; intros; reflexivity.
Qed.
Next Obligation.
  simpl; intros; reflexivity.
Qed.

(** * Kleisli トリプル **)
Class Kleisli (C: Category)(T: C -> C) :=
  {
    pure: forall {X: C}, C X (T X);
    bind: forall {X Y: C}, C X (T Y) -> C (T X) (T Y);

    bind_pure:
      forall {X: C},
        bind (pure (X:=X)) == Id (T X);

    pure_bind:
      forall {X Y: C}(f: C X (T Y)),
        bind f \o pure == f;

    bind_bind:
      forall {X Y Z: C}(f: C X (T Y))(g: C Y (T Z)),
        bind g \o bind f == bind (bind g \o f)
  }.


Class KPL (C: Category)(T: C -> C)(K: Kleisli C T)(pred: C -> Posets) :=
  {
    sbst: forall {X Y: C}, C X (T Y) -> Posets (pred Y) (pred X);

    sbst_subst: forall (X Y: C), Proper ((==) ==> (==)) (@sbst X Y);

    sbst_comp:
      forall (X Y Z: C)(f: C X (T Y))(g: C Y (T Z)),
        sbst f \o sbst g == sbst (bind g \o f);

    sbst_id:
      forall (X: C),
        Id (pred X) == sbst (pure (X:=X))
  }.
Existing Instance sbst_subst.
Notation "f # P " := (sbst f P) (at level 45, right associativity).

Open Scope poset_scope.

Lemma hoare_id:
  forall `(kpl: @KPL C T K pr)(X: C)(P: pr X),
    P <=p pure#P.
Proof.
  intros.
  generalize (sbst_id (KPL:=kpl) (X:=X)); simpl; intro.
  apply (Poset.subst_r (H P)).
  reflexivity.
Qed.

Lemma hoare_comp:
  forall `(kpl: @KPL C T K pr)(X Y Z: C)(P: pr X)(Q: pr Y)(R: pr Z)
         (f: C X (T Y))(g: C Y (T Z)),
    P <=p f#Q ->
    Q <=p g#R ->
    P <=p (bind g \o f)#R.
Proof.
  intros.
  transitivity (f#Q); auto.
  transitivity (f # (g # R)).
  - now rewrite H0.
  - generalize (sbst_comp (KPL:=kpl) f g R); simpl; intro.
    now rewrite H1.
Qed.

Lemma hoare_trans_r:
  forall `(kpl: @KPL C T K pr)(X Y: C)(P: pr X)(Q R: pr Y)(f: C X (T Y)),
    P <=p f#Q -> Q <=p R -> P <=p f#R.
Proof.
  intros; apply transitivity with (f#Q); auto.
  now rewrite H0.
Qed.

(* TODO: 以降 *)
Program Definition function_setoid (X Y: Type) :=
  Setoid.build (fun (f g: X -> Y) => forall x, f x = g x).
Next Obligation.
  intros f g h Heqfg Heqgh x.
  now rewrite Heqfg; apply Heqgh.
Qed.

Program Definition Types: Category :=
  Category.build (function_setoid)
                 (fun X Y Z f g x => g (f x))
                 (fun X x => x).
Next Obligation.
  intros f f' Heqf g g' Heqg x; simpl.
  now rewrite Heqf, Heqg.
Qed.

Notation "m >>= f" := (bind (C:=Types) f m) (at level 53, left associativity).
Notation "x <- m ; p" := (m >>= fun x => p) (at level 60, right associativity).
Notation "x <-: m ; p" := (x <- pure m ; p ) (at level 60, right associativity).
Notation "f >> g" := (bind (C:=Types) g \o{Types} f) (at level 42, right associativity).

Module Pred.
  Definition type (X: Type) := X -> Prop.
  Definition pord {X: Type}(P Q: type X) := forall x, P x -> Q x.
  Arguments pord {X}(P Q) /.
  Definition impl {X: Type}(P Q: type X) := fun x => P x -> Q x.
  Arguments impl {X}(P Q) x /.
  Definition not {X: Type}(P: type X) := fun x => ~ P x.
  Arguments not {X}(P) x /.
  Definition and {X: Type}(P Q: type X) := fun x => P x /\ Q x.
  Arguments and {X}(P Q) x /.
  Definition or {X: Type}(P Q: type X) := fun x => P x \/ Q x.
  Arguments or {X}(P Q) x /.
  Definition True := fun {X: Type}(_: X) => True.
  Definition False := fun {X: Type}(_: X) => False.
End Pred.
Notation predicate := Pred.type.

Program Definition Pred_setoid (X: Type): Setoid :=
  Setoid.build (fun (P Q: predicate X) => forall x, P x <-> Q x).
Next Obligation.
  intros P x; tauto.
Qed.
Next Obligation.
  now intros P Q H; symmetry; auto.
Qed.
Next Obligation.
  now intros P Q R H H' x; transitivity (Q x); auto.
Qed.

Program Definition Pred_poset (X: Type): Poset :=
  Poset.build (Pred_setoid X) Pred.pord.
Next Obligation.
  intros P P' Hp Q Q' Hq Hpq x; simpl in *.
  now rewrite Hp, Hq; apply Hpq.
Qed.
Next Obligation.
  split.
  - now intros P; simpl; auto.
  - intros P Q R; simpl; intros Hpq Hqr x Hp.
    now apply Hqr, Hpq.
  - now intros P Q; simpl; intros Hpq Hqp x; split; revert x.
Qed.

(* Definition pred_kpl_format (T: Type -> Type)(kt: Kleisli Types T)(kpl: KPL kt Pred_poset)(X Y: Type)(P: predicate X)(Q: predicate Y)(f: X -> T Y) := *)
(*   Pred.pord P ((sbst (C:=Types)(KPL:=kpl)) f Q). *)
(* Notation "'for' ( x : A ) 'with' P ; 'result' y 'of' m 'in' KPL ; 'satisfies' Q" := (@pred_kpl_format _ _ KPL A _ (fun (x:A) => P) (fun y => Q) (fun x => m)) (at level 97, x at next level, format "'for'  ( x :  A )  'with'  P ; '//' 'result'  y  'of'  m  'in'  KPL ; '//' 'satisfies'  Q"). *)
(* Notation "'for' ( x : A ) 'with' P ; 'result' y 'of' m ; 'satisfies' Q" := (for (x : A) with P; result y of m in _; satisfies Q) (at level 97, x at next level, format "'for'  ( x :  A )  'with'  P ; '//' 'result'  y  'of'  m ; '//' 'satisfies'  Q"). *)
(* Notation "'for' x 'with' P ; 'result' y 'of' m 'in' KPL ; 'satisfies' Q" := (for (x : _) with P; result y of m in KPL; satisfies Q) (at level 97, format "'for'  x  'with'  P ; '//' 'result'  y  'of'  m  'in'  KPL ; '//' 'satisfies'  Q"). *)
(* Notation "'for' x 'with' P ; 'result' y 'of' m ; 'satisfies' Q" := (for x with P; result y of m in _; satisfies Q) (at level 97, format "'for'  x  'with'  P ; '//' 'result'  y  'of'  m ; '//' 'satisfies'  Q"). *)
Notation "'for' ( x : A ) 'with' P  ; 'result' y 'of' m 'in' KPL ; 'satisfies' Q" := (Pred.pord (fun (x:A) => P) (sbst (C:=Types)(KPL:=KPL) (fun x => m) (fun y => Q))) (at level 97, x at next level).
Notation "'for' ( x : A ) 'with' P  ; 'result' y 'of' m ; 'satisfies' Q" := (for (x : A) with P; result y of m in _; satisfies Q) (at level 97, x at next level).
Notation "'for' x 'with' P  ; 'result' y 'of' m 'in' KPL ; 'satisfies' Q" := (for (x : _) with P; result y of m in KPL; satisfies Q) (at level 97).
Notation "'for' x 'with' P  ; 'result' y 'of' m ; 'satisfies' Q" := (for x with P; result y of m in _; satisfies Q) (at level 97).


Instance Maybe: Kleisli Types option :=
  {
    pure X x := Some x;
    bind X Y f m := match m with Some x => f x | _ => None end
  }.
Proof.
  - simpl; intros X [x|]; auto.
  - simpl; intros X Y f x; auto.
  - simpl; intros X Y Z f g [x|]; auto.
Defined.


Program Instance MaybeKPL: KPL Maybe Pred_poset :=
  {
    sbst X Y f :=
      Monotone.build ([: P :-> fun x: X => match f x with
                                           | Some y => P y
                                           | _ => False
                                           end ])
  }.
Next Obligation.
  simpl; intros P Q H x.
  destruct (f x) as [y|]; auto.
  split; auto.
Qed.
Next Obligation.
  intros P Q; simpl; intros Hpq x.
  destruct (f x) as [y|]; [revert y |]; tauto.
Qed.
Next Obligation.
  intros f g H Q x; simpl.
  rewrite <- H.
  destruct (f x) as [y|]; tauto.
Qed.
Next Obligation.
  rename x into R, x0 into x.
  destruct (f x) as [y|]; tauto.
Qed.
Next Obligation.
  tauto.
Qed.


Lemma hcomp:
  forall {X Y Z: Type}(P: predicate X)(Q: predicate Y)(R: predicate Z)
         (f: X -> option Y)(g: Y -> option Z),
    (for x with P x; result y of f x in MaybeKPL; satisfies Q y) ->
    (for y with Q y; result z of g y in MaybeKPL; satisfies R z) ->
    (for x with P x; result z of y <- f x; g y in MaybeKPL; satisfies R z).
Proof.
  intros.
  apply (hoare_comp (kpl:=MaybeKPL)) with Q; assumption.
Qed.

Require Import Arith.
Fixpoint dif (n m: nat){struct m} :=
  match n, m with
  | S n', S m' => dif n' m'
  | _, 0 => Some n
  | 0, S _ => None
  end.

(* success *)
Goal
  forall n,
    for x with x = S n;
    result z of
           (y <-: (S x);
            dif y 2);
    satisfies z = n.
Proof.
  simpl; intros; subst.
  destruct n; ring.
Qed.


Lemma le_ind':
  forall (P : nat -> nat -> Prop),
    (forall n, P 0 n) ->
    (forall n m : nat, P n m -> P (S n) (S m)) ->
    forall n m : nat, le n m -> P n m.
Proof.
  intros.
  revert m H1; induction n.
  - intros; apply H.
  - destruct m.
    + intro H1; inversion H1.
    + intro Hle; apply H0, IHn, le_S_n; auto.
Qed.

Require Import Omega.
Goal
  for x with (2 <= x);
  result z of
         (mx <-: x * x;
          px <-: x + x;
          pure (px, mx));
  satisfies let (px,mx) := z in px <= mx.
Proof.
  simpl.
  intros.
  elim H; simpl; auto.
  intros.
  rewrite plus_comm; simpl.
  rewrite mult_comm; simpl.
  omega.
Qed.

Goal
  for nm with (let (n,m) := nm:nat*nat in n <= m);
  result z of (let (n,m) := nm:nat*nat in dif m n) in MaybeKPL;
  satisfies 0 <= z.
Proof.
  simpl; intros [n m] Hle; simpl in *.
  pattern n, m; apply le_ind'; auto; clear Hle n m.
  destruct n; simpl; auto with arith.
Qed.

(* main *)
Goal
    for x with 2 <= x;
    result z of
           (mx <-: x * x;
            px <-: x + x;
            dif mx px);
    satisfies 0 <= z.
Proof.
  change
    (for x with 2 <= x;
     result z of
            (mx <-: x * x;
             px <-: x + x;
             pm <-: (px,mx);     (* intermediate parameter *)
             let (p,m) := pm:_*_ in dif m p);
     satisfies 0 <= z).
  eapply (hoare_comp (kpl:=MaybeKPL)).
  - apply Unnamed_thm0.
  - apply Unnamed_thm1.
Qed.

(* failure *)
Goal
  forall P,
    ~ (for x with x = 0;
       result _ of y <-: (S x); dif y 2;
       satisfies P).
Proof.
  simpl; intros P H; generalize (H _ (eq_refl _)); simpl; auto.
Qed.

Require Import List.
Import List.ListNotations.

Instance ListKt: Kleisli Types list :=
  {
    pure X x := x::[];
    bind X Y f l := flat_map f l
  }.
Proof.
  - simpl; intros X l; induction l as [| x xs]; auto.
    now simpl; rewrite IHxs.
  - simpl; intros X Y f l.
    now rewrite app_nil_r.
  - simpl; intros.
    induction x as [| x xs]; auto.
    simpl.
    rewrite !flat_map_concat_map.
    rewrite map_app, concat_app.
    rewrite <- !flat_map_concat_map.
    now rewrite IHxs.
Defined.


Lemma Exists_app:
  forall (X: Type)(l1 l2: list X)(P: predicate X),
    Exists P (l1 ++ l2) <-> (Exists P l1 \/ Exists P l2).
Proof.
  induction l1 as [| x l1]; simpl; intros.
  - split; [intros H; right | intros [H | H] ]; auto.
    now inversion H.
  - now rewrite !Exists_cons, IHl1, or_assoc.
Qed.

Lemma or_False_r:
  forall (P: Prop), (P \/ False) <-> P.
Proof.
  intros P; split; tauto.
Qed.

Program Instance ListExKPL: KPL ListKt Pred_poset :=
  {
    sbst X Y f :=
      Monotone.build ([: P :-> fun x => Exists P (f x)])
  }.
Next Obligation.
  intros P Q Heq x.
  induction (f x) as [| y ys]; simpl.
  - split; intros H; inversion H.
  - now rewrite !Exists_cons, IHys, (Heq y).
Qed.
Next Obligation.
  intros P Q Hord x; simpl.
  induction (f x) as [| y ys]; simpl.
  - intros H; inversion H.
  - now rewrite !Exists_cons; intros [Hy | Hys];
      [left; apply Hord | right; apply IHys].
Qed.
Next Obligation.
  intros f g Heq Q x; simpl.
  now rewrite Heq.
Qed.
Next Obligation.
  rename x into R, x0 into x.
  induction (f x) as [| y ys]; simpl.
  - split; intros H; inversion H.
  - now rewrite Exists_cons, Exists_app, IHys.
Qed.
Next Obligation.
  now rewrite Exists_cons, Exists_nil, or_False_r.
Qed.

Lemma Forall_cons':
  forall (X: Type)(P: predicate X)(x: X)(xs: list X),
    Forall P (x::xs) <-> (P x /\ Forall P xs).
Proof.
  intros; split.
  - intros H; inversion H; subst.
    now split.
  - now intros [Hx Hxs]; apply Forall_cons.
Qed.

Lemma Forall_app:
  forall (X: Type)(l1 l2: list X)(P: predicate X),
    Forall P (l1 ++ l2) <-> (Forall P l1 /\ Forall P l2).
Proof.
  induction l1 as [| x l1]; simpl; intros.
  - now split; [intros H; split | intros [_ H]].
  - now rewrite !Forall_cons', IHl1, and_assoc.
Qed.

Program Instance ListFaKPL: KPL ListKt Pred_poset :=
  {
    sbst X Y f :=
      Monotone.build ([: P :-> fun x => Forall P (f x)])
  }.
Next Obligation.
  intros P Q Heq x.
  induction (f x) as [| y ys]; simpl.
  - now split.
  - now rewrite !Forall_cons', IHys, (Heq y).
Qed.
Next Obligation.
  intros P Q Hord x; simpl.
  induction (f x) as [| y ys]; simpl.
  - now auto.
  - now rewrite !Forall_cons'; intros [Hy Hys]; split;
      [apply Hord | apply IHys].
Qed.
Next Obligation.
  intros f g Heq Q x; simpl.
  now rewrite Heq.
Qed.
Next Obligation.
  rename x into R, x0 into x.
  induction (f x) as [| y ys]; simpl.
  - now split.
  - now rewrite Forall_app, Forall_cons', IHys.
Qed.
Next Obligation.
  split; rewrite Forall_cons'; auto.
  now intros [H _].
Qed.


(** ** List モナドの例 **)

(* 相互再帰はめんどい *)
(* Inductive even: nat -> Prop := *)
(* | even_0: even 0 *)
(* | even_odd: forall n, odd n -> even (S n) *)
(* with *)
(* odd: nat -> Prop := *)
(* | odd_1: odd 1 *)
(* | odd_even: forall n, even n -> odd (S n). *)
(* Hint Resolve even_0 odd_1 even_odd odd_even. *)

Inductive even: nat -> Prop :=
| even_0: even 0
| even_SSn: forall n, even n -> even (S (S n)).
Hint Resolve even_0 even_SSn.

Lemma even_n2:
  forall n, even (n * 2).
Proof.
  induction n as [| n]; auto.
  rewrite Nat.mul_succ_l, plus_comm; simpl; auto.
Qed.

Lemma even_add_even:
  forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m Heven; revert m; induction Heven; auto.
  intros; simpl.
  now apply even_SSn, IHHeven.
Qed.

Lemma even_mul_even:
  forall n m, even n -> even (n * m).
Proof.
  intros n m Heven; revert m; induction Heven; simpl; auto.
  intros m.
  rewrite plus_assoc.
  apply even_add_even.
  - replace (m + m) with (2 * m).
    + now rewrite mult_comm; apply even_n2.
    + now simpl; rewrite plus_0_r.
  - apply IHHeven.
Qed.

Goal
  for l with (l = [2;3;5;7;9]);
  result x of l in ListExKPL;
  satisfies (even x).
Proof.
  simpl; intros; subst.
  now rewrite Exists_cons; left; auto.
Qed.

Goal
  forall nl: list nat,
    for l with (l = nl);
      result x of (n <- l; pure (n * 2)) in ListFaKPL;
      satisfies (even x).
Proof.
  simpl; intros; subst.
  induction nl as [| n nl]; simpl; auto.
  rewrite Forall_cons'; split; auto.
  apply even_n2.
Qed.


Goal
  for (_:unit) with True;
  result x of (n <- [1;3;5;7];
                 m <- [2;4;6;8];
                 pure (n * m)) in ListFaKPL;
  satisfies (even x).
Proof.
  simpl; intros.
  rewrite !Forall_cons'; repeat split; auto;
    (repeat apply even_SSn; auto).
Qed.



(* State Monad *)
Module PType.
  Record type := make { carrier: Type; point: carrier }.
End PType.
Notation PType := PType.type.
Coercion PType.carrier : PType >-> Sortclass.

Module SPred.
  Definition type (S: PType)(X: Type) := S -> X -> Prop.
  Definition pord {S: PType}{X: Type}(P Q: type S X) := forall s x, P s x -> Q s x.
  Arguments pord {S X}(P Q) /.
  Definition impl {S: PType}{X: Type}(P Q: type S X) := fun s x => P s x -> Q s x.
  Arguments impl {S X}(P Q) s x /.
  Definition not {S: PType}{X: Type}(P: type S X) := fun s x => ~ P s x.
  Arguments not {S X}(P) s x /.
  Definition and {S: PType}{X: Type}(P Q: type S X) := fun s x => P s x /\ Q s x.
  Arguments and {S X}(P Q) s x /.
  Definition or {S: PType}{X: Type}(P Q: type S X) := fun s x => P s x \/ Q s x.
  Arguments or {S X}(P Q) s x /.
  Definition True := fun {S: PType}{X: Type}(_: S)(_: X) => True.
  Definition False := fun {S: PType}{X: Type}(_: S)(_: X) => False.
End SPred.
Notation spredicate := SPred.type.

Program Definition SPred_setoid (S: PType)(X: Type): Setoid :=
  Setoid.build (fun P Q: spredicate S X =>
                  forall s x, P s x <-> Q s x).
Next Obligation.
  intros P s x; tauto.
Qed.
Next Obligation.
  now intros P Q H; symmetry; auto.
Qed.
Next Obligation.
  now intros P Q R H H' s x; transitivity (Q s x); auto.
Qed.

Program Definition SPred_poset (S: PType)(X: Type): Poset :=
  Poset.build (SPred_setoid S X) SPred.pord.
Next Obligation.
  intros P P' Hp Q Q' Hq Hpq s x.
  now rewrite Hp, Hq; apply Hpq.
Qed.
Next Obligation.
  split; simpl.
  - now intros P; simpl; auto.
  - intros P Q R; simpl; intros Hpq Hqr s x Hp.
    now apply Hqr, Hpq.
  - now intros P Q; simpl; intros Hpq Hqp s x; split; revert s x.
Qed.

Definition state (S: PType)(X: Type) := S -> (X * S)%type.

(* Instance State (S: PType): Kleisli (C:=Setoids) (state S) := *)
Axiom ext_eq: forall (A B: Type)(f g: A -> B),
    (forall x, f x = g x) -> f = g.
Instance State (S: PType): Kleisli Types (state S) :=
  {
    pure X x := fun s => (x,s);
    bind X Y f m := fun s => let (y,s') := m s in f y s'
  }.
Proof.
  - simpl; intros X x.
    apply ext_eq; intros s.
    destruct (x s); reflexivity.
  - simpl; intros X Y f x; auto.
  - simpl; intros X Y Z f g x; auto.
    apply ext_eq; intros s.
    destruct (x s); reflexivity.
Defined.
Definition get {S: PType}: state S S := fun s => (s,s).
Definition put {S: PType}(s': S): state S unit := fun s => (tt,s').
Definition modify {S: PType}(f: PType.carrier S -> PType.carrier S): state S unit
  := s <- get; put (f s).


Program Definition StateKPLMap (S: PType){X Y: Type}(f: X -> state S Y)
  : Map (SPred_setoid S Y) (SPred_setoid S X) :=
  [ P :-> fun s x => let (y,s') := f x s in P s' y ].
Next Obligation.
  intros P Q Heq s x.
  destruct (f x s); apply Heq.
Qed.

Program Instance StateKPL (S: PType): KPL (State S) (SPred_poset S) :=
  {
    sbst X Y f := Monotone.build (StateKPLMap f)
  }.
Next Obligation.
  intros P Q; simpl; intros Hpq s x.
  destruct (f x s); apply Hpq.
Qed.
Next Obligation.
  intros f g H Q s x; simpl.
  rewrite <- H.
  destruct (f x s); reflexivity.
Qed.
Next Obligation.
  rename x into R, x0 into x.
  destruct (f x s); reflexivity.
Qed.
Next Obligation.
  tauto.
Qed.

(* Notation "[ x <~ m 'and' s ; P ]" := (m # (fun s x => P)). *)
(* Definition spred_kpl_template (S: PType)(X Y: Type)(P: spredicate S X)(Q: spredicate S Y)(f: X -> state S Y) := *)
(*   (SPred.pord P (sbst (C:=Types)(KPL:=StateKPL S) f Q)). *)
Notation "'from' s 'in' S ; 'for' ( x : A ) 'with' P ; 'result' y 'of' m ; 'into' t ; 'satisfies' Q" :=
  (* (spred_kpl_template (fun (s: S)(x: A) => P) (fun t (y: _) => Q) (fun (x: A) => m)) *)
  (SPred.pord (fun (s:S)(x:A) => P) (sbst (C:=Types)(KPL:=StateKPL _) (fun x => m) (fun (t: S) y => Q)))
  (at level 97, x at next level, format "'[' 'from'  s  'in'  S ; ']' '/' '[' 'for'  ( x :  A )  'with'  P ; ']' '/' '[' 'result'  y  'of'  m ; ']' '/' '[' 'into'  t ; ']' '/' '[' 'satisfies'  Q ']'").
Notation "'from' s 'in' S ; 'for' x 'with' P ; 'result' y 'of' m ; 'into' t ; 'satisfies' Q" := (from s in S; for (x:_) with P; result y of m; into t; satisfies Q) (at level 97, format "'[' 'from'  s  'in'  S ; ']' '/' '[' 'for'  x  'with'  P ; ']' '/' '[' 'result'  y  'of'  m ; ']' '/' '[' 'into'  t ; ']' '/' '[' 'satisfies'  Q ']'").

Definition Pnat := PType.make 0.
Goal
  from s in Pnat;
  for x with (2 <= x);
  result z of
         (mx <-: x * x;
            px <-: x + x;
            pure (mx, px));
  into s';
  satisfies (let (mx,px) := z: nat*nat in px <= mx).
Proof.
  intros s x H; simpl.
  elim H; simpl; auto.
  intros.
  rewrite plus_comm, mult_comm; simpl.
  omega.
Qed.

Goal
  from s in Pnat;
  for (x: nat) with (1 <= s);
  result z of pure x;
  into s';
  satisfies (1 <= s').
Proof.
  intros s x H.
  simpl; auto.
Qed.


(** Monadic List **)
Definition consS (X: Types)(x: X)(l: list X) :=
  _ <- modify (S:=Pnat) S; pure (cons x l).

Goal
  forall (X: Types)(x: X)(n: nat),
    (from s in Pnat;
       for l with (s = n);
       result l' of consS x l;
       into s';
       satisfies (s' = S n)).
Proof.
  now simpl; intros; subst.
Save consS_length.



(* カウント付き比較 *)
Definition leb_c (n m: nat) := _ <- modify (S:=Pnat) S; pure (n <=? m).
(* Fixpoint leb_c (n m: nat): state Pnat bool := *)
(*   match n, m with *)
(*   | O, O *)
(*   | O, S _ => _ <- modify (S:=Pnat) S; *)
(*                 pure true *)
(*   | S _, O => _ <- modify (S:=Pnat) S; *)
(*                 pure false *)
(*   | S p, S q => leb_c p q *)
(*   end. *)

(* 比較すれば比較回数は真に大きくなるよ *)
Fixpoint insert (n: nat)(l: list nat){struct l}: state Pnat (list nat)  :=
  match l with
  | [] => pure (cons n nil)
  | m::xs => b <- leb_c n m;
               (if b:bool  
                then pure (n::m::xs)
                else (res <- insert n xs;
                        pure (m::res)))
  end.

Fixpoint insertion_sort (l: list nat): state Pnat (list nat) :=
  match l with
  | [] => pure []
  | n::xs => res <- insertion_sort xs
             ; insert n res
  end.

Eval compute in insertion_sort [3;1;4;1;5;9;6] 0.
     (* = ([1; 1; 3; 4; 5; 6; 9], 9) *)
     (* : list nat * Pnat *)


(* 大雑把な評価 *)
Lemma insertion_sort_compare_count_max_gen:
  forall c,
    from s in Pnat;                 (* 状態 s から始めて *)
    for (l: list nat) with (s = c); (* 値 l と条件 s = c について *)
    result l' of insertion_sort l;  (* insertion_sort l を計算した結果 l' が *)
    into s';                        (* 状態 s' に至ったとすると *)
    satisfies (s' <= c + length l' * length l'). (* これらは s' <= c + length l' * length l' を満たす *)
Proof.
  simpl; intros c s l H.
  induction l as [| n l]; simpl; auto.
  - now rewrite plus_0_r; subst.
  - simpl in IHl.
    generalize (conj H IHl).
    clear H IHl.
    revert s l.
    eapply (hoare_comp (kpl:=StateKPL Pnat)).
    + simpl; intros s l [Heq Hle]; subst.
      generalize (eq_refl (length l)); intro H.
      apply (conj H Hle).
    + simpl.
      intros s l.
      revert c n s.
      induction l as [| m l]; simpl; auto.
      * intros; omega.
      * intros c n s; generalize tt; revert s.
        change (
            from s in Pnat;
            for (_:unit) with (s <= c + S (length l + length l * S (length l)));
            result l' of (
                     _ <- modify (S:=Pnat) S;
                     if n <=? m
                     then pure (X:=list nat:Types)(n::m::l)
                     else l' <- insert n l; pure (X:=list nat:Types)(m::l'));
            into s';
            satisfies (s' <= c + length l' * length l')
          ).
        eapply (hoare_comp (kpl:=StateKPL Pnat)).
        Focus 2.
        simpl; intros.
        destruct (n <=? m).
        Focus 2.
        generalize (IHl (S c + length (fst (insert n l s)) + length (fst (insert n l s))) n s H).
        destruct (insert n l s); simpl.
        simpl.
        rewrite <- mult_n_Sm, (plus_comm (_*_)).
        rewrite !plus_n_Sm.
        now rewrite !plus_assoc.
Admitted.

Lemma insertion_sort_compare_count_max:
  from s in Pnat;
  for (l: list nat) with (s = 0);
  result l' of insertion_sort l;
  into s';
  satisfies (s' <= length l' * length l').
Proof.
  apply insertion_sort_compare_count_max_gen.
Qed.

(* 一筋縄じゃいかねぇ *)

Inductive le': nat -> nat -> Prop :=
| le'_0_n: forall n, le' 0 n
| le'_n_S: forall n m, le' n m -> le' (S n) (S m).
Hint Resolve le'_0_n le'_n_S.

Lemma le_0_n:
  forall n, le 0 n.
Proof.
  induction n; auto.
Qed.

Lemma le'_n:
  forall n, le' n n.
Proof.
  induction n as [| n]; auto.
Qed.

Lemma le'_S:
  forall n m, le' n m -> le' n (S m).
Proof.
  intros n m Hle'; induction Hle'; auto.
Qed.

Theorem le_le':
  forall n m, le n m <-> le' n m.
Proof.
  intros; split.
  {
    intros Hle; induction Hle.
    - now apply le'_n.
    - now apply le'_S.
  }
  {
    intros Hle; induction Hle.
    - now apply le_0_n.
    - now apply le_n_S.
  }
Qed.

Goal
  forall P n m,
    from s in Pnat;
    for (_:unit) with (n <= m/\P (S s));
    result b of (leb_c n m);
    into s';
    satisfies (b = true/\P s').
Proof.
  simpl; intros P n m s ? [Hle Hp].
  rewrite le_le' in Hle.
  induction Hle; simpl; auto.
Qed.

Goal
  forall P n m,
    from s in Pnat;
    for (_:unit) with (n > m/\P (S s));
    result b of (leb_c n m);
    into s';
    satisfies (b = false/\P s').
Proof.
  simpl; intros P n m s _ [Hle Hp].
  unfold gt, lt in Hle.
  revert m Hle s Hp; induction n as [| n]; simpl.
  - intros; inversion Hle.
  - destruct m; auto; intros.
    apply le_S_n in Hle.
    apply IHn; auto .
Qed.

(* 大雑把な評価 *)
Goal
  forall c,
    from s in Pnat;                 (* 状態 s から始めて *)
    for (l: list nat) with (s = c); (* 値 l と条件 s = c について *)
    result l' of insertion_sort l;  (* insertion_sort l を計算した結果 l' が *)
    into s';                        (* 状態 s' に至ったとすると *)
    satisfies (s' <= c + length l' * length l'). (* これらは s' <= c + length l' * length l' を満たす *)
Proof.
  simpl; intros.
  induction x as [| n l]; simpl; auto.
  - subst; omega.
  - generalize tt (conj H IHl).
    clear H IHl.
    revert s.
    eapply (hoare_comp (kpl:=StateKPL Pnat)).
    + simpl; intros s _ [Heq Hle].
      apply Hle.
    + Goal
        forall n c,
          (from s in Pnat;
           for l with (s <= c + length l * length l);
           result l' of insert n l;
           into s';
           satisfies (s' <= c + length l' * length l')).
      Proof.
        simpl.
        intros.
        induction x as [| m l]; auto.
        - simpl in *; omega.
        - simpl.
          revert c l H IHl.
          functional induction (leb_c n m).
          + intros; simpl in *.
            rewrite !mult_succ_r in *.
            omega.
          + intros; simpl in *.
            rewrite !mult_succ_r in *.
            omega.
          + intros; simpl in *.
            
            
            (*  *)
          destruct (le_gt_dec n m) as [Hle | Hgt].
          + generalize tt (conj H IHl).
            clear H IHl.
            revert s.
            eapply (hoare_comp (kpl:=StateKPL Pnat)).
            * simpl; intros.
              apply Unnamed_thm9 with
              (P := fun s => match s with
                             | O => True
                             | S s =>
                               s <= c + S (length l + length l * S (length l)) /\
                               (s <= c + length l * length l ->
                                let (y, s') := insert n l s in s' <= c + length y * length y)
                             end); auto.
            (* TODO *)
            * simpl; intros; subst.
              destruct H; subst.
              destruct s; auto with arith.
              simpl.
              destruct H0.
              admit.
          +
            Focus 2.
            simpl; intros.
          + simpl; intros s _ [H H'].
            Focus 2.
      Admitted.
      apply Unnamed_thm10.
Goal
  from s in Pnat;
  for (l: list nat) with (s = 0);
  result l' of insertion_sort l;
  into s';
  satisfies (s' <= length l' * length l').
Proof.
  apply Unnamed_thm9.
Qed.

(* 一筋縄じゃいかねぇ *)
Inductive sorted: list nat -> Prop :=
| sorted_nil: sorted []
| sorted_one: forall n, sorted [n]
| sorted_cons: forall n m l, n <= m -> sorted (m::l) -> sorted (n::m::l).
Hint Resolve sorted_nil sorted_one sorted_cons.


Lemma sorted_cons_inv:
  forall n l, sorted (n::l) -> sorted l.
Proof.
  intros n l Hs.
  inversion Hs; subst; auto.
Qed.



Lemma sorted_cons_cons_inv:
  forall n m l, sorted (n::m::l) -> sorted (n::l).
Proof.
  intros n m l.
  revert n m; destruct l as [| k l]; auto.
  intros.
  inversion H; subst.
  inversion H4; subst.
  apply sorted_cons; auto.
  apply le_trans with m; auto.
Qed.  

Lemma sorted_cons_inv_in:
  forall n l, sorted (n::l) ->
              (forall x, In x l -> n <= x).
Proof.
  intros n l; revert n.
  induction l as [| m l].
  - contradiction.
  - simpl; intros n Hs x [Heq | HIn].
    + subst.
      now inversion Hs.
    + apply IHl; auto.
      apply sorted_cons_cons_inv with m; auto.
Qed.

Lemma sorted_in:
  forall n l, sorted l -> (forall x, In x l -> n <= x) -> sorted (n::l).
Proof.
  intros n l Hs; revert n; induction Hs; auto.
  - simpl.
    intros m H; apply sorted_cons; auto.
  - intros; apply sorted_cons; auto.
    apply H0; left; reflexivity.
Qed.

Goal
  forall n,
    from _ in Pnat;
    for l with (sorted l);
    result l' of (insert n l);
    into _;
    satisfies (sorted l').
Proof.
Admitted.

Goal
  from _ in Pnat;
  for (l: list nat) with True;
  result l' of insertion_sort l;
  into _;
  satisfies (sorted l').
Proof.
  simpl; intros.
  induction x as [| n l]; simpl; auto.
  revert IHl.
  generalize tt.
  revert s.
  eapply (hoare_comp (kpl:=StateKPL Pnat)).
  - simpl; intros.
    apply H0.
  - simpl.
    intros.
    apply Unnamed_thm13; auto.
Qed.

Goal
  forall P n m c,
    from s in Pnat;
    for (l:list nat) with (s <= c /\ P (S s) l);
    result bl of b <- leb_c n m; pure (b,l);
    into s';
    satisfies (let (b,l) := bl: bool * list nat in s' <= S c /\ P s' l).
Proof.
  intros P n m c s H; simpl.
  subst.
  revert m c.
  induction n as [| n]; simpl.
  - destruct m as [| m]; intros c [Hle Hp]; split; try omega; auto.
  - destruct m as [| m]; auto; intros c [Hle Hp].
    + split; try omega; auto.
    + apply IHn; split; auto.
Qed.

(* insert に於ける比較回数は高々リストの長さ分だよ *)
(* 長さに関する記述が足りない *)
Goal
  forall len n c,
    from s in Pnat;
    for l with (s <= c /\ length l = len);
    result l' of insert n l;
    into s';
    satisfies (s' <= c + length l' /\ length l' = S len).
Proof.
  intros len n c s l; simpl.
  revert len n c s.
  induction l as [| m xs].
  - intros len c n s [Hle Heq]; simpl in *.
    subst; split; omega.
  - simpl.
    intros len n c s [Hle Heq].
    revert len c s xs Hle Heq IHxs.
    functional induction (leb_c n m); simpl.
    + split.
      * rewrite <- plus_n_Sm.
        apply le_n_S.
        now apply le_plus_trans.
      * now apply eq_S.
    + split.
      * rewrite <- plus_n_Sm.
        apply le_n_S.
        now apply le_plus_trans.
      * now apply eq_S.
    + intros.
      generalize (IHxs (length xs) (S p) (S s) (S s) (conj (le_n _) (eq_refl _))).
      destruct (insert (S p) xs (S s)); simpl.
      intros [Hle' Heq'].
      subst.
      rewrite Heq'; split; omega.
    + intros.
      generalize (IHs len c s xs Hle Heq).
      destruct (leb_c p q s) as [[|] s']; intros.
      * simpl in *.
        apply H.
        apply IHxs.
      * simpl in *.
        admit.
Admitted.
    
Goal
  forall len c,
    from s in Pnat;
    for (l: list nat) with (s <= c /\ length l = len);
    result l' of insertion_sort l;
    into s';
    satisfies (s' <= c + length l' * length l' /\ length l' = len).
Proof.
  intros len c s l.
  revert len c s.
  induction l as [| n xs ]; simpl.
  - intros; simpl; split; omega.
  - intros len c s Hle; generalize s xs (conj Hle (IHxs (length xs) c s)).
    clear s xs IHxs Hle.
    eapply (hoare_comp (kpl:=StateKPL Pnat)).
    + simpl.
      intros s xs [Heq H].
      destruct Heq as [Hle Heq].
      generalize (H (conj Hle (eq_refl _))).
      destruct (insertion_sort xs s).
      intros H'.
      apply H'.
    + eapply (hoare_trans_r (kpl:=StateKPL Pnat)).
      eapply transitivity.
      Focus 2.
      apply (@Unnamed_thm12).
      
      * simpl in *.
        intros.
        split.
        
        intros H s xs Hle.
      generalize (H n (c + length xs * length xs) s xs).
      destruct (insert n xs s).
      apply H.
    + simpl; intros s' l H.
      generalize (IHxs c s' H).
      destruct (insertion_sort xs s').
      tauto.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Generalizable All Variables.

Set Primitive Projections.
Set Universe Polymorphism.

Require Import COC.Base.Main.

Require Import List.
Import List.ListNotations.

Definition _list := list.
Program Definition list: Types --> Types :=
  [Functor by f :-> map f].
Next Obligation.
  - intros f g Heq l.
    induction l as [| x l IHl]; simpl; auto.
    now rewrite IHl, Heq.
  - now rewrite map_map.
  - now rewrite map_id.
Qed.


Program Definition length_natrans: list ==> [* in Types |-> nat in Types] :=
  [X :=> @length X].
Next Obligation.
  now induction x as [| x l IHl]; simpl; [| rewrite IHl].
Qed.


Definition _option := option.
Program Definition option: Types --> Types :=
  [Functor by f :-> option_map f].
Next Obligation.
  - now intros f g Heq [x |]; simpl; [rewrite Heq |].
  - now destruct x as [x |]; simpl.
  - now destruct x as [x |]; simpl.
Qed.


Program Definition hd_error_natrans: list ==> option :=
  [X :=> @hd_error X].
Next Obligation.
  now induction x as [| x l IHl]; simpl.
Qed.


Inductive _tree (X: Type) :=
| leaf (x: X)
| node (tl tr: _tree X).

Fixpoint tree_map (X Y: Type)(f: X -> Y)(t: _tree X): _tree Y :=
  match t with
  | leaf x => leaf (f x)
  | node tl tr => node (tree_map f tl) (tree_map f tr)
  end.
Notation "[: x :]" := (leaf x).
Infix "-:-" := node (at level 50, left associativity).

Lemma tree_map_map:
  forall (X Y Z: Type)(f: X -> Y)(g: Y -> Z)(t: _tree X),
    tree_map (fun x => g (f x)) t = tree_map g (tree_map f t).
Proof.
  induction t as [x | tl IHl tr IHr]; simpl in *; auto.
  now rewrite IHl, IHr.
Qed.
Hint Resolve tree_map_map.

Lemma tree_map_id:
  forall (X: Type)(t: _tree X),
    tree_map (fun x: X => x) t = t.
Proof.
  induction t as [x | tl IHl tr IHr]; simpl in *; auto.
  now rewrite IHl, IHr.
Qed.
Hint Resolve tree_map_id.

Program Definition tree: Types --> Types :=
  [Functor by f :-> tree_map f with X :-> _tree X].
Next Obligation.
  intros f g Heq t.
  induction t as [x | tl IHl tr IHr]; simpl in *.
  - now rewrite Heq.
  - now rewrite IHl, IHr.
Qed.

Fixpoint tree_flatten (X: Type)(t: tree X): list X :=
  match t with
  | [:x:] => [x]
  | tl -:- tr => tree_flatten tl ++ tree_flatten tr
  end.


Program Definition tree_flatten_natrans: tree ==> list :=
  [X :=> tree_flatten (X:=X)].
Next Obligation.
  induction x as [x | tl IHl tr IHr]; simpl; auto.
  now rewrite IHl, IHr, map_app.
Qed.

Fixpoint list_equal (X: Setoid)(l1 l2: list X) :=
  match l1, l2 with
  | [], [] => True
  | x :: l1, y :: l2 => x == y /\ list_equal l1 l2
  | _, _ => False
  end.

Inductive list_equal_inductive (X: Setoid): list X -> list X -> Prop :=
| list_equal_nil: list_equal_inductive [] []
| list_equal_cons: forall (x y: X)(l1 l2: list X),
    x == y -> list_equal_inductive l1 l2 ->
    list_equal_inductive (x :: l1) (y :: l2).
Hint Resolve list_equal_nil list_equal_cons.

Lemma list_equal_equiv:
  forall (X: Setoid)(l1 l2: list X),
    list_equal l1 l2 <-> list_equal_inductive l1 l2.
Proof.
  intros; split.
  - revert l2; induction l1 as [| x l1 IH].
    + now intros [| y l2] H; try contradiction; auto.
    + intros [| y l2] H; try contradiction; simpl in *.
      apply list_equal_cons; [apply H |].
      now apply IH, H.
  - now intros H; induction H.
Qed.

Program Definition list_setoid (X: Setoid) :=
  [Setoid by @list_equal X].
Next Obligation.
  - now intros l; induction l as [| x l IHl].
  - intros l1 l2 Heq; apply list_equal_equiv in Heq.
    now induction Heq.
  - intros l1 l2 l3 Heq12; revert l3.
    apply list_equal_equiv in Heq12; induction Heq12; try now idtac.
    intros l3 Heq23; apply list_equal_equiv in Heq23; inversion Heq23.
    simpl; subst.
    split; [now transitivity y |].
    now apply IHHeq12, list_equal_equiv.
Qed.
Canonical Structure list_setoid.

Program Definition list_functor: Setoids --> Setoids :=
  [Functor by f :-> [Map by map f] with X :-> list_setoid X].
Next Obligation.
  intros l1 l2 Heq; apply list_equal_equiv in Heq; induction Heq; simpl; try now idtac.
  now rewrite H1.
Qed.
Next Obligation.
  - intros f g Heq l.
    now induction l as [| x l IHl].
  - rewrite map_map.
    now apply (Equivalence_Reflexive (Equivalence:=list_setoid_obligation_1 Z)).
  - rewrite map_id.
    now apply (Equivalence_Reflexive (Equivalence:=list_setoid_obligation_1 X)).
Qed.

Require Import Rep.Yoneda.
Program Definition test: Map (eq_setoid bool) (eq_setoid nat) := [ m :-> match m with true => 0 | false => 1 end].
Next Obligation.
  now intros [|] [|].
Qed.

Goal
  (forall (C: Category)(X: C)(F: C --> Setoids)(x: F X)(Y: C)(f: C X Y),
      inv_yoneda_map X F x Y f == fmap F f x
  ).
Proof.
  now intros; simpl.
Qed.


Eval compute in fmap list_functor test [true; false; false; true].
Eval compute in inv_yoneda_map (eq_setoid bool) list_functor [true; false; false; true] (eq_setoid nat) test.


Lemma leaf_eq_eq:
  forall (X: Type)(x y: X),
    [:x:] = [:y:] -> x = y.
Proof.
  intros.
  inversion H.
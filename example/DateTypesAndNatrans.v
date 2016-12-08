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

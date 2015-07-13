(* -*- mode: coq -*- *)
(* Time-stamp: <2015/7/13 15:50:20> *)
(*
  Setoid.v 
  - mathink : author
 *)

Set Implicit Arguments.
Unset Strict Implicit.

Set Universe Polymorphism.

Generalizable All Variables.

(** * Setoid & Map
まずは Setoid とその間の変換である Map の定義を行ないます。
 *)

(** 関数 f を Proper クラスのインスタンスとすることで、
[=] でなくとも rewrite が使えるようになります。
圏論を展開していく上では、様々な定理の証明に射の等価性が表れますので、
rewrite による書き換えが出来るというのは非常にありがたいことです。
 *)
(** 以降のファイルでは一々これらのライブラリを入れるのは手間なので、
ここで Export しておきましょう *)
Require Export CMorphisms CEquivalence.

(**
基本的に、数学的構造の定義は

- まずは仕様を表わす Class を定義し、
- それから仕様を含めた構成要素全てを内包する Structure を定義

という順番で進めていきます。

ただし、Setoid についてはその仕様である同値関係を表わす Class が
既に存在しているので、 Structure の定義から始めましょう。
 *)
Structure Setoid :=
  { carrier :> Type;
    equal : crelation carrier;
    prf_Setoid :> Equivalence equal }.
Existing Instance prf_Setoid.
Notation makeSetoid eq := (@Build_Setoid _ eq _).

(** これらは Haskell のセクションのように使いたい場合に備えての記法集です *)
Notation "(==)" := (equal (s:=_)).
Notation "x == y :> S" := (@equal S x y) (at level 80, no associativity, y at next level).
Notation "x == y" := (equal x y) (at level 80, no associativity).
Notation "( x == )" := (fun y => x == y).
Notation "( == x )" := (fun y => y == x).

(** Map も Setoid と同様に仕様を表わす Class である Proper が
    定義されているので、 直接 Structure を定義します。
 *)
Structure Map (X Y: Setoid) :=
  { fbody:> X -> Y;
    fbody_Proper: Proper ((==) ==> (==)) fbody }.
Existing Instance fbody_Proper.
Notation makeMap f := (@Build_Map _ _ f _).
Notation "[ x .. y :-> p ]" := 
  (makeMap (fun x => .. (makeMap (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' [ x .. y :-> '/ ' p ] ']'").

(** ** Attributes of Map  *)
Definition injective (A B: Setoid)(f: Map A B) :=
  forall x y, f x == f y -> x == y.

Definition surjective (A B: Setoid)(f: Map A B) :=
  forall b: B, exists a: A, f a == b.

Arguments injective {A B} / f.
Arguments surjective {A B} / f.

(** ** composition & identity  *)
Program Definition compose_Map (X Y Z: Setoid)(f: Map X Y)(g: Map Y Z): Map X Z :=
  [ x :-> g (f x) ].
Next Obligation.
  intros x y Heq.
  do 2 apply fbody_Proper.
  assumption.
Qed.

Program Definition id_Map (X: Setoid): Map X X := [x :-> x].
Next Obligation.
  intros x y Heq.
  assumption.
Qed.

(** Map 上の等価性は外延的等価性と同等のもので定義。  *)
Definition equal_Map {X Y: Setoid}(f g: Map X Y): Prop :=
  forall x: X, f x == g x.
Arguments equal_Map {X Y} / f g.

Instance equal_Map_Equiv (X Y: Setoid): Equivalence (@equal_Map X Y).
Proof.
  split.
  - intros f x; simpl.
    apply reflexivity.
  - intros f g Heq x; simpl; apply symmetry; now apply Heq.
  - intros f g h Heqfg Heqgh x; simpl.
    apply (@transitivity _ _ _ _ (g x)).
    + apply Heqfg.
    + apply Heqgh.
Defined.

(** 同値関係であることが示せれば、Map 自身も Setoid となる。 *)
Definition Setoid_Map (X Y: Setoid): Setoid := Build_Setoid (equal_Map_Equiv X Y).
Canonical Structure Setoid_Map.

Notation "(-->)" := Setoid_Map.
Notation "X --> Y" := (Setoid_Map X Y) (at level 55, right associativity).

(** ** Unique Existance for Setoid  *)
Definition Unique (A: Setoid)(P: A -> Prop)(x: A) :=
  P x /\ (forall x': A, P x' -> x == x').

Notation "'Exists' ! x .. y , p" :=
  (ex (Unique (fun x => .. (ex (Unique (fun y => p))) ..)))
    (at level 200, x binder, right associativity,
     format "'[' 'Exists' ! '/ ' x .. y , '/ ' p ']'").


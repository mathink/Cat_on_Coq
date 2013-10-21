
Require Import List.
Require Import Setoid Category Sets Functor Natrans Adjunction Monad.

Set Implicit Arguments.

(* 1. flatten は 自然変換である．

   型変数をとるデータ型があった時，その構造にのみ依存するような変換は，
   それぞれのデータ型を型の圏上の函手とみなした時，その函手の間の自然変換となる．

   というお話．
 *)

(** * list as Idempotent Functor on Sets *)
Program Instance map_Map {X Y: Set}
: Map (FunctionSetoid X Y)
      (FunctionSetoid (list X) (list Y)) :=
  { ap := @map X Y }.
Next Obligation.
  induction x0 as [ | h t]; simpl in *; congruence.
Qed.

Program Instance ListFunctor: Functor Sets Sets :=
  { fobj X := list X;
    fmap X Y := map_Map }.
Next Obligation.
  apply map_id.
Qed.
Next Obligation.
  apply map_map.
Qed.


(** * tree as Idempotent Functor on Sets *)
Inductive tree (A: Set) :=
| leaf (a: A) | node (l r: tree A).

Fixpoint map_tree {A B: Set}(f: A -> B)(t: tree A): tree B :=
  match t with 
    | leaf a => leaf (f a)
    | node l r => node (map_tree f l) (map_tree f r)
  end.

Lemma map_tree_id:
  forall (A: Set)(t: tree A), map_tree (id (Category:=Sets)(X:=A)) t = t.
Proof.
  induction t as [ a | l IHl r IHr ]; simpl in *; congruence.
Qed.

Lemma map_tree_map_tree:
  forall (A B C: Set)(f: A -> B)(g: B -> C)(t: tree A),
    map_tree g (map_tree f t) = map_tree (fun x => g (f x)) t.
Proof.
  induction t as [ a | l IHl r IHr]; simpl in *; congruence.
Qed.

Program Instance map_tree_Map {X Y: Set}
: Map (FunctionSetoid X Y)
      (FunctionSetoid (tree X) (tree Y)) :=
  { ap := @map_tree X Y }.
Next Obligation.
  induction x0 as [ a | l IHl r IHr ]; simpl in *; congruence.
Qed.

Program Instance TreeFunctor: Functor Sets Sets :=
  { fobj X := tree X;
    fmap X Y := map_tree_Map }.
Next Obligation.
  apply map_tree_id.
Qed.
Next Obligation.
  apply map_tree_map_tree.
Qed.


(* flatten: tree => list  *)
Fixpoint flatten {A: Set}(t: tree A): list A :=
  match t with
    | leaf a => cons a nil
    | node l r => app (flatten l) (flatten r)
  end.

(* flatten は確かに自然変換である．証明は短い *)
Program Instance flatten_natrans: Natrans TreeFunctor ListFunctor :=
  { natrans X := flatten (A:=X) }.
Next Obligation.
  induction x as [a | l IHl r IHr]; simpl; auto.
  rewrite map_app.
  congruence.
Qed.


(* 2. list は忘却函手 U: Mon -> Sets の左随伴である．

   自由〜については，それを構成する函手が忘却函手の左随伴として特徴づけられる．
   というような話が圏論勉強会であった．

   list が自由モノイドを構成する，ということから，上の事実を確認してみよう．
  *)

(* 2.1 圏 Mon を構成する *)
(* Monoid の定義 *)
Class Monoid :=
  { mon : Set;
    mon_binop: mon -> mon -> mon;
    mon_unit: mon;

    monoid_unit_left:
      forall x: mon,
        mon_binop mon_unit x = x;
    monoid_unit_right:
      forall x: mon,
        mon_binop x mon_unit = x;
    monoid_assoc:
      forall x y z: mon,
        mon_binop x (mon_binop y z) =mon_binop (mon_binop x y) z }.
Notation "X ⊕ Y" := (mon_binop X Y) (at level 60, right associativity).
Coercion mon: Monoid >-> Sortclass.

(* Monoid 準同型 *)
Class MonoidHom (M N: Monoid) :=
  { mon_map : M -> N;

    mon_map_unit:
      mon_map mon_unit = mon_unit;

    mon_map_binop:
      forall x y: M,
        mon_map (x⊕y) = mon_map x⊕mon_map y }.
Coercion mon_map: MonoidHom >-> Funclass.

Program Instance ComposeMH{M N L: Monoid}(f: MonoidHom M N)(g: MonoidHom N L)
: MonoidHom M L :=
  { mon_map x := mon_map (mon_map x) }. 
Next Obligation.
  repeat rewrite mon_map_unit; auto.
Qed.
Next Obligation.
  repeat rewrite mon_map_binop; auto.
Qed.

Program Instance IdMH {M: Monoid}: MonoidHom M M :=
  { mon_map x := x }. 

Program Instance MonoidHomSetoid (X Y: Monoid): Setoid :=
  { carrier := MonoidHom X Y; equal f g := forall x, f x = g x }. 
Next Obligation.
  split; auto; congruence.
Qed.

(* 圏 Mon が定義できた．
   下準備がいろいろいるので，いざというときの証明が短い *)
Program Instance Mon: Category :=
  { obj := Monoid;
    arr X Y := MonoidHomSetoid X Y;
    compose X Y Z f g := ComposeMH f g;
    id X := IdMH }.
Next Obligation.
  congruence.
Qed.

(* 2.2 忘却函手 U: Mon -> Sets の構成

   えらくあっさりしているが，定義を考えればこうなるのは自然．

   (自然，という言葉を迂闊に使うのは避けましょう)
 *)
Program Instance ForgetMon_fmap (X Y: Monoid)
: Map (MonoidHomSetoid X Y) (FunctionSetoid X Y) :=
  { ap f := f }.

Program Instance ForgetMon: Functor Mon Sets :=
  { fobj X := (@mon X) ; fmap X Y := ForgetMon_fmap X Y }.

(* 2.3 自由モノイド構成函手 List : Sets -> Mon の構成

   普通は | |: Sets -> Mon と書かれている．
   集合 X に対して，X型の要素からなるリスト，連結，空リスト がモノイドをなすことを利用．
 *)
(* List はモノイドですよー *)
Program Instance ListMonoid (X: Set): Monoid :=
  { mon := list X;
    mon_binop x y := app x y;
    mon_unit := nil }.
Next Obligation.
  apply app_nil_r.
Qed.
Next Obligation.
  apply app_assoc.
Qed.

(* map はモノイド準同型ですよー *)
Program Instance map_MonoidHom {X Y: Set}(f: X -> Y)
: MonoidHom (ListMonoid X) (ListMonoid Y) :=
  { mon_map := map f }.
Next Obligation.
  apply map_app.
Qed.

Program Instance map_MonoidHomMap (X Y: Sets)
: Map (FunctionSetoid X Y) (MonoidHomSetoid (ListMonoid X) (ListMonoid Y)) :=
  { ap := map_MonoidHom }.
Next Obligation.
  induction x0 as [ | h t ]; auto.
  simpl.
  rewrite Heq.
  rewrite IHt.
  reflexivity.
Qed.

(* そして List が Sets から Mon への函手を導出しますよー *)
Program Instance ListFunctorMon: Functor Sets Mon :=
  { fobj X := ListMonoid X ; fmap X Y := map_MonoidHomMap X Y }.
Next Obligation.
  simpl; intros.
  induction x as [ | h t ]; simpl; congruence.
Qed.
Next Obligation.
  induction x as [ | h t ]; simpl; congruence.
Qed.


(* 随伴における射の対応．これは Sets の射を Mon の射へ変換する．名前が長い．*)
Fixpoint List_adj_phi_inv_def {X: Sets}{Y: Mon}
         (g: X -> ForgetMon Y)(m: ListFunctorMon X) :=
  match m with
    | nil => mon_unit
    | cons h t => g h ⊕ List_adj_phi_inv_def g t
  end.

(* その変換が確かにモノイド準同型を構成することを確認． *)
Program Instance List_adj_phi_inv (X: Sets)(Y: Mon)(g: X -> ForgetMon Y)
: MonoidHom (ListFunctorMon X) Y :=
  { mon_map := List_adj_phi_inv_def g }.
Next Obligation.
  unfold List_adj_phi_inv_def; simpl.
  generalize dependent y.
  induction x as [ | h t ].
  - simpl.
    intro.
    rewrite monoid_unit_left; auto.
  - simpl.
    intro.
    rewrite IHt.
    rewrite monoid_assoc.
    auto.
Qed.

(* 準備が終わったので，随伴であることを示しましょう．

   今回は Hom-set による定義で随伴を与えますが，
   Unit や Counit を使ってもできるはずです．

   その際は．今回 adj_phi や adj_phi_inv の定義として与えた変換が
   自然変換であることを示すという準備が必要です．

   どのような随伴かに合わせて定義を選ぶと，証明がやりやすくなるんじゃないでしょうか．
 *)
Program Instance ListAdjunction
: Adjunction_Hom ListFunctorMon ForgetMon :=
  { adj_phi X Y f := fun x => f (cons x nil);
    adj_phi_inv X Y g := List_adj_phi_inv _ _ g
  }.
Next Obligation.
  unfold List_adj_phi_inv_def; simpl.
  induction x as [ | h t ]; simpl; congruence.
Qed.
Next Obligation.
  unfold List_adj_phi_inv_def; simpl.
  induction x as [ | h t ]; simpl.
  - change (mon_unit = f mon_unit).
    rewrite mon_map_unit; auto.
  - rewrite IHt.
    rewrite <- mon_map_binop.
    simpl.
    auto.
Qed.
Next Obligation.
  rewrite monoid_unit_right.
  auto.
Qed.


(* 3. List はモナドを構成します
 
   よくある例ですね．やってみましょう．
 *)
(* 3.1 モナドの unit を構成．

   ただひとつの要素からなるリストを作る操作がこれに該当します．
   型クラスが証明を終えてくれました．

   特に面白くありません．
   *)
Program Instance cons_a_nil_Natrans: Natrans (IdFunctor Sets) ListFunctor :=
  { natrans X := fun x => cons x nil }.

(* 3.2 モナドの join を構成．

   リストのリスト，をリストへ変換する操作，つまり concat です．
   ライブラリの List に入ってなかった気がしたのでまずはそこから作ります．

   もし入っていたらそれを使えばいいです．
  *)
Fixpoint concat {X: Set}(ll: list (list X)) :=
  match ll with
    | nil => nil
    | cons hl tll => app hl (concat tll)
  end.

(* 証明はまぁ，帰納法で普通に終わります． *)
Program Instance concat_Natrans
: Natrans (ComposeFunctor ListFunctor ListFunctor) ListFunctor :=
  { natrans X := fun ll => concat ll }.
Next Obligation.
  induction x as [ | hl tll ]; simpl in *; auto.
  rewrite map_app.
  congruence.
Qed.

(* 3.3 モナドを作る

   concat をここで初めて定義したので，後の証明で使う補題を一つ示しておきます．

   演算の交換可能性ってよく出てくるので，
   その部分だけ取り出してパッケージングしておきたいですね．
   *)
Lemma concat_app:
  forall {X: Set}(ll1 ll2: list (list X)),
    concat (ll1 ++ ll2) = concat ll1 ++ concat ll2.
Proof.
  induction ll1 as [ | hl tll ]; simpl in *; auto.
  intros.
  rewrite <- app_assoc.
  rewrite IHtll.
  reflexivity.
Qed.

(* List はモナドです． *)
Program Instance ListMonad: Monad ListFunctor.
Next Obligation.
  apply app_nil_r.
Qed.
Next Obligation.
  induction x as [ | h t ]; simpl in *; congruence.
Qed.
Next Obligation.
  induction x as [ | hll tlll ]; simpl in *; auto.
  rewrite concat_app.
  rewrite IHtlll.
  reflexivity.
Qed.
(* List はモナドでした． *)

(* 3.4 list はクライスリトリプル

   Haskell のモナドはこっちです．
   モナドとは互いに互いを構成可能という意味で等価です(証明は Monad.v にあります)．
   *)
(* KT の bind は flat_map です．
   list が KT であることの証明で用いる補題を証明しておきます． *)
Lemma flat_map_app:
  forall (X Y: Set)(f: X -> list Y)(l1 l2: list X),
    flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  induction l1 as [ | h t ]; simpl in *; auto.
  intros.
  rewrite <- app_assoc; congruence.
Qed.

(* 作ります．この定義は馴染みがある人も多いんじゃないでしょうか *)
Program Instance ListKT: KT (fun X: Sets => list X) :=
  { ret X a := cons a nil;
    bind X Y f := flat_map f }.
Next Obligation.
  induction x as [ | h t ]; simpl in *; auto; congruence.
Qed.
Next Obligation.
  induction x as [ | h t ]; simpl in *; auto; congruence.
Qed.
Next Obligation.
  apply app_nil_r.
Qed.
Next Obligation.
  induction x as [ | h t ]; simpl in *; auto.
  rewrite flat_map_app.
  rewrite IHt.
  reflexivity.
Qed.
(* 作りました． *)



(* 圏から作り始めて，普段使いの "モナド" まで辿りつけたのでよかったなぁ．つづく *)
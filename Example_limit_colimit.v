(* 
  Cone.v で 函手についての極限と余極限を定義しました．
  ここでは，圏のいろいろなものがこれら2つの言葉で言い表せることを見て行きたいと思います．

  普遍射を定義したらもっといい感じになると思います．
 *)

Require Import Setoid Category Functor Cone.

(* 1. 直積と余直積

   2つの対象のみからなる圏を 2 と書くことにすると，
   圏 C に於ける直積と余直積はそれぞれ 函手 D: 2 -> C の
   極限対象と余極限対象になります．
   *)

(* 1.1 "2" の構成

  "2" の対象は，めんどいので bool 型の true と false にしておきます
   射が単位元しかないのでそういう Setoid を作っておきましょう．

*)
Program Instance Empty_Setoid: Setoid :=
  { carrier := Empty_set }.

Program Instance Unit_Setoid: Setoid :=
  { carrier := unit }.

Program Instance Two: Category :=
  { obj := bool;
    arr X Y := if negb (xorb X Y) then Unit_Setoid else Empty_Setoid }.
Next Obligation.
  destruct X.
  destruct Z; simpl in *.
  exact tt.
  destruct Y; simpl in *; contradiction.
  destruct Z; simpl in *.
  destruct Y; simpl in *; contradiction.
  exact tt.
Defined.
Next Obligation.
  destruct X; simpl; exact tt.
Defined.
Next Obligation.
  unfold Two_obligation_1.
  simpl.
  destruct X; simpl in *.
  destruct W; simpl in *.
  reflexivity.
  destruct Y; simpl in *.
  destruct Z; simpl in *; contradiction.
  destruct Z; simpl in *; contradiction.
  destruct W; simpl in *.
  destruct Y; simpl in *.
  contradiction.
  destruct Z; simpl in *; contradiction.
  reflexivity.
Qed.  
Next Obligation.
  unfold Two_obligation_1.
  destruct X; simpl in *.
  destruct Z; simpl in *.
  reflexivity.
  destruct Y; simpl in *; contradiction.
  destruct Z; simpl in *.
  destruct Y; simpl in *; contradiction.
  reflexivity.
Qed.  
Next Obligation.
  unfold Two_obligation_1.
  unfold Two_obligation_2.
  destruct X; simpl in *.
  destruct Y; simpl in *.
  elim f; reflexivity.
  contradiction.
  destruct Y; simpl in *.
  contradiction.
  elim f; reflexivity.
Qed.  
Next Obligation.
  unfold Two_obligation_1.
  unfold Two_obligation_2.
  destruct X; simpl in *.
  destruct Y; simpl in *.
  elim f; reflexivity.
  contradiction.
  destruct Y; simpl in *.
  contradiction.
  elim f; reflexivity.
Qed.  
(* あぁ! 手を抜いたせいで中身がひどい! *)


(* というわけで始めましょう *)
Section Example.
  Context (C: Category).

  (* 1.2 Two からの函手の構成 
     対象関数は楽ですね♪ *)
  Definition TwoFunctor_fobj (X Y: C): Two -> C :=
    fun b => if b then X else Y.

  (* 射関数を直接書くの難しいので，証明モードに頼ります☆ *)
  Program Instance TwoFunctor_fmap (X Y: C)(b1 b2: Two)
  : Map (b1 ⟶ b2) (TwoFunctor_fobj X Y b1 ⟶ TwoFunctor_fobj X Y b2).
  Next Obligation.
    destruct b1; simpl in *.
    destruct b2; simpl in *.
    exact (id_ X).
    contradiction.
    destruct b2; simpl in *.
    contradiction.
    exact (id_ Y).
  Defined.
  (* ...... *)
  Next Obligation.
    destruct b1; simpl in *.
    destruct b2; simpl in *.
    equiv_refl.
    contradiction.
    destruct b2; simpl in *.
    contradiction.
    equiv_refl.
  Qed.
  (* ...射関数を作りました! *)

  (* これでやっと函手を構成できますね! *)
  Program Instance TwoFunctor (X Y: C): Functor Two C :=
    { fobj b := if b then X else Y;
      fmap b1 b2 := TwoFunctor_fmap X Y b1 b2 }.
  Next Obligation.
    destruct X0; simpl; equiv_refl.
  Qed.
  Next Obligation.
    (* (^_^) *)
    destruct X0; simpl in *.
    destruct Y0; simpl in *.
    destruct Z; simpl in *.
    apply id_dom.
    contradiction.
    destruct Z; simpl in *.
    contradiction.
    contradiction.
    destruct Y0; simpl in *.
    contradiction.
    destruct Z; simpl in *.
    contradiction.
    apply id_cod.
  Qed.
  (* 証明をむやみに追わないように．
     対話的に実行した時にいろいろツケが回ってきているのを確認できます *)

  (* なんにせよ，任意の圏 C に対する Two からの函手を構成できました *)

  
  (* 1.3 TwoFunctor への錐の構成

     「直積が函手の極限である」という言明のためには，
     その函手への錐全体からなる圏を構築する必要があります．

     以下では，TwoFunctor への錐とその間の変換を構成していきます．
   *)
  Program Instance TwoFunctor_ConeTo
          (X Y P: C)(f1: P ⟶ X)(f2: P ⟶ Y)
  : ConeTo (TwoFunctor X Y) :=
    { apex_to := P }.
  Next Obligation.
    case i.
    exact f1.
    exact f2.
  Defined.
  Next Obligation.
    destruct i; simpl in *.
    destruct j; simpl in *.
    apply id_cod.
    contradiction.
    destruct j; simpl in *.
    contradiction.
    apply id_cod.
  Qed.

  Program Instance TwoFunctor_ConeTo_Hom
          (X Y P: C)(f1: P ⟶ X)(f2: P ⟶ Y)
          (Q: C)(g1: Q ⟶ X)(g2: Q ⟶ Y)
          (h: P ⟶ Q)
          (Heq_fgh1: f1 == g1◦h)
          (Heq_fgh2: f2 == g2◦h)
  : ConeTo_Hom
       (TwoFunctor_ConeTo X Y P f1 f2)
       (TwoFunctor_ConeTo X Y Q g1 g2) :=
    { cone_to_hom := h }.
  Next Obligation.
    case i; simpl; auto.
  Qed.

  (* 錐と変換を定義できれば，圏の構成は簡単です．
     Cone.v で一般の錐から圏を構成する方法を与えていました． *)
  Program Instance TwoFunctor_ConeTo_Cat (X Y: C): Category :=
    ConeTos (TwoFunctor X Y).

  
  (* 1.4 直積は "2" からの函手の極限
     
     錐のなす圏を構成できたので，早速本題にとりかかりましょう *)
  Section Product_as_limit.
    (* まず，C には直積対象が存在すると仮定します *)
    Context (X Y XY: C)(proj_X: XY ⟶ X)(proj_Y: XY ⟶ Y)
            (Hproduct: product C X Y XY proj_X proj_Y).

    (* 直積自身も TwoFunctor への錐をなすことを示します
       極限対象はあくまで錐のなす圏に於ける対象なので，
       錐であることをしっかり証明しておかないと議論が進みません． *)
    Program Instance prod_ConeTo
    : ConeTo (TwoFunctor X Y)  :=
      { apex_to := XY }.
    Next Obligation.
      case i; [ exact proj_X | exact proj_Y ].
    Defined.
    Next Obligation.
      destruct i; simpl in *.
      destruct j; simpl in *.
      apply id_cod.
      contradiction.
      destruct j; simpl in *.
      contradiction.
      apply id_cod.
    Qed.

    (* さて，直積が極限であること，即ち錐のなす圏の終対象であることを
       証明するので，任意の錐からの射が構成できるはずです． *)
    Program Instance prod_ConeTo_Hom
            (c: ConeTo (TwoFunctor X Y))
    : ConeTo_Hom c prod_ConeTo.
    (* あれ? 定義で与えてませんね? *)
    Next Obligation.
      unfold product in Hproduct.
      generalize
        (Hproduct c (generatrix_to (ConeTo:=c) true) (generatrix_to (ConeTo:=c) false)); intro H.
      destruct H.
      exact x.
    Defined.
    (* 証明モードで項を与えたときは Defined. で締める．これ大事です． *)
    Next Obligation.
      unfold product in Hproduct.
      unfold prod_ConeTo_Hom_obligation_1.
      (* あっ...... *)
      generalize
        (Hproduct c (generatrix_to (ConeTo:=c) true) (generatrix_to (ConeTo:=c) false)); intro H.
      destruct H as [fg [[HX HY] Hh]].
      case i; simpl; equiv_symm; auto.
    Qed.
    
    (* これで準備が終わりました．
       終対象であることは，更に射の唯一性を求めますが，それは次の定理の証明の中で示しましょう．
       やっと，この例の目的であった「直積が極限である」ことの証明に入ります．
       ステートメントが少し込み入っていますが，これは後々スッキリさせる予定です．
 *)
    Theorem product_is_limit_of_TwoFunctor:
      @is_Limit _ _ (TwoFunctor X Y)
                prod_ConeTo
                (fun c => prod_ConeTo_Hom c).
    Proof.
      unfold is_Limit, terminal.
      intros c f.
      simpl in *.
      unfold prod_ConeTo_Hom_obligation_1.
      generalize
        (Hproduct c (generatrix_to (ConeTo:=c) true) (generatrix_to (ConeTo:=c) false)); intro H.
      destruct H as [fg [[HX HY] Hh]].
      simpl in *.
      apply Hh.
      split; equiv_symm.
      generalize (cone_to_hom_commute (ConeTo_Hom:=f) true);
        simpl; auto.
      generalize (cone_to_hom_commute (ConeTo_Hom:=f) false);
        simpl; auto.
    Qed.

  (* はい．この定理に至るまでにはいくつかの惨事を目にしたことと思いますが，
     この定理自身の証明はそこそこわかりやすいです...よね?

     とにかく，極限の例としてよく取り上げられる直積対象を Coq の上でもそのように扱うことができました．やったね! でもこのコードすっげー汚いよ! いろいろ練り直す必要があるね!

     あと，terminal とか product とかも型クラスとしてパッキングしないと使いづら行ったらありゃしないんじゃないかな! 

    つづく(余直積についてやる気力が今はない)
   *)
  End Product_as_limit.

End Example.

           
           
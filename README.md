Cat_on_Coq
==========

* 現状報告(2014/05/15)

  設計を見直したり SSReflect の利用を標準としたりなど大きい変更をしているので、現時点で動作を確認できているのは

  - Setoid.v
  - Category.v
  - Functor.v
  - Natrans.v
  - Cone.v
  - Adjunction.v
  - ListFunctor.v

  の 7 つです。

  ファイル間の依存関係については [これ](dep_graph.dot.png) をご参照ください。

* 環境

  - 必須なもの

	- Coq-8.4pl3 以上
	- SSReflect-1.4 以上

	私自身は Coq-8.4pl4 + SSReflect-1.5 で作業していますが，最新版特有の機能は利用していないはずなので，
	一つ前くらいなら問題なく動くと思います．

  - あったほうがよいもの

	- ProofGeneral-4.3 (snapshot)

	ProofGeneral を使う場合，4.3 でないと load path 関係で文句を言われます．
	具体的に言えば，Cat\_on\_Coq のトップディレクトリに対して COC という名前で論理的なパスを割り当てています．
	コンパイル時はオプションをつけているので .v ファイルからモジュールを読み込むときにはこの情報が手にはいり，問題なくロードできるのですが，
	ProofGeneral を利用する場合にはその情報(論理パス COC が具体的にどこなのか)を教えてあげなければいけません．
	4.3 からの新機能として，.v ファイルの処理を開始するとき，そのファイルがあるディレクトリ内の _CoqProject という名前のファイルを読み込むようになったのですが，そこに実は上記の情報が書いてあります(Makefile の生成もこのファイルを使っています)．
	4.3 からの新機能ということは，つまり 4.2 だと使えないわけなので，別の形の対策が入ります．
	それについては [ProofGeneral の File Variable とかいうものを使ったり](http://proofgeneral.inf.ed.ac.uk/htmlshow.php?title=Proof+General+user+manual&file=releases%2FProofGeneral%2Fdoc%2FProofGeneral%2FProofGeneral_10.html#Using-file-variables)，
	`Add LoadPath "." as COC.` をファイルの冒頭につけるなり，`Require Import` 内の `COC.` を全削除するなりして ad-hoc に回避しましょう．

	これがめんどくさくて 4.3 の snapshot に手を出したので，なんか気の利いた対策を僕がすることはないと思います．

  
* foldr as catamorphism

  ListFunctor.v は foldr が Set のなす圏の上の自己函手 listF_A: X |-> 1+A*X の始代数の catamorphism であることを証明しています。
  また、そうやって得られた foldr (ファイル中では cata_foldr) を Haskell コードへ Extraction したものが [[ext/cata_foldr.hs]] にあります。

* 目的

  1. 圏論の勉強

     圏論における様々なものを書いて示して書いて示して書いて示して...

  2. 圏論的概念の利用 on Coq.

     プログラム運算とかっすね．catamorphism や anamorphism を扱う土台作り?

  3. Monads with Predicate Liftings への接続

     MPL を使ってモナドを使って書かれたプログラムに関する証明を
     特定のモナドの構造に依存しないような形で行うための証明フレームワークを作ろう，
     としているんですが，MPL 自体が本来はそこそこ複雑な構成物
     (添字付圏全体からなる圏上の自己函手のなす圏のモノイド対象)
     なので，本格的に証明を弄っていくためにはさまざまな性質を用いる必要があるなぁ，と．

     Cat_on_Coq から地続きに MPL の定義まで持っていくのが当面の目標でしょうか．
     
     そもそも，MPL 自体かなり知識の隙間を拭って作ったものなので，これ自体はしっかりしているんですが，扱う僕がしっかりしていないので，そこをカバーするための過程でもあります．

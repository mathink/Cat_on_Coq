Cat_on_Coq
==========

* 現状報告(2014/05/15)

  設計を見直したり SSReflect の利用を標準としたりなど大きい変更をしているので、現時点で動作を確認できているのは

  - Setoid.v
  - Category.v
  - Functor.v
  - Cone.v
  - Adjunction.v
  - ListFunctor.v

  の 5 つです。
  
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

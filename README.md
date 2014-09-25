Category Theory on Coq
========

# 注意事項

内容の大幅更を予定していまして、それに伴ってリポジトリ内を一掃いたしました。
ただし、一掃されたのは master ブランチのみですので、
univ ブランチ内のコードはそのままです。

最新版への最初の更新は 9 月末です。

9/23 現在、試験的に米田の補題 (src/Yoneda/YonedaLemma.v) までのコードを載せています。

# 概要

Coq の上で圏論を展開し、圏論を勉強していこうと目論んでいます。

coqdoc で生成したドキュメントが [http://mathink.github.io/Cat_on_Coq/](http://mathink.github.io/Cat_on_Coq/) から見れますが、
あまりドキュメンテーションされてません。

気長にお待ちください。

# 用法

## ソフトウェア

Universe Polymorphism を利用しています。
最新版の Coq-8.4pl4 には導入されていない機能ですので、
コンパイルなどにはこちらの Coq をお使いください。
[https://github.com/HoTT/coq](https://github.com/HoTT/coq "HoTT/coq")

また、ProofGeneral も、プロジェクトファイルの扱いなどを良い感じにするために [開発版](http://proofgeneral.inf.ed.ac.uk/devel) を利用しております。

## ビルド

HoTT/coq にパスが通し、 Cat\_on\_Coq ディレクトリ直下で make すれば OK です。


# 構成

```
src
|-- Algebra
|   |-- Algebra.v
|   `-- ListFunctor.v
|-- Base
|   |-- Category.v
|   |-- Discrete.v
|   |-- Functor.v
|   |-- Natrans.v
|   `-- Setoid.v
|-- Limit
|   |-- Cone.v
|   `-- LimProd.v
`-- Yoneda
    `-- YonedaLemma.v
```

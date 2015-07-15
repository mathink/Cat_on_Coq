Category Theory on Coq
========

# 概要

Coq をノートとして利用し、圏論を展開していく予定です。

HoTT とは異なり、 Setoid をベースに圏や他の概念の定義を行う予定です。

# 用法

## ソフトウェア

HoTT 用の Coq を使っています。
* Universe Polymorphism を利用
* heterogeneous equality を使おうとするときのバグ(？)回避
のためです。

また、ProofGeneral も、プロジェクトファイルの扱いなどを良い感じにするために [開発版](http://proofgeneral.inf.ed.ac.uk/devel) を利用しております。

# 構成

```
.
|-- Makefile
|-- README.md
|-- _CoqProject
|-- doc
|   |-- coqdoc.css
|   `-- dependency.svg
`-- theories
    `-- Scratch.v
```

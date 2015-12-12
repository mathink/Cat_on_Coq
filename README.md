Category Theory on Coq
========

# 概要

Coq をノートとして利用し、圏論を展開していく予定です。

HoTT とは異なり、 Setoid をベースに圏や他の概念の定義を行う予定です。

# 用法

* Universe Polymorphism を利用するため、 coq-8.5beta3 を使用。
* ProofGeneral も、プロジェクトファイルの扱いなどを良い感じにするために [開発版](http://proofgeneral.inf.ed.ac.uk/devel) を利用。

# 構成

```
.
|-- html
`-- theories
    |-- Abel.v
    |-- Adjunction
    |   `-- Core.v
    |-- Adjunction.v
    |-- Appendix
    |   `-- length.v
    |-- Category
    |   |-- Core.v
    |   |-- Functor.v
    |   |-- Morphism.v
    |   |-- Natrans.v
    |   `-- Object.v
    |-- Category.v
    |-- Construction
    |   |-- Equalizer.v
    |   |-- Limit.v
    |   |-- Product.v
    |   |-- Universal.v
    |   `-- Yoneda.v
    |-- Construction.v
    |-- Enrich
    |   `-- Core.v
    |-- Equalities.v
    |-- Example.v
    |-- Init
    |   |-- Prelude.v
    |   `-- Relations.v
    |-- Init.v
    |-- Monoid
    |   `-- Monoidal.v
    |-- Monoid.v
    |-- Setoid
    |   |-- Core.v
    |   `-- Map.v
    |-- Setoid.v
    |-- Structure
    |   |-- Cat.v
    |   |-- Comma.v
    |   |-- Fun.v
    |   |-- Hcomp.v
    |   |-- Hom.v
    |   `-- Prod.v
    `-- Structure.v
```

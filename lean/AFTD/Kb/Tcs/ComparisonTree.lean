import AFTD.Prelude

/-!
# ComparisonTree

Topic: algorithms   Node: 8effb78df211

Provenance: formalization of a published result. Source: arXiv:2610.18740 Sec. 3.1

A binary comparison decision tree on n elements whose internal nodes perform pairwise comparisons and whose leaves return an element index.
-/

/-- A deterministic comparison decision tree for elements indexed by Fin n. -/
inductive ComparisonTree (n : ℕ) : Type | leaf (ans : Fin n) : ComparisonTree n
  | branch (i j : Fin n) (left right : ComparisonTree n) : ComparisonTree n

import AFTD.Prelude

/-!
# ComparisonDecisionTree

Topic: algorithms   Node: 1325064f51bb

Provenance: original. Related work: arXiv:2611.26297

A binary comparison decision tree on n elements whose leaves return a value of type β.
-/

/-- A binary comparison decision tree on n elements whose internal nodes perform pairwise comparisons and whose leaves return a value of type β. -/
inductive ComparisonDecisionTree (n : ℕ) (β : Type) : Type where
  | leaf : β → ComparisonDecisionTree n β
  | branch : Fin n → Fin n → ComparisonDecisionTree n β → ComparisonDecisionTree n β → ComparisonDecisionTree n β

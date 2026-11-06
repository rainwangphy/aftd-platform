import AFTD.Prelude

/-!
# FunctionQueryTree

Topic: submodular   Node: ceacc53a0835

Provenance: formalization of a published result. Source: arXiv:2611.02374 Sec. 2

A deterministic query decision tree for an unknown function from α to β returning a boolean.
-/

/-- Deterministic adaptive query tree for evaluating an unknown function f : α → β with boolean output. -/
inductive FunctionQueryTree (α β : Type*) where
  | leaf : Bool → FunctionQueryTree α β
  | query : α → (β → FunctionQueryTree α β) → FunctionQueryTree α β

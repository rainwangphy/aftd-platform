import AFTD.Prelude

/-!
# StochasticMstStrategy

Topic: algorithms   Node: bb2edd3798a4

Provenance: formalization of a published result. Source: arXiv:2610.40844 Section 3

An adaptive strategy for binary stochastic MST identification is a binary decision tree on a type of edges: either a leaf (no further queries) or an internal node that queries an edge e and branches to a 0-child (on outcome 0) and a 1-child (on outcome 1).
-/

/-- An adaptive querying strategy for binary stochastic MST identification as a binary decision tree. -/
inductive StochasticMstStrategy (α : Type*) : Type _ | leaf : StochasticMstStrategy α
| query (e : α) (s₀ s₁ : StochasticMstStrategy α) : StochasticMstStrategy α

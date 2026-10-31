import AFTD.Prelude

/-!
# has_directed_cycle

Topic: combinatorics   Node: 07ccf7cc7cce

Provenance: formalization of a published result. Source: arXiv:2610.40321 Def 2

A directed graph with adjacency relation Adj has a directed simple cycle of length k (with 3 ≤ k) if there exists an injective map c : Fin k → V such that Adj (c i) (c (finRotate k i)) for all i : Fin k.
-/

/-- Existence of a simple directed cycle of length k in a digraph. -/
def has_directed_cycle {V : Type*} (Adj : V → V → Prop) (k : ℕ) : Prop := 3 ≤ k ∧ ∃ c : Fin k → V, Function.Injective c ∧ ∀ i : Fin k, Adj (c i) (c (finRotate k i))

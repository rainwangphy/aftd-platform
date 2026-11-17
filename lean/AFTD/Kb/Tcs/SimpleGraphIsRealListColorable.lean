import AFTD.Prelude

/-!
# simple_graph_is_real_list_colorable

Topic: combinatorics   Node: 4b58ca9b70c3

Provenance: formalization of a published result. Source: arXiv:2611.18384 Section 2.2

A simple graph H is k-list-colorable from real lists if for every assignment of lists of real numbers A(v) with card A(v) = k, there exists a proper vertex coloring c with c(v) ∈ A(v) for all v.
-/

/-- Predicate that a simple graph is k-list-colorable from real lists. -/
def simple_graph_is_real_list_colorable {V : Type*} (H : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ A : V → Finset ℝ, (∀ v, (A v).card = k) →
    ∃ c : V → ℝ, (∀ v, c v ∈ A v) ∧ (∀ u v, H.Adj u v → c u ≠ c v)

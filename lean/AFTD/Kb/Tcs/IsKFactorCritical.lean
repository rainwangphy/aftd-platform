import AFTD.Prelude

/-!
# is_k_factor_critical

Topic: graphs   Node: 950e33742ee2

Provenance: formalization of a published result. Source: arXiv:2611.09072, Section 1

A simple graph G on a finite vertex type V is k-factor-critical if for every subset S of V with cardinality k, the induced subgraph on Sᶜ has a perfect matching.
-/

/-- A simple graph G on a finite vertex type V is k-factor-critical if for every subset S ⊆ V of size k, the induced subgraph on Sᶜ has a perfect matching. -/
def is_k_factor_critical {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop := ∀ S : Finset V, S.card = k → ∃ M : (G.induce (S : Set V)ᶜ).Subgraph, M.IsPerfectMatching

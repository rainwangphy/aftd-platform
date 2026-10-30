import AFTD.Prelude

/-!
# is_binary_linear_graph_code

Topic: combinatorics   Node: 8db029f7d1bf

Provenance: formalization of a published result. Source: arXiv:2610.35136, Section 1

A family C of simple graphs on vertex set [n] is a binary linear graph-code if it contains the empty graph and is closed under symmetric difference.
-/

/-- A family of simple graphs on Fin n is a binary linear graph-code if it contains the empty graph and is closed under symmetric difference. -/
def is_binary_linear_graph_code (n : ℕ) (C : Set (SimpleGraph (Fin n))) : Prop := ⊥ ∈ C ∧ ∀ ⦃G G' : SimpleGraph (Fin n)⦄, G ∈ C → G' ∈ C → symmDiff G G' ∈ C

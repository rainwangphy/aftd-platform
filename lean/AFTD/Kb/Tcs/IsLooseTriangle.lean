import AFTD.Prelude

/-!
# is_loose_triangle

Topic: combinatorics   Node: c20f5a9a58a3

Provenance: formalization of a published result. Source: arXiv:2611.05261, Section 1

Three edges e₁, e₂, e₃ in a hypergraph form a loose triangle if they are pairwise distinct, each pair intersects in exactly one vertex, and their intersection e₁ ∩ e₂ ∩ e₃ is empty.
-/

/-- Three edges in a hypergraph form a loose triangle if they are pairwise distinct, each pair intersects in exactly one vertex, and the three edges have empty intersection. -/
def is_loose_triangle {V : Type*} [DecidableEq V] (e₁ e₂ e₃ : Finset V) : Prop := e₁ ≠ e₂ ∧ e₂ ≠ e₃ ∧ e₁ ≠ e₃ ∧ (e₁ ∩ e₂).card = 1 ∧ (e₂ ∩ e₃).card = 1 ∧ (e₃ ∩ e₁).card = 1 ∧ Disjoint (e₁ ∩ e₂) e₃

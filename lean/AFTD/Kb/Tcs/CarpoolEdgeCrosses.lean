import AFTD.Prelude

/-!
# carpool_edge_crosses

Topic: online_algorithms   Node: d9333e7c88c8

Provenance: formalization of a published result. Source: arXiv:2611.00388 Section 2

An edge between vertices u and v in Fin n crosses a finite vertex subset S : Finset (Fin n) if either u ∈ S and v ∉ S, or v ∈ S and u ∉ S.
-/

/-- An edge between u and v crosses subset S if exactly one endpoint belongs to S. -/
def carpool_edge_crosses {n : ℕ} (u v : Fin n) (S : Finset (Fin n)) : Prop := (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)

import AFTD.Prelude

/-!
# ValidCarpoolEdgeSequence

Topic: online_algorithms   Node: be8feaabef0f

Provenance: formalization of a published result. Source: arXiv:2611.00388 Sec 1.1, Online carpooling against an oblivious adversary

A list of edges on n vertices is valid for online carpooling if every arriving edge connects two distinct vertices.
-/

/-- Validity condition that every edge joins two distinct vertices. -/
def ValidCarpoolEdgeSequence (n : ℕ) (edges : List (Fin n × Fin n)) : Prop := ∀ e ∈ edges, e.1 ≠ e.2

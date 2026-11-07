import AFTD.Prelude

/-!
# monotone_cycle

Topic: graphs   Node: 8e37e629ac6c

Provenance: formalization of a published result. Source: arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 1

The monotone cycle MC_k is the ordered simple graph on Fin k with edges {i, i+1} for 0 ≤ i < k-1 and the edge {0, k-1}.
-/

/-- The monotone cycle MC_k on Fin k with edges between consecutive vertices and between 0 and k-1. -/
def monotone_cycle (k : ℕ) : SimpleGraph (Fin k) := SimpleGraph.fromRel (fun a b => a.val + 1 = b.val ∨ (a.val = 0 ∧ b.val + 1 = k))

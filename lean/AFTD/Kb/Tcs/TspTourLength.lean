import AFTD.Prelude

/-!
# tsp_tour_length

Topic: approximation   Node: d4d6200b17ff

Provenance: formalization of a published result. Source: arXiv:2611.09421 Section 1

The length of a tour σ on a finite set V under edge weight function ℓ is ∑_{v ∈ V} ℓ(v, σ(v)).
-/

/-- The length of a tour σ under edge weights ℓ is the sum over v of ℓ(v, σ v). -/
def tsp_tour_length {V : Type*} [Fintype V] (ℓ : V → V → ℝ) (σ : Equiv.Perm V) : ℝ := ∑ v : V, ℓ v (σ v)

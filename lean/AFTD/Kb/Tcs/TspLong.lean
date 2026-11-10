import AFTD.Prelude

/-!
# tsp_long

Topic: approximation   Node: 2295bb01db7b

Provenance: formalization of a published result. Source: arXiv:2611.09421 Section 2.1

For a vertex v in a finite set V with edge weights ℓ : V → V → ℝ, long(v) is max_{x ≠ v} ℓ(v, x).
-/

/-- For a vertex v in a complete edge-weighted graph, long(v) is the maximum length of an edge incident to v. -/
noncomputable def tsp_long {V : Type*} [Fintype V] [DecidableEq V] (ℓ : V → V → ℝ) (v : V) : ℝ := if h : (Finset.univ.erase v).Nonempty then ((Finset.univ.erase v).image (ℓ v)).max' (Finset.Nonempty.image h _) else 0

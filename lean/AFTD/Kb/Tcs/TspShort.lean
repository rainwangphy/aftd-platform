import AFTD.Prelude

/-!
# tsp_short

Topic: approximation   Node: 9106b5633e73

Provenance: formalization of a published result. Source: arXiv:2611.09421 Section 2.1

For a vertex v in a finite set V with decidable equality and edge weights ℓ : V → V → ℝ, tsp_short ℓ v is the minimum of ℓ(v, u) over all u in Finset.univ.erase v if that set is nonempty, and 0 otherwise.
-/

/-- For a vertex v in a complete edge-weighted graph, short(v) is the minimum length of an edge incident to v. -/
noncomputable def tsp_short {V : Type*} [Fintype V] [DecidableEq V] (ℓ : V → V → ℝ) (v : V) : ℝ := if h : (Finset.univ.erase v).Nonempty then ((Finset.univ.erase v).image (ℓ v)).min' (Finset.Nonempty.image h _) else 0

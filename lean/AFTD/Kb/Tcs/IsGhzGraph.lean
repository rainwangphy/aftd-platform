import AFTD.Prelude
import AFTD.Kb.Tcs.GhzIsPerfectMatching
import AFTD.Kb.Tcs.GhzVertexColouringWeight

/-!
# is_ghz_graph

Topic: quantum   Node: 1a5af073d428

Provenance: formalization of a published result. Source: scout/2610-22190-connectivity-bounds-for-ghz-graphs.md:167

For any type V : Type* with [Fintype V], a simple graph G on V with edge colouring c : Sym2 V → ℕ and edge weighting w : Sym2 V → ℂ satisfies is_ghz_graph G c w if every edge e in G.edgeSet has w e ≠ 0, every feasible monochromatic vertex colouring has ghz_vertex_colouring_weight G w c vc = 1 (where feasible means there exists M : Finset (Sym2 V) satisfying ghz_is_perfect_matching G M and ∀ e ∈ M, ∀ v : V, v ∈ e → vc v = c e, and monochromatic means ∃ k : ℕ, ∀ v : V, vc v = k), and every non-monochromatic vertex colouring vc : V → ℕ (satisfying ¬ ∃ k : ℕ, ∀ v : V, vc v = k) has ghz_vertex_colouring_weight G w c vc = 0.
-/

/-- An edge-coloured and weighted simple graph is a GHZ graph if all monochromatic feasible colourings have weight 1 and all non-monochromatic colourings have weight 0. -/
def is_ghz_graph {V : Type*} [Fintype V] (G : SimpleGraph V) (c : Sym2 V → ℕ) (w : Sym2 V → ℂ) : Prop := (∀ e ∈ G.edgeSet, w e ≠ 0) ∧
  (∀ vc : V → ℕ,
    (∃ M : Finset (Sym2 V), ghz_is_perfect_matching G M ∧ (∀ e ∈ M, ∀ v : V, v ∈ e → vc v = c e)) →
    (∃ k : ℕ, ∀ v : V, vc v = k) →
    ghz_vertex_colouring_weight G w c vc = 1) ∧
  (∀ vc : V → ℕ,
    ¬ (∃ k : ℕ, ∀ v : V, vc v = k) →
    ghz_vertex_colouring_weight G w c vc = 0)

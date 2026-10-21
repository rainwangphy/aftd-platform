import AFTD.Prelude
import AFTD.Kb.Tcs.GhzIsPerfectMatching
import AFTD.Kb.Tcs.GhzMatchingWeight

/-!
# ghz_vertex_colouring_weight

Topic: quantum   Node: 8c3eae80d4a1

Provenance: formalization of a published result. Source: scout/2610-22190-connectivity-bounds-for-ghz-graphs.md:161

For any type V : Type* with [Fintype V], given a simple graph G on V, edge weights w : Sym2 V → ℂ, edge colouring c : Sym2 V → ℕ, and vertex colouring vc : V → ℕ, ghz_vertex_colouring_weight G w c vc is the sum of ghz_matching_weight w M over all M : Finset (Sym2 V) in Finset.univ such that ghz_is_perfect_matching G M holds and for all e in M and all v in V with v ∈ e, vc v = c e.
-/

/-- The weight of an inherited vertex colouring vc is the sum over all perfect matchings inducing vc of their weights. -/
noncomputable def ghz_vertex_colouring_weight {V : Type*} [Fintype V]
    (G : SimpleGraph V) (w : Sym2 V → ℂ) (c : Sym2 V → ℕ) (vc : V → ℕ) : ℂ := open scoped Classical in
  ∑ M ∈ Finset.univ.filter (fun M => ghz_is_perfect_matching G M ∧ ∀ e ∈ M, ∀ v : V, v ∈ e → vc v = c e),
    ghz_matching_weight w M

import AFTD.Prelude
import AFTD.Kb.Tcs.GhzIsPerfectMatching
import AFTD.Kb.Tcs.IsGhzGraph

/-!
# ghz_matching_index

Topic: quantum   Node: c3daa80e1958

Provenance: formalization of a published result. Source: scout/2610-22190-connectivity-bounds-for-ghz-graphs.md:191

For any type V : Type* with [Fintype V], the matching index ghz_matching_index G of a simple graph G on V is the supremum (sSup in ℕ) of the set of natural numbers d : ℕ for which there exist an edge colouring c : Sym2 V → ℕ and edge weights w : Sym2 V → ℂ such that is_ghz_graph G c w holds, where d = Set.ncard { vc : V → ℕ | (∃ M : Finset (Sym2 V), ghz_is_perfect_matching G M ∧ ∀ e ∈ M, ∀ v : V, v ∈ e → vc v = c e) ∧ ∃ k : ℕ, ∀ v : V, vc v = k }.
-/

/-- The matching index μ(G) is the supremum over all GHZ colourings and weightings of the number of feasible monochromatic inherited vertex colourings. -/
noncomputable def ghz_matching_index {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := open scoped Classical in
  sSup { d : ℕ | ∃ (c : Sym2 V → ℕ) (w : Sym2 V → ℂ),
    is_ghz_graph G c w ∧
    d = Set.ncard { vc : V → ℕ |
      (∃ M : Finset (Sym2 V), ghz_is_perfect_matching G M ∧ ∀ e ∈ M, ∀ v : V, v ∈ e → vc v = c e) ∧
      (∃ k : ℕ, ∀ v : V, vc v = k) } }

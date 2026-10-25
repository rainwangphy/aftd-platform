import AFTD.Prelude
import AFTD.Kb.Tcs.AdjacencySpectralRadius
import AFTD.Kb.Tcs.SimpleGraphPower

/-!
# spectral_extremal_chromatic_number

Topic: graphs   Node: 5f606b2cce26

Provenance: formalization of a published result. Source: arXiv:2610.13852 Section 6

For an integer k ≥ 1 and real number r, the extremal distance-k chromatic number under spectral radius constraint r, denoted χ_λ(k, r), is the supremum of the chromatic number of the k-th power G^k over all finite simple graphs G with adjacency spectral radius at most r.
-/

/-- Extremal distance-k chromatic number under adjacency spectral radius constraint r. -/
noncomputable def spectral_extremal_chromatic_number (k : ℕ) (r : ℝ) : ℕ∞ := open scoped ENNReal in
  ⨆ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : adjacency_spectral_radius G ≤ ENNReal.ofReal r),
    (simple_graph_power G k).chromaticNumber

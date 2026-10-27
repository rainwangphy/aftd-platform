import AFTD.Prelude
import AFTD.Kb.Tcs.BalancedMultipartiteNearestSpectralDistance
import AFTD.Kb.Tcs.BalancedCompleteMultipartiteGraph
import AFTD.Kb.Tcs.SpectralDistanceL2Sq
import AFTD.Kb.Tcs.SimpleGraphAdjEigenvaluesSorted

/-!
# balanced_multipartite_nearest_spectral_distance_nonneg

Topic: graphs   Node: be79900e0e94

Provenance: helper lemma. sanity lemma for balanced_multipartite_nearest_spectral_distance (OP-546)

The nearest squared spectral distance c_r(n) is nonnegative.
-/

theorem balanced_multipartite_nearest_spectral_distance_nonneg (r n : ℕ) :
    0 ≤ balanced_multipartite_nearest_spectral_distance r n := by
  apply Real.sInf_nonneg
  rintro d ⟨H, -, rfl⟩
  unfold spectral_distance_l2_sq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

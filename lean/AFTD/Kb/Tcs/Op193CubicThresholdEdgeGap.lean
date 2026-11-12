import AFTD.Prelude

/-!
# op_193_cubic_threshold_edge_gap

Topic: graphs   Node: 8ed9cf0a270e

Provenance: helper lemma. Arithmetic component of the clique-free reduction for arXiv:2610.17884 Section 3; experiment 23319.

The edge-count gap in the clique-free anchor argument is strictly positive at and beyond the cubic threshold.
-/

theorem op_193_cubic_threshold_edge_gap (k m : ℝ) (hk : 3 ≤ k)
    (hm : k * ((k-1)^2 + 1) ≤ m) :
    0 < m^2 - 3*m*(k-1) - (m-2*k+2)*k*(k-1)^2 := by
  have hkpos : 0 < k := by linarith
  have hkm : 0 < k-2 := by linarith
  have hdelta : 0 ≤ m-k*((k-1)^2+1) := sub_nonneg.mpr hm
  have hid : m^2 - 3*m*(k-1) - (m-2*k+2)*k*(k-1)^2 =
      k*(k-2)^2 + (m-k*((k-1)^2+1))*(k^2*(k-2)+3) +
        (m-k*((k-1)^2+1))^2 := by ring
  rw [hid]
  positivity

import AFTD.Prelude
import AFTD.Kb.Tcs.LlyPositiveEdgeConnectivityThreshold
import AFTD.Kb.Tcs.LlyPositiveEdgeConnectivityThresholdThree

/-!
# not_forall_lly_positive_edge_connectivity_threshold_eq_ceil

Topic: graphs   Node: c99e7226795e

Provenance: original. Related work: Answers OP-165 (asked after arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Theorem 1.4, whose sharpness construction needs 2n/3 even and ≥ 6) in the negative. Exact computation of c(n) for n ≤ 6 (curvatures via the paper's Theorem 2.2 and min-cost flow): c(3) = 0, c(4) = 2, c(5) = 2, c(6) = 3, against ⌈2n/3 − 1⌉ = 1, 2, 3, 3.

It is not true that c(n) = ⌈2n/3 − 1⌉ for all n ≥ 3. Already c(3) = 0, since every connected graph on 3 vertices (the path and the triangle) has positive Lin–Lu–Yau curvature on every edge, while ⌈2·3/3 − 1⌉ = 1. The failure is not only this degenerate case: by exact computation c(5) = 2 while ⌈2·5/3 − 1⌉ = 3 (see lly_positive_edge_connectivity_threshold_five).
-/

theorem not_forall_lly_positive_edge_connectivity_threshold_eq_ceil :
    ¬ ∀ n : ℕ, 3 ≤ n →
      lly_positive_edge_connectivity_threshold n = ⌈(2 * (n : ℝ)) / 3 - 1⌉₊ := by
  intro h
  have h3 := h 3 le_rfl
  rw [lly_positive_edge_connectivity_threshold_three] at h3
  norm_num at h3

import AFTD.Prelude

/-!
# closed_network_end_node_response_bound

Topic: quantum   Node: e3635fa2ec29

Provenance: helper lemma. arXiv:2610.35838 Eq. 30

For any real numbers s and t with |s| ≤ 1 and |t| ≤ 1, |s + t| / 2 + |s - t| / 2 ≤ 1.
-/

/-- Elementary bound on the sum of sum and difference absolute values for response variables in [-1, 1]. -/
theorem closed_network_end_node_response_bound
    (s t : ℝ) (hs : |s| ≤ 1) (ht : |t| ≤ 1) :
    |s + t| / 2 + |s - t| / 2 ≤ 1 := by
  have hs' := abs_le.mp hs
  have ht' := abs_le.mp ht
  rcases le_total 0 (s + t) with hst | hst
  · rcases le_total 0 (s - t) with hsub | hsub
    · rw [abs_of_nonneg hst, abs_of_nonneg hsub]
      linarith
    · rw [abs_of_nonneg hst, abs_of_nonpos hsub]
      linarith
  · rcases le_total 0 (s - t) with hsub | hsub
    · rw [abs_of_nonpos hst, abs_of_nonneg hsub]
      linarith
    · rw [abs_of_nonpos hst, abs_of_nonpos hsub]
      linarith

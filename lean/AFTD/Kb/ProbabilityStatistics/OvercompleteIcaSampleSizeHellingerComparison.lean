import AFTD.Prelude

/-!
# overcomplete_ica_sample_size_hellinger_comparison

Topic: estimation   Node: c8c256796b4e

Provenance: formalization of a published result. Source: arXiv:2611.11852 Sec. 2.2, eq. (3)

For all real numbers M_q and H_q_sq with 0 < M_q, if M_q / 4 ≤ H_q_sq and H_q_sq ≤ 2 * M_q, then 32 / M_q ≤ 64 / H_q_sq and 64 / H_q_sq ≤ 256 / M_q.
-/

/-- Sample size bounds in terms of the squared Hellinger distance H_q^2 and the amplitude second moment M_q are comparable. -/
theorem overcomplete_ica_sample_size_hellinger_comparison (M_q H_q_sq : ℝ) (h : M_q / 4 ≤ H_q_sq) (h2 : H_q_sq ≤ 2 * M_q) (hM : 0 < M_q) : 32 / M_q ≤ 64 / H_q_sq ∧ 64 / H_q_sq ≤ 256 / M_q := by
  have hH : 0 < H_q_sq := by linarith
  constructor
  · rw [div_le_div_iff₀ hM hH]
    linarith
  · rw [div_le_div_iff₀ hH hM]
    linarith

import AFTD.Prelude
import AFTD.Kb.Tcs.IsDichotomicObservable

/-!
# dichotomic_sum_diff_sq_sum

Topic: quantum   Node: befcb3f12170

Provenance: helper lemma. arXiv:2610.35838 App. E

For any two dichotomic projective observables B_0, B_1 on a Hilbert space, (B_0 + B_1)^2 + (B_0 - B_1)^2 = 4 I.
-/

/-- The sum of squares of B0 + B1 and B0 - B1 equals 4 times the identity. -/
theorem dichotomic_sum_diff_sq_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (B0 B1 : E →L[ℂ] E) (h0 : B0 ^ 2 = 1) (h1 : B1 ^ 2 = 1) : (B0 + B1) ^ 2 + (B0 - B1) ^ 2 = 4 • (1 : E →L[ℂ] E) := by
  have h : (B0 + B1) ^ 2 + (B0 - B1) ^ 2 = 2 * B0 ^ 2 + 2 * B1 ^ 2 := by
    noncomm_ring
  rw [h, h0, h1]
  norm_num

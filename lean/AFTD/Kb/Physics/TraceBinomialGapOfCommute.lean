import AFTD.Prelude
import AFTD.Kb.Physics.TraceBinomialGap

/-!
# trace_binomial_gap_of_commute

Topic: quantum_mechanics   Node: 069e17553887

Provenance: helper lemma. arXiv:2411.33774

For any natural number k and any two commuting complex d by d matrices A and B, the trace binomial gap Delta_k(A, B) is zero.
-/

/-- The trace binomial gap vanishes for commuting matrices. -/
theorem trace_binomial_gap_of_commute
    {d : ℕ} (k : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) (h : Commute A B) :
    traceBinomialGap k A B = 0 := by
  unfold traceBinomialGap
  have htrace : Matrix.trace ((A + B) ^ k) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * Matrix.trace (A ^ j * B ^ (k - j)) := by
    rw [h.add_pow k]
    rw [Matrix.trace_sum]
    congr 1
    ext j
    rw [← nsmul_eq_mul', Matrix.trace_smul, nsmul_eq_mul]
  rw [htrace, Complex.re_sum]
  have hterm : (fun j => (↑(k.choose j) * Matrix.trace (A ^ j * B ^ (k - j))).re) =
      (fun j => (k.choose j : ℝ) * (Matrix.trace (A ^ j * B ^ (k - j))).re) := by
    ext j
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [hterm]
  exact sub_self _

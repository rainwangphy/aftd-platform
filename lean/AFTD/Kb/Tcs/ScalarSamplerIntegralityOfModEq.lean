import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# scalar_sampler_integrality_of_modEq

Topic: information   Node: 200a8cc785df

Provenance: helper lemma. arXiv:2611.13281, Lemma 2.1 proof, step 1

If an integer B satisfies B ≡ -m_j * A (mod m_j^2) with m_j ≠ 0, then A / m_j + B / m_j^2 is an integer.
-/

/-- If B ≡ -m_j * A mod m_j^2, then A / m_j + B / m_j^2 is an integer. -/
theorem scalar_sampler_integrality_of_modEq (m_j A B : ℤ) (hm : m_j ≠ 0)
    (hB : B ≡ - m_j * A [ZMOD m_j^2]) :
    ∃ z : ℤ, (A : ℚ) / (m_j : ℚ) + (B : ℚ) / ((m_j : ℚ)^2) = (z : ℚ) := by
  rcases hB.dvd with ⟨k, hk⟩
  have hk' : m_j * A + B = m_j^2 * (-k) := by
    linarith
  refine ⟨-k, ?_⟩
  have hq : (m_j : ℚ) * (A : ℚ) + (B : ℚ) = (m_j : ℚ)^2 * (-(k : ℚ)) := by
    exact_mod_cast hk'
  field_simp [hm]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hq

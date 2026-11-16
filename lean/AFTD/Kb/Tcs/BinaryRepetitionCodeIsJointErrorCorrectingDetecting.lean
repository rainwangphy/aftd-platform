import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryRepetitionCode
import AFTD.Kb.Tcs.IsJointErrorCorrectingDetecting
import AFTD.Kb.Tcs.HammingDistBinaryZeroAddOne
import AFTD.Kb.Tcs.DisjointHammingBallHammingRingSame
import AFTD.Kb.Tcs.HammingRing
import AFTD.Kb.Tcs.HammingBall

/-!
# binary_repetition_code_is_joint_error_correcting_detecting

Topic: information   Node: 11a4b3d530f0

Provenance: helper lemma. arXiv:2611.18156 Theorem IV.3

For an explicit natural number n with 2 ≤ n and natural numbers c, c' such that 2 * c + c' + 1 = n, `binary_repetition_code n` is a (c, c') joint error-correcting and detecting code, that is, `is_joint_error_correcting_detecting c c' (binary_repetition_code n)` holds.
-/

private lemma binary_repetition_code_is_joint_error_correcting_detecting_dist_sum (n : ℕ)
    {x₁ x₂ : Fin n → Fin 2}
    (h₁ : x₁ ∈ binary_repetition_code n) (h₂ : x₂ ∈ binary_repetition_code n) (hne : x₁ ≠ x₂)
    (y : Fin n → Fin 2) : hammingDist x₁ y + hammingDist x₂ y = n := by
  simp only [binary_repetition_code, Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact absurd rfl hne
  · exact hamming_dist_binary_zero_add_one n y
  · have := hamming_dist_binary_zero_add_one n y
    omega
  · exact absurd rfl hne

/-- The binary repetition code of length n ≥ 2 is a (c, c') joint error-correcting and detecting code whenever 2c + c' + 1 = n. -/
lemma binary_repetition_code_is_joint_error_correcting_detecting (n c c' : ℕ) (hn : 2 ≤ n)
    (h_dim : 2 * c + c' + 1 = n) :
    is_joint_error_correcting_detecting c c' (binary_repetition_code n) := by
  constructor
  · intro x₁ h₁ x₂ h₂ hne
    rw [Finset.disjoint_left]
    intro y hy₁ hy₂
    simp only [hamming_ball, Finset.mem_filter, Finset.mem_univ, true_and] at hy₁ hy₂
    have e := binary_repetition_code_is_joint_error_correcting_detecting_dist_sum n h₁ h₂ hne y
    omega
  · intro x₁ h₁ x₂ h₂
    by_cases h : x₁ = x₂
    · subst h
      exact disjoint_hamming_ball_hamming_ring_same c c' x₁
    · rw [Finset.disjoint_left]
      intro y hy₁ hy₂
      simp only [hamming_ball, Finset.mem_filter, Finset.mem_univ, true_and] at hy₁
      simp only [hamming_ring, Finset.mem_filter, Finset.mem_univ, true_and] at hy₂
      have e := binary_repetition_code_is_joint_error_correcting_detecting_dist_sum n h₁ h₂ h y
      omega

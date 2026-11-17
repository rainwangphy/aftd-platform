import AFTD.Prelude

/-!
# dichotomic_sum_diff_anticommute

Topic: quantum   Node: 47855684548a

Provenance: helper lemma. arXiv:2610.35838 Appendix E

For any two elements B_0, B_1 in a ring R satisfying B_0^2 = 1 and B_1^2 = 1, the sum B_0 + B_1 and the difference B_0 - B_1 anticommute: (B_0 + B_1)(B_0 - B_1) + (B_0 - B_1)(B_0 + B_1) = 0.
-/

/-- For any two operators squaring to 1 in a ring, their sum and difference anticommute. -/
theorem dichotomic_sum_diff_anticommute {R : Type*} [Ring R] (B₀ B₁ : R)
    (h₀ : B₀ ^ 2 = 1) (h₁ : B₁ ^ 2 = 1) :
    (B₀ + B₁) * (B₀ - B₁) + (B₀ - B₁) * (B₀ + B₁) = 0 := by
  rw [sq] at h₀ h₁
  calc
    (B₀ + B₁) * (B₀ - B₁) + (B₀ - B₁) * (B₀ + B₁)
      = 2 • (B₀ * B₀) + -2 • (B₁ * B₁) := by noncomm_ring
    _ = 2 • (1 : R) + -2 • (1 : R) := by rw [h₀, h₁]
    _ = 0 := by abel

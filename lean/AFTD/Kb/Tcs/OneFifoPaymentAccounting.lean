import AFTD.Prelude

/-!
# one_fifo_payment_accounting

Topic: online_algorithms   Node: 0a1a8e091fed

Provenance: formalization of a published result. Source: arXiv:2610.18767 Lemma 3.4

For all natural numbers k, P, and F_opt, every real number D_opt, and all natural numbers phi_0 and phi_final, if phi_0 = 0 and (P : ℝ) + (phi_final : ℝ) - (phi_0 : ℝ) ≤ (k + 1 : ℝ) * (F_opt : ℝ) + (k + 1 : ℝ) * D_opt, then (P : ℝ) ≤ (k + 1 : ℝ) * ((F_opt : ℝ) + D_opt).
-/

/-- Number of payments of 1-FIFO is at most (k+1) times offline cost. -/
theorem one_fifo_payment_accounting (k : ℕ) (P : ℕ) (F_opt : ℕ) (D_opt : ℝ) (phi_0 phi_final : ℕ) (h_phi_0 : phi_0 = 0) (h_acc : (P : ℝ) + (phi_final : ℝ) - (phi_0 : ℝ) ≤ (k + 1 : ℝ) * (F_opt : ℝ) + (k + 1 : ℝ) * D_opt) : (P : ℝ) ≤ (k + 1 : ℝ) * ((F_opt : ℝ) + D_opt) := by
  have h_phi_final : (phi_final : ℝ) ≥ 0 := Nat.cast_nonneg phi_final
  rw [mul_add]
  subst h_phi_0
  simp only [Nat.cast_zero, sub_zero] at h_acc
  linarith

import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsSeparable

/-!
# product_witness_negative_expectation_implies_entangled

Topic: quantum   Node: 63ce6212a92b

Provenance: helper lemma. Product-witness reduction for OP-2299.

A product-positive witness with negative expectation on a matrix proves that the matrix is not separable.
-/

open scoped BigOperators

theorem product_witness_negative_expectation_implies_entangled
    (dA dB : ℕ) (W ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hw : ∀ (x : Fin dA → ℂ) (y : Fin dB → ℂ),
      0 ≤ (∑ p : Fin dA × Fin dB, ∑ q : Fin dA × Fin dB,
        star (x p.1 * y p.2) * W p q * (x q.1 * y q.2)).re)
    (hneg : (∑ p : Fin dA × Fin dB, ∑ q : Fin dA × Fin dB, W p q * ρ q p).re < 0) :
    ¬ matrix_is_separable dA dB ρ := by
  intro ⟨N, x, y, hρ⟩
  have hswap (i : Fin N) (p q : Fin dA × Fin dB) :
      W p q * (x i q.1 * star (x i p.1) * (y i q.2 * star (y i p.2))) =
      star (x i p.1 * y i p.2) * W p q * (x i q.1 * y i q.2) := by
    simp only [star_mul]
    ring
  have heq : (∑ p : Fin dA × Fin dB, ∑ q : Fin dA × Fin dB, W p q * ρ q p) =
      ∑ i : Fin N, ∑ p : Fin dA × Fin dB, ∑ q : Fin dA × Fin dB,
        star (x i p.1 * y i p.2) * W p q * (x i q.1 * y i q.2) := by
    calc
      _ = ∑ p : Fin dA × Fin dB, ∑ q : Fin dA × Fin dB, ∑ i : Fin N,
          W p q * (x i q.1 * star (x i p.1) * (y i q.2 * star (y i p.2))) := by
            simp_rw [hρ, Finset.mul_sum]
      _ = ∑ p : Fin dA × Fin dB, ∑ i : Fin N, ∑ q : Fin dA × Fin dB,
          W p q * (x i q.1 * star (x i p.1) * (y i q.2 * star (y i p.2))) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.sum_comm]
      _ = ∑ i : Fin N, ∑ p : Fin dA × Fin dB, ∑ q : Fin dA × Fin dB,
          W p q * (x i q.1 * star (x i p.1) * (y i q.2 * star (y i p.2))) := by
            rw [Finset.sum_comm]
      _ = _ := by simp_rw [hswap]
  have hn : 0 ≤ ∑ i : Fin N, (∑ p : Fin dA × Fin dB, ∑ q : Fin dA × Fin dB,
        star (x i p.1 * y i p.2) * W p q * (x i q.1 * y i q.2)).re := by
    exact Finset.sum_nonneg fun i _ => hw (x i) (y i)
  have hh := congrArg Complex.re heq
  simp only [Complex.re_sum] at hh hneg hn
  linarith

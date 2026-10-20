import AFTD.Prelude

/-!
# saddle_gap_self_payoff_ge_two_v_of_sub_ge

Topic: equilibria   Node: ca5021958c07

Provenance: helper lemma. arXiv:2610.25524 Lemma 4.2

For an n-by-n matrix A with nonnegative entries, probability vectors a and b in `stdSimplex ℝ (Fin n)`, and real number v, if `Matrix.vecMul a.val A k - Matrix.mulVec A b.val k ≥ v` for all k in Fin n, then `dotProduct a.val (Matrix.mulVec A a.val) ≥ 2 * v`.
-/

/-- Averaging the saddle-gap marginal difference inequality over a and b yields the self-payoff bound aᵀ A a ≥ 2v. -/
lemma saddle_gap_self_payoff_ge_two_v_of_sub_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA_nonneg : ∀ i j, 0 ≤ A i j) (a b : stdSimplex ℝ (Fin n)) (v : ℝ) (h : ∀ k : Fin n, Matrix.vecMul a.val A k - Matrix.mulVec A b.val k ≥ v) : dotProduct a.val (Matrix.mulVec A a.val) ≥ 2 * v := by
  have h_dot (p : stdSimplex ℝ (Fin n)) :
      v ≤ dotProduct p.val (fun k => Matrix.vecMul a.val A k - Matrix.mulVec A b.val k) := by
    have hp_nonneg : ∀ k, 0 ≤ p.val k := p.2.1
    have hp_sum : ∑ k, p.val k = 1 := p.2.2
    have h1 : ∑ k, p.val k * v ≤ ∑ k, p.val k * (Matrix.vecMul a.val A k - Matrix.mulVec A b.val k) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (h k) (hp_nonneg k)
    have h2 : ∑ k, p.val k * v = (∑ k, p.val k) * v := (Finset.sum_mul _ _ _).symm
    rw [hp_sum, one_mul] at h2
    unfold dotProduct
    linarith
  have h_sub (p : stdSimplex ℝ (Fin n)) :
      dotProduct p.val (fun k => Matrix.vecMul a.val A k - Matrix.mulVec A b.val k) =
        dotProduct p.val (Matrix.vecMul a.val A) - dotProduct p.val (Matrix.mulVec A b.val) := by
    have : (fun k => Matrix.vecMul a.val A k - Matrix.mulVec A b.val k) =
        Matrix.vecMul a.val A - Matrix.mulVec A b.val := rfl
    rw [this]
    exact dotProduct_sub p.val (Matrix.vecMul a.val A) (Matrix.mulVec A b.val)
  have ha : v ≤ dotProduct a.val (Matrix.vecMul a.val A) - dotProduct a.val (Matrix.mulVec A b.val) := by
    rw [← h_sub a]
    exact h_dot a
  have hb : v ≤ dotProduct b.val (Matrix.vecMul a.val A) - dotProduct b.val (Matrix.mulVec A b.val) := by
    rw [← h_sub b]
    exact h_dot b
  have h_comm1 : dotProduct a.val (Matrix.vecMul a.val A) = dotProduct a.val (Matrix.mulVec A a.val) := by
    rw [dotProduct_comm]
    exact (Matrix.dotProduct_mulVec a.val A a.val).symm
  have h_comm2 : dotProduct b.val (Matrix.vecMul a.val A) = dotProduct a.val (Matrix.mulVec A b.val) := by
    rw [dotProduct_comm]
    exact (Matrix.dotProduct_mulVec a.val A b.val).symm
  have hb_nonneg : 0 ≤ dotProduct b.val (Matrix.mulVec A b.val) := by
    unfold dotProduct Matrix.mulVec
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (b.2.1 i)
    unfold dotProduct
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hA_nonneg i j) (b.2.1 j)
  rw [h_comm1] at ha
  rw [h_comm2] at hb
  linarith

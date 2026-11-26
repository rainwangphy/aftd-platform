import AFTD.Prelude
import AFTD.Kb.Tcs.QutritPhaseRoot
import AFTD.Kb.Tcs.QutritCyclicCubicNonnegative
import AFTD.Kb.Tcs.QutritZeroBellCyclicTwoCopySos
import AFTD.Kb.Tcs.QutritCyclicFaceSosTerms

/-!
# qutrit_zero_bell_cyclic_product_inequality

Topic: quantum   Node: 3be9cfcbd5ad

Provenance: helper lemma. OP-2299 zero-Bell face witness; exact projected determinant computation 41055.

On the product-state face with one maximally entangled overlap zero, the overlap at one other basis state is bounded by the next overlap plus the mass in the opposite shift row.
-/

theorem qutrit_zero_bell_cyclic_product_inequality
    (x y : Fin 3 → ℂ)
    (hzero : x 0*y 1 + qutrit_phase_root*x 1*y 2 + qutrit_phase_root^2*x 2*y 0 = 0) :
    Complex.normSq (x 0*y 1 + x 1*y 2 + x 2*y 0) ≤
    Complex.normSq (x 0*y 1 + qutrit_phase_root^2*x 1*y 2 + qutrit_phase_root*x 2*y 0) +
    3*(Complex.normSq (x 0*y 2) + Complex.normSq (x 1*y 0) + Complex.normSq (x 2*y 1)) := by
  have hsos := qutrit_zero_bell_cyclic_two_copy_sos x y hzero
  have hs : 0 ≤ ∑ i : Fin 3, Complex.normSq (y i) := Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  by_cases hs0 : (∑ i : Fin 3, Complex.normSq (y i)) = 0
  · simp only [Fin.sum_univ_three] at hs0
    have h0 : Complex.normSq (y 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (y 0), Complex.normSq_nonneg (y 1), Complex.normSq_nonneg (y 2)]
    have h1 : Complex.normSq (y 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (y 0), Complex.normSq_nonneg (y 1), Complex.normSq_nonneg (y 2)]
    have h2 : Complex.normSq (y 2) = 0 := by
      nlinarith [Complex.normSq_nonneg (y 0), Complex.normSq_nonneg (y 1), Complex.normSq_nonneg (y 2)]
    have hy0 := Complex.normSq_eq_zero.mp h0
    have hy1 := Complex.normSq_eq_zero.mp h1
    have hy2 := Complex.normSq_eq_zero.mp h2
    simp [hy0, hy1, hy2]
  · have hspos : 0 < ∑ i : Fin 3, Complex.normSq (y i) := lt_of_le_of_ne hs (Ne.symm hs0)
    have hmul : 0 ≤ (∑ i : Fin 3, Complex.normSq (y i)) *
        ((-Complex.normSq (x 0*y 1+x 1*y 2+x 2*y 0) +
           Complex.normSq (x 0*y 1+qutrit_phase_root^2*x 1*y 2+qutrit_phase_root*x 2*y 0))/3 +
          ∑ i : Fin 3, Complex.normSq (x i*y (i+2))) := by
      rw [hsos]
      exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
    have hf := (mul_nonneg_iff_of_pos_left hspos).mp hmul
    simp only [Fin.sum_univ_three, Fin.reduceAdd] at hf
    nlinarith [hf]

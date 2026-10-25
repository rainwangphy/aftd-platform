import AFTD.Prelude
import AFTD.Kb.Optimization.MultilinearExtension

/-!
# multilinear_extension_nonneg

Topic: submodular   Node: d71944075b7a

Provenance: helper lemma. step towards matroid_symmetry_gap_integral_lt_eight_seventeenths

The multilinear extension of a non-negative set function evaluated on the unit hypercube is non-negative.
-/

/-- The multilinear extension of a non-negative set function evaluated on the unit hypercube is non-negative. -/
theorem multilinear_extension_nonneg {m : ℕ} (f : Finset (Fin m) → ℝ) (hf : ∀ S, 0 ≤ f S) (x : Fin m → ℝ) (hx : ∀ u, 0 ≤ x u ∧ x u ≤ 1) : 0 ≤ multilinear_extension f x := by
  unfold multilinear_extension
  apply Finset.sum_nonneg
  intro S hS
  apply mul_nonneg
  · apply mul_nonneg
    · exact hf S
    · apply Finset.prod_nonneg
      intro u hu
      exact (hx u).1
  · apply Finset.prod_nonneg
    intro u hu
    have := (hx u).2
    linarith

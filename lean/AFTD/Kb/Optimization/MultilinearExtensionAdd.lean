import AFTD.Prelude
import AFTD.Kb.Optimization.MultilinearExtension

/-!
# multilinear_extension_add

Topic: submodular   Node: 90ac25cffa34

Provenance: helper lemma. step towards matroid_symmetry_gap_integral_lt_eight_seventeenths

The multilinear extension of a sum of set functions is the sum of their multilinear extensions.
-/

/-- The multilinear extension of a sum of set functions is the sum of their multilinear extensions. -/
theorem multilinear_extension_add {m : ℕ} (f g : Finset (Fin m) → ℝ) (x : Fin m → ℝ) : multilinear_extension (f + g) x = multilinear_extension f x + multilinear_extension g x := by
  unfold multilinear_extension
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  simp only [Pi.add_apply]
  ring

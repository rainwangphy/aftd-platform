import AFTD.Prelude
import AFTD.Kb.Optimization.MultilinearExtension

/-!
# multilinear_extension_smul

Topic: submodular   Node: bdf9f418cb16

Provenance: helper lemma. step towards matroid_symmetry_gap_integral_lt_eight_seventeenths

The multilinear extension commutes with scalar multiplication.
-/

/-- The multilinear extension commutes with scalar multiplication. -/
theorem multilinear_extension_smul {m : ℕ} (c : ℝ) (f : Finset (Fin m) → ℝ) (x : Fin m → ℝ) : multilinear_extension (c • f) x = c * multilinear_extension f x := by
  simp only [multilinear_extension, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

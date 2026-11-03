import AFTD.Prelude

/-!
# op826_envelope_perfect_square

Topic: fair_division   Node: b69c256073cf

Provenance: helper lemma. arXiv:2610.34625

For any positive integer k, when the value ratio is a perfect square R = k^2, the conjectured envelope min (1 / floor(sqrt(k^2))) (ceil(sqrt(k^2)) / k^2) equals 1 / k.
-/

/-- Evaluation of the discrete EFX envelope at perfect squares R = k^2 yields 1 / k. -/
theorem op826_envelope_perfect_square (k : ℕ) (hk : 1 ≤ k) :
    min (1 / (⌊Real.sqrt ((k : ℝ) ^ 2)⌋ : ℝ)) ((⌈Real.sqrt ((k : ℝ) ^ 2)⌉ : ℝ) / ((k : ℝ) ^ 2)) = 1 / (k : ℝ) := by
  have hkpos : (0:ℝ) < k := by
    have : (0:ℕ) < k := hk
    exact_mod_cast this
  have hsqrt : Real.sqrt ((k : ℝ) ^ 2) = (k:ℝ) := Real.sqrt_sq (le_of_lt hkpos)
  rw [hsqrt, Int.floor_natCast, Int.ceil_natCast]
  push_cast
  have hdiv : (k:ℝ) / ((k:ℝ) ^ 2) = 1 / (k:ℝ) := by
    field_simp
  rw [hdiv, min_self]

import AFTD.Prelude

/-!
# finite_variance_recurrence_additive

Topic: combinatorics   Node: fc82e8759938

Provenance: helper lemma. Component decomposition for op_1355_clique_components_variance_ge_bound.

If partition functions and the first two unnormalized moments satisfy the independent-component recurrences with nonzero denominators, the total variance is the sum of the component variances.
-/

open scoped Classical

theorem finite_variance_recurrence_additive {C : Type*} [DecidableEq C]
    (Z A B : Finset C → ℝ) (s m₁ m₂ : C → ℝ)
    (hZ : ∀ T, Z T ≠ 0) (hs : ∀ c, 1 + s c ≠ 0)
    (hbase : A ∅ = 0 ∧ B ∅ = 0)
    (hZstep : ∀ c T, c ∉ T → Z (insert c T) = (1+s c) * Z T)
    (hAstep : ∀ c T, c ∉ T → A (insert c T) = (1+s c) * A T + m₁ c * Z T)
    (hBstep : ∀ c T, c ∉ T → B (insert c T) = (1+s c) * B T + 2 * m₁ c * A T + m₂ c * Z T)
    (T : Finset C) :
    B T / Z T - (A T / Z T)^2 = ∑ c ∈ T, (m₂ c / (1+s c) - (m₁ c / (1+s c))^2) := by
  induction T using Finset.induction_on with
  | empty => simp [hbase.1, hbase.2]
  | @insert c T hc ih =>
    rw [hZstep c T hc, hAstep c T hc, hBstep c T hc, Finset.sum_insert hc]
    have hstep : ((1+s c) * B T + 2 * m₁ c * A T + m₂ c * Z T) / ((1+s c) * Z T) -
        (((1+s c) * A T + m₁ c * Z T) / ((1+s c) * Z T))^2 =
        (B T / Z T - (A T / Z T)^2) + (m₂ c / (1+s c) - (m₁ c / (1+s c))^2) := by
      have h1 : (1 + s c) * Z T ≠ 0 := mul_ne_zero (hs c) (hZ T)
      field_simp [hZ T, hs c]
      ring
    rw [hstep, ih]
    ring

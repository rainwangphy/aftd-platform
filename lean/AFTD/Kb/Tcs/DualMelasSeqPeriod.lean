import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasSeq

/-!
# dual_melas_seq_period

Topic: information   Node: cd22db302f73

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For a field F finite-dimensional over ZMod 2, a natural number k, elements α, c ∈ F such that α has order 2^k - 1, and index i, dual_melas_seq α c (i + (2^k - 1)) = dual_melas_seq α c i.
-/

/-- The dual Melas binary trace sequence has period 2^k - 1 when α is a primitive root of order 2^k - 1. -/
theorem dual_melas_seq_period {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (k : ℕ) (α c : F) (hprim : IsPrimitiveRoot α (2 ^ k - 1)) (i : ℕ) :
    dual_melas_seq α c (i + (2 ^ k - 1)) = dual_melas_seq α c i := by
  have hα : α ^ (2 ^ k - 1) = 1 := hprim.pow_eq_one
  have hinv : (α⁻¹) ^ (2 ^ k - 1) = 1 := by rw [inv_pow, hα, inv_one]
  have e1 : α ^ (i + (2 ^ k - 1)) = α ^ i := by rw [pow_add, hα, mul_one]
  have e2 : (α⁻¹) ^ (i + (2 ^ k - 1)) = (α⁻¹) ^ i := by rw [pow_add, hinv, mul_one]
  simp only [dual_melas_seq, e1, e2]

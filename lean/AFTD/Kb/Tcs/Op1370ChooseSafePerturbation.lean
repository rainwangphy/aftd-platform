import AFTD.Prelude

/-!
# op1370_choose_safe_perturbation

Topic: combinatorics   Node: d13cc4cd24e9

Provenance: helper lemma.

An infinite field admits a nonzero perturbation avoiding both a singular update and a zero reciprocal weight.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_choose_safe_perturbation
    {K : Type*} [Field K] [Infinite K] (q u d : K) (hd : d ≠ 0) :
    ∃ t : K, t ≠ 0 ∧ 1 + t * q ≠ 0 ∧ u + t * d ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := ({0, -q⁻¹, -u / d} : Finset K).exists_notMem
  have ht0 : t ≠ 0 := by
    intro h
    exact ht (by simp [h])
  have htq : t ≠ -q⁻¹ := by
    intro h
    exact ht (by simp [h])
  have htd : t ≠ -u / d := by
    intro h
    exact ht (by simp [h])
  refine ⟨t, ht0, ?_, ?_⟩
  · intro he
    have hq : q ≠ 0 := by
      intro hq
      simp [hq] at he
    apply htq
    apply mul_right_cancel₀ hq
    have hp : t * q = -1 := by linear_combination he
    rw [hp, neg_mul, inv_mul_cancel₀ hq]
  · intro he
    apply htd
    apply mul_right_cancel₀ hd
    have hp : t * d = -u := by linear_combination he
    rw [hp]
    field_simp

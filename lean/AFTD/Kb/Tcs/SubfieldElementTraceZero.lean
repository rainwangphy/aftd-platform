import AFTD.Prelude

/-!
# subfield_element_trace_zero

Topic: cryptography   Node: 8a92cde67978

Provenance: helper lemma. arXiv:2611.10269 Sec. 7

Let E be a finite field of characteristic 2 with 2^(2m) elements. Then the absolute trace of any element t in E satisfying t^(2^m) = t is zero in ZMod 2.
-/

/-- The absolute trace from an even-degree extension E of F_{2^m} vanishes on the subfield F_{2^m}. -/
theorem subfield_element_trace_zero {E : Type*} [Field E] [Fintype E] [Algebra (ZMod 2) E] (m : ℕ) (hcard : Fintype.card E = 2 ^ (2 * m)) (t : E) (ht : t ^ (2 ^ m) = t) : Algebra.trace (ZMod 2) E t = 0 := by
  have hrank : Module.finrank (ZMod 2) E = 2 * m := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := E)
    rw [ZMod.card, hcard] at h
    exact Nat.pow_right_injective (by norm_num) h.symm
  have htrace := FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) E t
  have hcard2 : Nat.card (ZMod 2) = 2 := by simp
  rw [hrank, hcard2] at htrace
  have hsum : ∑ i ∈ Finset.range (2 * m), t ^ (2 ^ i) = 0 := by
    have h2m : 2 * m = m + m := two_mul m
    rw [h2m, Finset.sum_range_add]
    have h_eq : ∑ x ∈ Finset.range m, t ^ (2 ^ (m + x)) = ∑ x ∈ Finset.range m, t ^ (2 ^ x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_add, pow_mul, ht]
    rw [h_eq]
    have h2 : (2 : E) = 0 := by
      have h : (2 : E) = algebraMap (ZMod 2) E (2 : ZMod 2) := (map_ofNat (algebraMap (ZMod 2) E) 2).symm
      rw [h]
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, map_zero]
    have h_add : ∀ s : E, s + s = 0 := by
      intro s
      calc s + s = 2 * s := (two_mul s).symm
      _ = 0 * s := by rw [h2]
      _ = 0 := zero_mul s
    exact h_add _
  rw [hsum] at htrace
  have hinj := FaithfulSMul.algebraMap_injective (ZMod 2) E
  exact hinj (by simp [htrace])

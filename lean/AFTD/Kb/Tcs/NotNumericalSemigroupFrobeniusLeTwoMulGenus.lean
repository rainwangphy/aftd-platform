import AFTD.Prelude
import AFTD.Kb.Tcs.NumericalSemigroup
import AFTD.Kb.Tcs.NumericalSemigroupFrobeniusNumber
import AFTD.Kb.Tcs.NumericalSemigroupGenus

/-!
# not_numerical_semigroup_frobenius_le_two_mul_genus

Topic: combinatorics   Node: 6e65c3877b14

Provenance: original. Related work: refutes `numerical_semigroup_frobenius_le_two_mul_genus`

The statement `numerical_semigroup_frobenius_le_two_mul_genus` is false: The structure NumericalSemigroup only requires the complement of the underlying AddSubmonoid to be finite, so S = ℕ (i.e. ⊤ as an AddSubmonoid of ℕ) is a valid numerical semigroup. Its complement is empty, hence numerical_semigroup_frobenius_number S = sSup ∅ = 0 and numerical_semigroup_genus S = ncard ∅ = 0. Taking F = g = 0 the hypotheses hold but the conclusion becomes 0 + 1 ≤ 2 * 0, i.e. 1 ≤ 0, which is false. The classical bound F + 1 ≤ 2g requires the complement to be nonempty (equivalently F > 0, i.e. S ≠ ℕ).
-/

theorem not_numerical_semigroup_frobenius_le_two_mul_genus : ¬ (∀ (S : NumericalSemigroup) (F g : ℕ)
    (h_frob : numerical_semigroup_frobenius_number S = F)
    (h_gen : numerical_semigroup_genus S = g), F + 1 ≤ 2 * g) := by
  rintro h
  have hce : ∃ S : NumericalSemigroup,
      numerical_semigroup_frobenius_number S = 0 ∧ numerical_semigroup_genus S = 0 := by
    refine ⟨⟨⊤, ?_⟩, ?_, ?_⟩
    · simp
    · simp [numerical_semigroup_frobenius_number]
    · simp [numerical_semigroup_genus]
  obtain ⟨S, hf, hg⟩ := hce
  have h1 := h S 0 0 hf hg
  omega

import AFTD.Prelude
import AFTD.Kb.Tcs.NumericalSemigroupCount
import AFTD.Kb.Tcs.NumericalSemigroupNotDvdFrobenius
import AFTD.Kb.Tcs.NumericalSemigroupMultiplicity
import AFTD.Kb.Tcs.NumericalSemigroupFrobeniusNumber
import AFTD.Kb.Tcs.NumericalSemigroup
import AFTD.Kb.Tcs.NumericalSemigroupGenus

/-!
# numerical_semigroup_count_of_dvd_frobenius

Topic: combinatorics   Node: a90a7f7cf0b7

Provenance: helper lemma. arXiv:2611.11559 Section 2

If F is a positive integer and m divides F, then the number of numerical semigroups with Frobenius number F, multiplicity m, and genus g is 0.
-/

/-- No numerical semigroup has multiplicity dividing its positive Frobenius number, so the count is zero. -/
theorem numerical_semigroup_count_of_dvd_frobenius (F m g : ℕ) (hF : 0 < F) (hdvd : m ∣ F) :
    numerical_semigroup_count F m g = 0 := by
  unfold numerical_semigroup_count
  have hempty : {S : NumericalSemigroup | numerical_semigroup_frobenius_number S = F ∧
      numerical_semigroup_multiplicity S = m ∧ numerical_semigroup_genus S = g} = ∅ := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hf, hm, _⟩
    exact numerical_semigroup_not_dvd_frobenius S F m hF hf hm hdvd
  rw [hempty, Set.ncard_empty]

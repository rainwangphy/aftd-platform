import AFTD.Prelude
import AFTD.Kb.Tcs.FibonacciAttractorBasis
import AFTD.Kb.Tcs.IsStringAttractor
import AFTD.Kb.Tcs.WordOccurrenceCoverage
import AFTD.Kb.Tcs.WordMinFactorCoverages
import AFTD.Kb.Tcs.IsStringAttractorIffForallMinFactorCoverage
import AFTD.Kb.Tcs.FibonacciWord

/-!
# fibonacci_string_attractor_iff_meets_basis

Topic: combinatorics   Node: 9aa0b865017f

Provenance: helper lemma. arXiv:2610.10950 Smallest String Attractors and Minimal Coverage Certificates of Thue--Morse Words

For any natural number n, assuming the inclusion-minimal factor coverages of F_n are exactly the coverages of the basis B_n (word_min_factor_coverages (fibonacci_word n) = {word_occurrence_coverage (fibonacci_word n) u | u ∈ fibonacci_attractor_basis n}), a position set Γ ⊆ [1, |F_n|] is a string attractor of F_n if and only if Γ intersects the occurrence coverage word_occurrence_coverage (fibonacci_word n) u for every basis word u ∈ fibonacci_attractor_basis n.
-/

/-- If the minimal factor coverages of F_n are the coverages of B_n, then Γ is a string attractor iff Γ meets every coverage in B_n. -/
theorem fibonacci_string_attractor_iff_meets_basis (n : ℕ)
    (hbasis : word_min_factor_coverages (fibonacci_word n) =
      {word_occurrence_coverage (fibonacci_word n) u | u ∈ fibonacci_attractor_basis n})
    (Γ : Finset ℕ) (hΓ : Γ ⊆ Finset.Icc 1 (fibonacci_word n).length) :
    is_string_attractor (fibonacci_word n) Γ ↔
      ∀ u ∈ fibonacci_attractor_basis n, (Γ ∩ word_occurrence_coverage (fibonacci_word n) u).Nonempty := by
  rw [is_string_attractor_iff_forall_min_factor_coverage _ _ hΓ, hbasis]
  refine ⟨fun h u hu => h _ ⟨u, hu, rfl⟩, ?_⟩
  rintro h C ⟨u, hu, rfl⟩
  exact h u hu

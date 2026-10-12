import AFTD.Prelude
import AFTD.Kb.Tcs.IsStringAttractor
import AFTD.Kb.Tcs.WordMinFactorCoverages
import AFTD.Kb.Tcs.ExistsMinFactorCoverageSubset
import AFTD.Kb.Tcs.WordFactorCoverages
import AFTD.Kb.Tcs.WordOccurrenceCoverage

/-!
# is_string_attractor_iff_forall_min_factor_coverage

Topic: combinatorics   Node: 7c8170a7cbce

Provenance: formalization of a published result. Source: arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Proposition 3.2 (minimal-coverage reduction).

For every finite word w and every Γ ⊆ [1, |w|], Γ is a string attractor of w if and only if Γ ∩ C ≠ ∅ for every inclusion-minimal factor coverage C ∈ H_min(w).
-/

theorem is_string_attractor_iff_forall_min_factor_coverage {α : Type*} [DecidableEq α]
    (w : List α) (Γ : Finset ℕ) (hΓ : Γ ⊆ Finset.Icc 1 w.length) :
    is_string_attractor w Γ ↔ ∀ C ∈ word_min_factor_coverages w, (Γ ∩ C).Nonempty := by
  constructor
  · rintro ⟨-, h⟩ C ⟨⟨x, hx, hxw, rfl⟩, -⟩
    exact h x hx hxw
  · intro h
    refine ⟨hΓ, fun x hx hxw => ?_⟩
    obtain ⟨C, hC, hCD⟩ := exists_min_factor_coverage_subset w ⟨x, hx, hxw, rfl⟩
    obtain ⟨p, hp⟩ := h C hC
    exact ⟨p, Finset.inter_subset_inter_left hCD hp⟩

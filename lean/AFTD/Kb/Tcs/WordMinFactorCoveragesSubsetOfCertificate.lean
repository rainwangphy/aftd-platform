import AFTD.Prelude
import AFTD.Kb.Tcs.IsStringAttractor
import AFTD.Kb.Tcs.WordMinFactorCoverages
import AFTD.Kb.Tcs.WordOccurrenceCoverageSubset
import AFTD.Kb.Tcs.WordFactorCoverages
import AFTD.Kb.Tcs.WordOccurrenceCoverage

/-!
# word_min_factor_coverages_subset_of_certificate

Topic: combinatorics   Node: a56efba5eff6

Provenance: formalization of a published result. Source: arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Lemma 6.9 (canonical irredundancy). The proof here takes Γ = [1,|w|] \ C instead of one chosen point per member of F.

Let F ⊆ H(w) be a family of factor coverages such that for every Γ ⊆ [1, |w|], Γ is a string attractor of w iff Γ meets every member of F. Then H_min(w) ⊆ F: every exact certificate contains all inclusion-minimal coverages.
-/

theorem word_min_factor_coverages_subset_of_certificate {α : Type*} [DecidableEq α]
    (w : List α) (F : Set (Finset ℕ)) (hF : F ⊆ word_factor_coverages w)
    (hcert : ∀ Γ ⊆ Finset.Icc 1 w.length,
      is_string_attractor w Γ ↔ ∀ C ∈ F, (Γ ∩ C).Nonempty) :
    word_min_factor_coverages w ⊆ F := by
  intro C hC
  by_contra hCF
  obtain ⟨⟨x, hx, hxw, hxC⟩, hmin⟩ := hC
  have hΓ : Finset.Icc 1 w.length \ C ⊆ Finset.Icc 1 w.length := Finset.sdiff_subset
  have hatt : is_string_attractor w (Finset.Icc 1 w.length \ C) := by
    rw [hcert _ hΓ]
    intro D hD
    obtain ⟨y, hy, hyw, rfl⟩ := hF hD
    have hnot : ¬ word_occurrence_coverage w y ⊆ C := by
      intro hsub
      have := hmin _ ⟨y, hy, hyw, rfl⟩ hsub
      exact hCF (this ▸ hD)
    obtain ⟨p, hpD, hpC⟩ := Finset.not_subset.1 hnot
    exact ⟨p, Finset.mem_inter.2
      ⟨Finset.mem_sdiff.2 ⟨word_occurrence_coverage_subset w y hpD, hpC⟩, hpD⟩⟩
  obtain ⟨p, hp⟩ := hatt.2 x hx hxw
  rw [hxC, Finset.mem_inter, Finset.mem_sdiff] at hp
  exact hp.1.2 hp.2

import AFTD.Prelude
import AFTD.Kb.Tcs.WordMinFactorCoverages
import AFTD.Kb.Tcs.WordFactorCoverages

/-!
# exists_min_factor_coverage_subset

Topic: combinatorics   Node: 51e62d3dddc7

Provenance: helper lemma. Helper for arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Proposition 3.2 (every member of the finite family H(w) lies above a minimal one).

Every factor coverage D ∈ H(w) contains some inclusion-minimal factor coverage C ∈ H_min(w).
-/

theorem exists_min_factor_coverage_subset {α : Type*} [DecidableEq α] (w : List α)
    {D : Finset ℕ} (hD : D ∈ word_factor_coverages w) :
    ∃ C ∈ word_min_factor_coverages w, C ⊆ D := by
  obtain ⟨C, ⟨hCH, hCD⟩, hmin⟩ := (measure Finset.card).wf.has_min
    {C | C ∈ word_factor_coverages w ∧ C ⊆ D} ⟨D, hD, subset_rfl⟩
  refine ⟨C, ⟨hCH, fun E hE hEC => ?_⟩, hCD⟩
  by_contra hne
  exact hmin E ⟨hE, hEC.trans hCD⟩ (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hEC, hne⟩))

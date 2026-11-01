import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# exists_minimally_envied_subset

Topic: fair_division   Node: a45b78644d7f

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Standard minimal-envied-subset mechanism, arXiv:2002.05119v3 Observation 6 and Corollary 7; no novelty claim.

Given a real additive valuation profile, a real utility threshold for each agent, and a finite bundle envied by some agent relative to those thresholds, there is a subset still strictly envied by some agent such that deleting any of its goods leaves value at most the threshold for every agent.
-/

open Function Finset

theorem exists_minimally_envied_subset {m n : ℕ} (u : Fin n → Fin m → ℝ)
    (b : Fin n → ℝ) (S : Finset (Fin m))
    (h : ∃ i, b i < additive_valuation (u i) S) :
    ∃ T ⊆ S, (∃ j, b j < additive_valuation (u j) T) ∧
      ∀ i, ∀ g ∈ T, additive_valuation (u i) (T.erase g) ≤ b i := by
  classical
  revert h
  refine Finset.strongInductionOn S ?_
  intro S ih h
  by_cases hmin : ∀ i, ∀ g ∈ S, additive_valuation (u i) (S.erase g) ≤ b i
  · exact ⟨S, Finset.Subset.refl _, h, hmin⟩
  · push Not at hmin
    obtain ⟨i, g, hg, hgt⟩ := hmin
    obtain ⟨T, hT, henv, htrim⟩ := ih (S.erase g) (Finset.erase_ssubset hg) ⟨i, hgt⟩
    exact ⟨T, hT.trans (Finset.erase_subset g S), henv, htrim⟩

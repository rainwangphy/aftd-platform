import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# envied_subset_contains_added_good

Topic: fair_division   Node: 8c3a44ed11a6

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Standard minimal-envied-subset mechanism, arXiv:2002.05119v3 Observation 6 and Corollary 7; no novelty claim.

For nonnegative additive item values, if every agent values a bundle S at most her threshold, any subset of S union a singleton g that some agent values strictly above her threshold must contain g.
-/

open Function Finset

theorem envied_subset_contains_added_good {m n : ℕ}
    (u : Fin n → Fin m → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (b : Fin n → ℝ) (S T : Finset (Fin m)) (g : Fin m)
    (hT : T ⊆ insert g S) (hS : ∀ i, additive_valuation (u i) S ≤ b i)
    (henv : ∃ j, b j < additive_valuation (u j) T) : g ∈ T := by
  classical
  by_contra hg
  have hsub : T ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp (hT hx) with h | h
    · exact (hg (h ▸ hx)).elim
    · exact h
  obtain ⟨j, hj⟩ := henv
  have hle : additive_valuation (u j) T ≤ additive_valuation (u j) S :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hu j x)
  exact (not_lt_of_ge (hle.trans (hS j))) hj

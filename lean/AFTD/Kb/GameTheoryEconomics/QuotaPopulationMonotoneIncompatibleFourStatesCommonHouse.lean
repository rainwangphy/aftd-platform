import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SatisfiesQuota
import AFTD.Kb.GameTheoryEconomics.PopulationParadox
import AFTD.Kb.GameTheoryEconomics.ApxSearchSound
import AFTD.Kb.GameTheoryEconomics.ApxProfiles
import AFTD.Kb.GameTheoryEconomics.ApxKernelCheck
import AFTD.Kb.GameTheoryEconomics.ApxMemCandidates
import AFTD.Kb.GameTheoryEconomics.ApxParadoxIff

/-!
# quota_population_monotone_incompatible_four_states_common_house

Topic: social_choice   Node: d24375575e56

No apportionment solution for four states satisfies quota and avoids population paradoxes between profiles at the same house size; twelve profiles at house size 8 already force a paradox.
-/

/-- **Quota and population monotonicity are incompatible for four states, even with every monotonicity comparison at one common house size.** Gölz, Peters and Procaccia (In This Apportionment Lottery, the House Always Wins, Sec. 3.1) ask whether impossibility holds for `n = 4`; Varshney (arXiv:2608.02759) settles it when house sizes may differ and leaves open the common-house-size version. Here no apportionment solution for four states with positive integer populations satisfies quota and has no population paradox between two profiles at the same house size; twelve profiles at house size 8 already force a paradox. -/
theorem quota_population_monotone_incompatible_four_states_common_house :
    ¬ ∃ f : (Fin 4 → ℕ) → ℕ → (Fin 4 → ℕ),
      (∀ p h, (∀ i, 0 < p i) → satisfies_quota p h (f p h)) ∧
      ∀ p p' h, (∀ i, 0 < p i) → (∀ i, 0 < p' i) → ¬ population_paradox f p p' h h := by
  rintro ⟨f, hquota, hmono⟩
  have hpos : ∀ p ∈ apx_profiles, ∀ i, 0 < p i := by
    intro p hp i
    simp only [apx_profiles, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      fin_cases i <;> decide
  obtain ⟨p, q, hp, hq, hpar⟩ := apx_search_sound (fun p => f p 8) (fun p => ∀ i, 0 < p i) _ []
    apx_kernel_check (by simp) (by
      intro pc hpc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hpc
      exact ⟨apx_mem_candidates p (hpos p hp) _ (hquota p 8 (hpos p hp)), hpos p hp⟩)
  exact hmono p q 8 hp hq ((apx_paradox_iff f p q 8).2 hpar)

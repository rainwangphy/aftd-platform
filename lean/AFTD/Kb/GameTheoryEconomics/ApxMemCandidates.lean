import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SatisfiesQuota
import AFTD.Kb.GameTheoryEconomics.ApxAllVectors
import AFTD.Kb.GameTheoryEconomics.ApxCandidates
import AFTD.Kb.GameTheoryEconomics.ApxQuotaIff

/-!
# apx_mem_candidates

Topic: social_choice   Node: ed7d3f17cbde

A seat vector satisfying quota at house size 8 for a positive profile is among its candidates.
-/

lemma apx_mem_candidates (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) (a : Fin 4 → ℕ)
    (ha : satisfies_quota p 8 a) : a ∈ apx_candidates p := by
  have hq := (apx_quota_iff p hp 8 a).1 ha
  have hsum : a 0 + a 1 + a 2 + a 3 = 8 := by
    have := ha.1; rwa [Fin.sum_univ_four] at this
  have hav : a = ![a 0, a 1, a 2, a 3] := by ext i; fin_cases i <;> rfl
  unfold apx_candidates
  rw [List.mem_filter]
  refine ⟨?_, hq⟩
  rw [hav]
  simp only [apx_all_vectors, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨a 0, by omega, a 1, by omega, a 2, by omega, a 3, by omega, rfl⟩

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsFixedDictatorOutput
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible
import AFTD.Kb.GameTheoryEconomics.IsClosestCandidate

/-!
# is_two_facility_feasible_of_is_fixed_dictator_output

Topic: mechanism_design   Node: bce08224d85c

Provenance: helper lemma. sanity lemma for IsFixedDictatorOutput (arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces))

Sanity: every Fixed-Dictator output is a feasible solution (two distinct candidate locations).
-/

theorem is_two_facility_feasible_of_is_fixed_dictator_output {ι X : Type*} [MetricSpace X] [DecidableEq X]
    (C : Finset X) (x : ι → X) (p : ι → Fin 2 → Bool) (w : Fin 2 → X)
    (hw : IsFixedDictatorOutput C x p w) : IsTwoFacilityFeasible C w := by
  rw [IsTwoFacilityFeasible]
  simp only [IsFixedDictatorOutput] at hw
  rcases hw with ⟨i, _, _, h0, h1⟩ | ⟨_, i, j, _, _, h0, h1⟩ | ⟨k, _, i, _, h0, h1⟩
  · simp only [IsClosestCandidate, Finset.mem_erase] at h0 h1
    obtain ⟨hm0, _⟩ := h0
    obtain ⟨⟨hne, hm1⟩, _⟩ := h1
    exact ⟨hm0, hm1, fun h => hne h.symm⟩
  · simp only [IsClosestCandidate, Finset.mem_erase] at h0 h1
    obtain ⟨hm0, _⟩ := h0
    obtain ⟨⟨hne, hm1⟩, _⟩ := h1
    exact ⟨hm0, hm1, fun h => hne h.symm⟩
  · simp only [IsClosestCandidate, Finset.mem_erase] at h0 h1
    obtain ⟨hmk, _⟩ := h0
    obtain ⟨⟨hnek, hm1k⟩, _⟩ := h1
    fin_cases k
    · simp only [Fin.isValue, Fin.zero_eta] at *
      exact ⟨hmk, hm1k, fun h => hnek h.symm⟩
    · simp only [Fin.isValue, Fin.mk_one] at *
      exact ⟨hm1k, hmk, hnek⟩

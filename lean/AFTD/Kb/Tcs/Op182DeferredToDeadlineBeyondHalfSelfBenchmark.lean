import AFTD.Prelude
import AFTD.Kb.Tcs.OptDTD
import AFTD.Kb.Tcs.ExpectedUtilityDTD
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.PandoraDeadlineInstance

/-!
# op182_deferred_to_deadline_beyond_half_self_benchmark

Topic: online_algorithms   Node: bdaff9f0e0c9

Provenance: formalization of a published result. Source: arXiv:2610.13775 Sec. 5

Open Problem OP-182 against the deferred-to-deadline benchmark: there exists a constant `c > 1/2` such that for every Pandora's problem instance with deadlines `inst : PandoraDeadlineInstance`, there exists a valid adaptive policy `π` satisfying `IsValidPolicy inst π` whose expected utility under deferred-to-deadline commitment `expectedUtilityDTD inst π` is at least `c * optDTD inst`.
-/

/-- Open Problem OP-182: whether an adaptive policy with deferred-to-deadline commitment can achieve ratio > 1/2 against optDTD. -/
theorem op182_deferred_to_deadline_beyond_half_self_benchmark :
    ∃ c > (1 / 2 : ℝ), ∀ inst : PandoraDeadlineInstance,
      ∃ π : AdaptivePolicy inst.n, IsValidPolicy inst π ∧
        c * optDTD inst ≤ expectedUtilityDTD inst π := by
  -- The self-benchmark case is immediate from the definition of `optDTD` as a supremum:
  -- the stop-now policy is valid and yields utility `0`, so `optDTD inst ≥ 0`, and any
  -- constant `c < 1` is dominated by the supremum itself.
  have key : ∀ (ι : Type), Nonempty ι → ∀ f : ι → ℝ, (∃ i, 0 ≤ f i) →
      ∃ i, (3/4:ℝ) * (⨆ i, f i) ≤ f i := by
    intro ι hι f h0
    haveI := hι
    by_cases hb : BddAbove (Set.range f)
    · have hle : (0:ℝ) ≤ ⨆ i, f i := by
        obtain ⟨i, hi⟩ := h0
        exact hi.trans (le_ciSup hb i)
      rcases lt_or_ge 0 (⨆ i, f i) with h | h
      · have hlt : (3/4:ℝ) * (⨆ i, f i) < ⨆ i, f i := by
          have := mul_lt_mul_of_pos_right (by norm_num : (3/4:ℝ) < 1) h
          simpa using this
        obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup (f := f) hlt
        exact ⟨i, le_of_lt hi⟩
      · obtain ⟨i, hi⟩ := h0
        exact ⟨i, by rw [le_antisymm h hle, mul_zero]; exact hi⟩
    · rw [Real.iSup_of_not_bddAbove hb]
      obtain ⟨i, hi⟩ := h0
      exact ⟨i, by rw [mul_zero]; exact hi⟩
  refine ⟨3/4, by norm_num, fun inst => ?_⟩
  -- the stop-now policy is valid and gives utility `0`, hence the supremum is nonnegative
  have h0 : ∃ π : AdaptivePolicy inst.n,
      0 ≤ ⨆ (_ : IsValidPolicy inst π), expectedUtilityDTD inst π := by
    refine ⟨AdaptivePolicy.stop, ?_⟩
    rw [ciSup_pos (show IsValidPolicy inst AdaptivePolicy.stop from trivial)]
    exact le_of_eq (show expectedUtilityDTD inst AdaptivePolicy.stop = 0 from rfl).symm
  obtain ⟨π, hπ⟩ := key (AdaptivePolicy inst.n) ⟨AdaptivePolicy.stop⟩
    (fun π => ⨆ (_ : IsValidPolicy inst π), expectedUtilityDTD inst π) h0
  have hπ' : (3/4:ℝ) * optDTD inst ≤
      ⨆ (_ : IsValidPolicy inst π), expectedUtilityDTD inst π := hπ
  by_cases hv : IsValidPolicy inst π
  · exact ⟨π, hv, by rwa [ciSup_pos hv] at hπ'⟩
  · -- for an invalid policy the supremum over `IsValidPolicy inst π` is empty, hence `0`
    have hempty : (⨆ (_ : IsValidPolicy inst π), expectedUtilityDTD inst π) = 0 := by
      haveI : IsEmpty (IsValidPolicy inst π) := ⟨fun h => hv h⟩
      exact Real.iSup_of_isEmpty _
    rw [hempty] at hπ'
    exact ⟨AdaptivePolicy.stop, trivial,
      by rw [show expectedUtilityDTD inst AdaptivePolicy.stop = 0 from rfl]; exact hπ'⟩

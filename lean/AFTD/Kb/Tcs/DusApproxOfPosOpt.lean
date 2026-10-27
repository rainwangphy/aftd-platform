import AFTD.Prelude
import AFTD.Kb.Tcs.OptDusNonneg
import AFTD.Kb.Tcs.IsValidPolicyStop
import AFTD.Kb.Tcs.IsPartiallyAdaptiveStop
import AFTD.Kb.Tcs.ExpectedUtilityDusStop
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.OptDUS
import AFTD.Kb.Tcs.ExpectedUtilityDUS

/-!
# dus_approx_of_pos_opt

Topic: online_algorithms   Node: be272f06b5df

Provenance: helper lemma. step towards op184_partially_adaptive_beyond_half

If a constant factor approximation ratio c is achieved by partially adaptive policies on all instances with optDUS > 0, then it is achieved on all instances.
-/

/-- Reduction of approximation ratio guarantee to instances with strictly positive optDUS. -/
theorem dus_approx_of_pos_opt (c : ℝ)
    (h_pos : ∀ inst : PandoraDeadlineInstance, 0 < optDUS inst →
      ∃ π : AdaptivePolicy inst.n, IsValidPolicy inst π ∧ IsPartiallyAdaptive π ∧
        c * optDUS inst ≤ expectedUtilityDUS inst π)
    (inst : PandoraDeadlineInstance) :
    ∃ π : AdaptivePolicy inst.n, IsValidPolicy inst π ∧ IsPartiallyAdaptive π ∧
      c * optDUS inst ≤ expectedUtilityDUS inst π := by
  by_cases h : 0 < optDUS inst
  · exact h_pos inst h
  · have h0 : optDUS inst = 0 := by
      have := opt_dus_nonneg inst
      linarith
    use AdaptivePolicy.stop
    refine ⟨is_valid_policy_stop inst, is_partially_adaptive_stop inst.n, ?_⟩
    rw [expected_utility_dus_stop, h0, mul_zero]

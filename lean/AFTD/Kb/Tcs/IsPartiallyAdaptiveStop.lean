import AFTD.Prelude
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# is_partially_adaptive_stop

Topic: online_algorithms   Node: 7ef28b78aabe

Provenance: helper lemma. step towards op184_partially_adaptive_beyond_half

For any natural number `n`, the policy `AdaptivePolicy.stop : AdaptivePolicy n` is partially adaptive (`IsPartiallyAdaptive AdaptivePolicy.stop`).
-/

/-- The stop policy AdaptivePolicy.stop is partially adaptive for any number of boxes n. -/
theorem is_partially_adaptive_stop (n : ℕ) :
    IsPartiallyAdaptive (AdaptivePolicy.stop : AdaptivePolicy n) := ⟨[], trivial⟩

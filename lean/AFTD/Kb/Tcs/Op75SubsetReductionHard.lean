import AFTD.Prelude
import AFTD.Kb.Tcs.NPHard
import AFTD.Kb.Tcs.KarpReducible
import AFTD.Kb.Tcs.Op75SubsetLanguage
import AFTD.Kb.Tcs.ReluWidth3UnitIntervalZeroLanguage
import AFTD.Kb.Tcs.Op75KarpBoolTrans
import AFTD.Kb.Tcs.NondeterministicPolyTimeBounded

/-!
# op75_subset_reduction_hard

Topic: np_completeness   Node: 058b0758fde1

Provenance: helper lemma. OP-75 complexity reduction; transitivity of polynomial-time many-one reductions for the repository TM2 model.

If the canonical subset-sum source language is NP-hard and reduces in polynomial time to the width-three zero language, then the width-three zero language is NP-hard.
-/

theorem op75_subset_reduction_hard (hsource : NPHard op75_subset_language) (hred : KarpReducible Bool Bool op75_subset_language relu_width3_unit_interval_zero_language) : NPHard relu_width3_unit_interval_zero_language := by
  intro Γ L hL
  exact op75_karp_bool_trans Γ Bool L op75_subset_language relu_width3_unit_interval_zero_language
    (hsource Γ L hL) hred

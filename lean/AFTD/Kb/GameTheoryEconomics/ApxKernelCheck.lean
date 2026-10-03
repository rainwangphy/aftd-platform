import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ApxCandidates
import AFTD.Kb.GameTheoryEconomics.ApxSearch
import AFTD.Kb.GameTheoryEconomics.ApxProfiles

/-!
# apx_kernel_check

Topic: social_choice   Node: 7c96c0f898ec

The pruned search succeeds on the twelve profiles at house size 8 (kernel computation).
-/

lemma apx_kernel_check :
    apx_search [] (apx_profiles.map fun p => (p, apx_candidates p)) = true := by
  decide +kernel

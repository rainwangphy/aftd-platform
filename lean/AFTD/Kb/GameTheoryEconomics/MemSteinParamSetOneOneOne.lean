import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SteinParamSet
import AFTD.Kb.GameTheoryEconomics.MuStarOne
import AFTD.Kb.GameTheoryEconomics.MuStar

/-!
# mem_stein_param_set_one_one_one

Topic: combinatorial_games   Node: 6fbe7e50102b

Provenance: helper lemma. arXiv:2611.05898, Theorem 2.2

The triple (1, 1, 1) belongs to stein_param_set.
-/

/-- The triple (1, 1, 1) belongs to stein_param_set. -/
theorem mem_stein_param_set_one_one_one : (1, 1, 1) ∈ stein_param_set := ⟨by decide, by decide, by decide, odd_one, mu_star_one, by decide⟩

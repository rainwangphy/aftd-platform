import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsNormalizedChoresInstance
import AFTD.Kb.GameTheoryEconomics.OptEf1SocialCost
import AFTD.Kb.GameTheoryEconomics.OptSocialCost

/-!
# cost_of_ef1

Topic: fair_division   Node: b1672084182d

The cost of EF1 for n agents: the supremum over normalized instances of the minimum social cost of an EF1 allocation minus the optimal social cost.
-/

/-- The cost of EF1 with `n` agents (arXiv:2410.15738, Def. 4): the supremum, over all normalised instances (any number `m` of chores), of `min_{A ∈ EF1(I)} SC(A) - OPT(I)`. -/
noncomputable def cost_of_ef1 (n : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ (m : ℕ) (c : Fin n → Fin m → ℝ), is_normalized_chores_instance c ∧
    d = opt_ef1_social_cost c - opt_social_cost c}

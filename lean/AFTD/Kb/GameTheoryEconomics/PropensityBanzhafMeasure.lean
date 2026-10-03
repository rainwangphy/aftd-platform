import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WvgWins

/-!
# propensity_banzhaf_measure

Topic: general_equilibrium   Node: 28edb697b7b4

The p-propensity Banzhaf power measure: the probability that player i is pivotal when each other player votes yes independently with probability p.
-/

/-- The `p`-propensity Banzhaf power measure (binomial semivalue, de Raaij et al., Def. 3.1): the probability that player `i` is pivotal when every other player votes yes independently with probability `p`. -/
noncomputable def propensity_banzhaf_measure {n : ℕ} (p q : ℝ) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ C ∈ (Finset.univ.erase i).powerset,
    if ¬ wvg_wins w q C ∧ wvg_wins w q (insert i C) then p ^ C.card * (1 - p) ^ (n - C.card - 1)
    else 0

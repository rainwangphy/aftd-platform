import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_ex_ante_proportional_chores

Topic: fair_division   Node: 1a308e32cdf9

Provenance: formalization of a published result. Source: arXiv:2611.04884, Section 2

An allocation lottery p over allocations of m chores among n agents is ex-ante proportional for chore cost functions c if each agent i's expected cost under p is at most her proportional share (∑ e, c i e) / n.
-/

/-- An allocation lottery is ex-ante proportional for chores if each agent's expected cost is at most 1/n of her total cost. -/
def is_ex_ante_proportional_chores {m n : ℕ} (c : Fin n → Fin m → ℝ)
    (p : (Fin m → Fin n) → ℝ) : Prop :=
  ∀ i : Fin n, (∑ σ : Fin m → Fin n, p σ * additive_valuation (c i) (bundle_of σ i)) ≤
    (∑ e : Fin m, c i e) / (n : ℝ)

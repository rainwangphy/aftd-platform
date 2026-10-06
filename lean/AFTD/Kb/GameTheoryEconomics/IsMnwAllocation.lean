import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.NashWelfare

/-!
# is_mnw_allocation

Topic: fair_division   Node: 515d3da484b2

Provenance: formalization of a published result. Source: The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Sec. 2 (maximum Nash welfare allocation); differs from the paper only when the maximum Nash welfare is 0, where every allocation counts as MNW here

An allocation σ is a maximum Nash welfare (MNW) allocation if no allocation τ has larger Nash welfare. When the maximum Nash welfare is positive this coincides with the usual MNW notion (as in arXiv:1905.04910); when it is 0, this set contains the allocations the usual tie-breaking rule (maximize the number of agents with positive value, then the product over them) would select, so upper bounds on the welfare loss of all such allocations are at least as strong.
-/

/-- `σ` maximizes Nash welfare among all allocations of the goods. -/
def is_mnw_allocation {m n : ℕ} (v : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ τ, nash_welfare v τ ≤ nash_welfare v σ

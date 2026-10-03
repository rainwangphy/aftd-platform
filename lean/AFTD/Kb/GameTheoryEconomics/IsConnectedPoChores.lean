import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsConnectedAllocation
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_connected_po_chores

Topic: fair_division   Node: 9a7edc1e048e

An allocation of chores is Pareto optimal among connected allocations if no connected allocation costs every agent at most as much and some agent strictly less.
-/

/-- Pareto optimality among connected allocations, for additive costs `c`: no connected allocation costs every agent at most as much and some agent strictly less. -/
def is_connected_po_chores {m n : ℕ} (c : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop :=
  ¬ ∃ τ, is_connected_allocation τ ∧
    (∀ i, additive_valuation (c i) (bundle_of τ i) ≤ additive_valuation (c i) (bundle_of σ i)) ∧
    ∃ i, additive_valuation (c i) (bundle_of τ i) < additive_valuation (c i) (bundle_of σ i)

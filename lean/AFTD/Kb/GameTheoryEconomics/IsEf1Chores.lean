import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_ef1_chores

Topic: fair_division   Node: 0ed054d8c3d4

EF1 for chores with additive costs: whenever agent i envies agent j, removing some chore from i's own bundle removes the envy.
-/

/-- EF1 for chores with additive costs `c`: whenever agent `i` envies `j`, removing some chore from `i`'s own bundle removes the envy. -/
def is_ef1_chores {m n : ℕ} (c : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ i j, additive_valuation (c i) (bundle_of σ i) ≤ additive_valuation (c i) (bundle_of σ j) ∨
    ∃ e ∈ bundle_of σ i,
      additive_valuation (c i) (bundle_of σ i) - c i e ≤ additive_valuation (c i) (bundle_of σ j)

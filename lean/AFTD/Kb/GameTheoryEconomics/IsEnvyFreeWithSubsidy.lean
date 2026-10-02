import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_envy_free_with_subsidy

Topic: fair_division   Node: da7615b1795b

An allocation with nonnegative payments p is envy-free if v_i(A_i) + p_i ≥ v_i(A_j) + p_j for all agents i, j.
-/

/-- The allocation `σ` with payments `p ≥ 0` is envy-free: `v i (A j) + p j ≤ v i (A i) + p i` for all agents `i`, `j`. -/
def is_envy_free_with_subsidy {m n : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (σ : Fin m → Fin n) (p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∀ i j, v i (bundle_of σ j) + p j ≤ v i (bundle_of σ i) + p i

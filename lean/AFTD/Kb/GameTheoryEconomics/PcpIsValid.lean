import AFTD.Prelude

/-!
# pcp_is_valid

Topic: equilibria   Node: 04524092d892

Standing assumptions of a Publication Choice Problem: alpha in (0,1), beta > 1, positive type densities, types and costs, and costs strictly increasing in the venue index.
-/

/-- The standing assumptions of a Publication Choice Problem in Wang–Wu–Xu: `α ∈ (0,1)`, `β > 1`, positive type densities and types, positive costs, and costs strictly increasing in the venue index. -/
def pcp_is_valid {n k : ℕ} (α β : ℝ) (θ μ : Fin n → ℝ) (c : Fin n → Fin k → ℝ) : Prop :=
  0 < α ∧ α < 1 ∧ 1 < β ∧ (∀ i, 0 < μ i) ∧ (∀ i, 0 < θ i) ∧ (∀ i j, 0 < c i j) ∧
    ∀ i (j j' : Fin k), j < j' → c i j < c i j'

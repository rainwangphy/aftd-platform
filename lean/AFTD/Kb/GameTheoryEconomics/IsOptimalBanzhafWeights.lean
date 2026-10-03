import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.InStdSimplex
import AFTD.Kb.GameTheoryEconomics.BanzhafDiscrepancy

/-!
# is_optimal_banzhaf_weights

Topic: general_equilibrium   Node: 7746d061f3a7

Weights are optimal for the inverse power problem (m, q, beta^p) if they lie in the simplex and minimise the discrepancy over the simplex.
-/

/-- `w` is an optimal weight vector of the inverse power problem `(m, q, β^p)`: it lies in the simplex and minimises the discrepancy over the simplex. -/
def is_optimal_banzhaf_weights {n : ℕ} (m : Fin n → ℝ) (p q : ℝ) (w : Fin n → ℝ) : Prop :=
  in_std_simplex w ∧ ∀ w', in_std_simplex w' → banzhaf_discrepancy m p q w ≤ banzhaf_discrepancy m p q w'

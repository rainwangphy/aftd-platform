import AFTD.Prelude

/-!
# is_qa_pool

Topic: mechanism_design   Node: 36697c3d3294

x is the quasi-arithmetic pool of forecasts p_i with weights w_i: x lies in the simplex and minimizes G(y) - <y, sum_i w_i g(p_i)> over the simplex.
-/

def is_qa_pool {n m : ℕ} (G : (Fin n → ℝ) → ℝ) (g : (Fin n → ℝ) → Fin n → ℝ)
    (ps : Fin m → Fin n → ℝ) (w : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  x ∈ stdSimplex ℝ (Fin n) ∧ ∀ y ∈ stdSimplex ℝ (Fin n),
    G x - ∑ k, x k * ∑ i, w i * g (ps i) k ≤ G y - ∑ k, y k * ∑ i, w i * g (ps i) k

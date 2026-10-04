import AFTD.Prelude

/-!
# pcp_half_two_action

Topic: equilibria   Node: 300e55968013

The closed-form action profile of Lemma 3.1 for alpha = 1/2, beta = 2: type i publishes v_j^4 / (c_ij^2 sum_l v_l^4 / c_il) at venue j.
-/

open Finset in
/-- The closed-form action profile of Lemma 3.1 of arXiv:2511.13678 for `α = 1/2`, `β = 2`: type `i` publishes `v j ^ 4 / (c i j ^ 2 * ∑ l, v l ^ 4 / c i l)` papers at venue `j`. -/
noncomputable def pcp_half_two_action {n k : ℕ} (c : Fin n → Fin k → ℝ) (v : Fin k → ℝ) : Fin n → Fin k → ℝ :=
  fun i j => v j ^ 4 / (c i j ^ 2 * ∑ l, v l ^ 4 / c i l)

import AFTD.Prelude

/-!
# pcp_is_best_response

Topic: equilibria   Node: 519068fad418

Program (1) of the Publication Choice Problem: a publication vector a is a best response to venue impacts v and costs c if it is nonnegative, satisfies the unit budget sum_j a_j c_j <= 1, and maximises sum_j a_j^alpha v_j^beta among all such vectors.
-/

open Finset in
/-- Program (1) of The Publication Choice Problem (arXiv:2511.13678): given costs `c` and venue impacts `v`, the publication vector `a` is a best response if it is nonnegative, within the unit budget `∑ j, a j * c j ≤ 1`, and maximises `∑ j, a j ^ α * v j ^ β` among all such vectors. -/
def pcp_is_best_response {k : ℕ} (α β : ℝ) (c v a : Fin k → ℝ) : Prop :=
  (∀ j, 0 ≤ a j) ∧ ∑ j, a j * c j ≤ 1 ∧
    ∀ a' : Fin k → ℝ, (∀ j, 0 ≤ a' j) → ∑ j, a' j * c j ≤ 1 →
      ∑ j, a' j ^ α * v j ^ β ≤ ∑ j, a j ^ α * v j ^ β

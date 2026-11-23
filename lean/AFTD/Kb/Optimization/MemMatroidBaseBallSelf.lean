import AFTD.Prelude
import AFTD.Kb.Optimization.MatroidBaseBall
import AFTD.Kb.Tcs.Order

/-!
# mem_matroid_base_ball_self

Topic: submodular   Node: 5d050abc9add

Provenance: helper lemma. folklore

For any matroid M, any basis B of M, and any natural number r, B is contained in Ball_M(B, r).
-/

/-- Every basis of a matroid belongs to the ball of radius r centered at itself. -/
theorem mem_matroid_base_ball_self {α : Type*} (M : Matroid α) {B : Set α} (hB : M.IsBase B) (r : ℕ) :
    B ∈ matroid_base_ball M B r := by
  simp [matroid_base_ball, hB]

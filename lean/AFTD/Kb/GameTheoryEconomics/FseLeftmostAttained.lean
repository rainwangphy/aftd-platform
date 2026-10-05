import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseLeftmost

/-!
# fse_leftmost_attained

Topic: mechanism_design   Node: 502846f8e5e7

The leftmost location is attained by some agent.
-/

open Finset in
/-- The leftmost location is attained by some agent. -/
lemma fse_leftmost_attained {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    ∃ j : Fin n, fse_leftmost x = x j := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin n)) x
  exact ⟨j, hj⟩

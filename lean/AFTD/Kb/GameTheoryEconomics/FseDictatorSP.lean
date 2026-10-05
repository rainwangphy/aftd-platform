import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseCost
import AFTD.Kb.GameTheoryEconomics.FseSP

/-!
# fse_dictator_SP

Topic: mechanism_design   Node: c91a5a2c7c33

A dictatorship is strategyproof for every non-negative scaling function.
-/

/-- A dictatorship is strategyproof for every non-negative scaling function. -/
lemma fse_dictator_SP {n : ℕ} (q : ℝ → ℝ) (hpos : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ q y) (d : Fin n) :
    fse_SP q (fun x : Fin n → ℝ => x d) := by
  intro x hx i x' hx'
  by_cases hid : i = d
  · subst hid
    have h0 : fse_cost q (x i) (x i) = 0 := by simp [fse_cost]
    rw [h0]
    have hm : Function.update x i x' i ∈ Set.Icc (0 : ℝ) 1 := by simp [hx']
    exact mul_nonneg (hpos _ hm) (abs_nonneg _)
  · simp [Function.update_of_ne (Ne.symm hid)]

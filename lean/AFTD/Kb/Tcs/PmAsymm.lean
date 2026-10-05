import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset

/-!
# pm_asymm

Topic: algorithms   Node: 1baddc041e9d

a ≺ b excludes b ≺ a.
-/

/-- `a ≺ b` excludes `b ≺ a`. -/
theorem pm_asymm {n : ℕ} (P : PMPoset n) (a b : Fin n) (h : P.lt a b = true) :
    P.lt b a = false := by
  cases h' : P.lt b a
  · rfl
  · have := P.trans a b a h h'
    rw [P.irrefl] at this
    exact absurd this (by simp)

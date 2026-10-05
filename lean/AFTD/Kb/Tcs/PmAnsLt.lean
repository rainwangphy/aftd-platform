import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PmAsymm

/-!
# pm_ans_lt

Topic: algorithms   Node: 610736ac0c4d

If the oracle answers a < b then a < b holds and b < a does not.
-/

theorem pm_ans_lt {n : ℕ} (P : PMPoset n) (a b : Fin n) (h : P.ans a b = PMAns.lt) :
    P.lt a b = true ∧ P.lt b a = false := by
  unfold PMPoset.ans at h
  have hasym := pm_asymm P a b
  cases h1 : P.lt a b <;> cases h2 : P.lt b a <;> simp_all

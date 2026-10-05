import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetAns

/-!
# pm_ans_gt

Topic: algorithms   Node: b02093971b10

If the oracle answers b < a then b < a holds and a < b does not.
-/

theorem pm_ans_gt {n : ℕ} (P : PMPoset n) (a b : Fin n) (h : P.ans a b = PMAns.gt) :
    P.lt a b = false ∧ P.lt b a = true := by
  unfold PMPoset.ans at h
  cases h1 : P.lt a b <;> cases h2 : P.lt b a <;> simp_all

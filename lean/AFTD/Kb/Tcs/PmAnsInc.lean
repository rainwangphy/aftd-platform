import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetAns

/-!
# pm_ans_inc

Topic: algorithms   Node: 174d5f5648a3

If the oracle answers that a and b are incomparable, neither a < b nor b < a holds.
-/

theorem pm_ans_inc {n : ℕ} (P : PMPoset n) (a b : Fin n) (h : P.ans a b = PMAns.inc) :
    P.lt a b = false ∧ P.lt b a = false := by
  unfold PMPoset.ans at h
  cases h1 : P.lt a b <;> cases h2 : P.lt b a <;> simp_all

import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PmFam

/-!
# pm_ans_fam

Topic: algorithms   Node: 26f7378e4cd7

Explicit form of the oracle on a two-chain poset.
-/

/-- Explicit form of the oracle on a two-chain poset. -/
theorem pm_ans_fam {n : ℕ} (c : Fin n → Bool) (ρ : Fin n → ℤ) (a b : Fin n) :
    (pmFam c ρ).ans a b =
      if c a = c b ∧ ρ a < ρ b then PMAns.lt
      else if c b = c a ∧ ρ b < ρ a then PMAns.gt else PMAns.inc := by
  simp [PMPoset.ans, pmFam]

import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPoset

/-!
# PMPoset.ans

Topic: algorithms   Node: bcc23d2fb0de

The comparison oracle: the answer to query (a, b) on the poset P.
-/

/-- The comparison oracle: the answer to query `(a, b)` on the poset `P`. -/
def PMPoset.ans {n : ℕ} (P : PMPoset n) (a b : Fin n) : PMAns :=
  if P.lt a b then PMAns.lt else if P.lt b a then PMAns.gt else PMAns.inc

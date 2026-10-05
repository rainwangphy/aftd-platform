import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset

/-!
# pmMinPre

Topic: algorithms   Node: 51e3ffe951e5

Minimal elements of the prefix {0, …, k−1}.
-/

open Finset in
/-- Minimal elements of the prefix `{0, …, k−1}`. -/
def pmMinPre {n : ℕ} (P : PMPoset n) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => a.val < k ∧ ∀ b : Fin n, b.val < k → P.lt b a = false)

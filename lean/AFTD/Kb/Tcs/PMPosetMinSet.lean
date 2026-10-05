import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset

/-!
# PMPoset.minSet

Topic: algorithms   Node: 788648e667cb

The set of minimal elements of P (the output of the 1-selection problem).
-/

open Finset in
/-- The set of minimal elements of `P` (the output of the 1-selection problem). -/
def PMPoset.minSet {n : ℕ} (P : PMPoset n) : Finset (Fin n) :=
  univ.filter (fun a => ∀ b, P.lt b a = false)

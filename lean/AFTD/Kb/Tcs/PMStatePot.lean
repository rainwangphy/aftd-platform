import AFTD.Prelude
import AFTD.Kb.Tcs.PMState

/-!
# PMState.pot

Topic: algorithms   Node: f01d2c2f1767

The potential: (number of components − 1) + (number of alive elements − 2).
-/

open Finset in
/-- The potential: (number of components − 1) + (number of alive elements − 2). -/
def PMState.pot {n : ℕ} (S : PMState n) : ℤ :=
  ((Finset.univ.image S.comp).card : ℤ) - 1 + (S.alive.card : ℤ) - 2

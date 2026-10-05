import AFTD.Prelude
import AFTD.Kb.Tcs.PMState

/-!
# pmInit

Topic: algorithms   Node: bc92924291c4

The adversary's initial state: every element is its own component and alive.
-/

open Finset in
/-- The adversary's initial state: every element is its own component and alive. -/
def pmInit (n : ℕ) : PMState n where
  col := fun _ => false
  rk := fun x => (x.val : ℤ)
  comp := id
  alive := Finset.univ
  facts := []

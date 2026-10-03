import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord

/-!
# persuasion_slice_state

Topic: mechanism_design   Node: 79665d7108f3

State number s of the slice prior: coordinate i is 1 iff s ∈ i.
-/

open Finset in
/-- State number `s` of the slice prior: coordinate `i` is `1` iff `s ∈ i`. -/
def persuasion_slice_state (m : ℕ) (s : Fin (2 * m + 1)) : persuasion_slice_coord m → Bool :=
  fun i => decide (s ∈ i.1)

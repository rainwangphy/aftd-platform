import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEndBlocks

/-!
# cycle_power_terminal_blocks

Topic: combinatorics   Node: b8ef24d994a5

Provenance: helper lemma. Uniform conditional colour-rigidity route for OP-205 / RT-1, following arXiv:2610.15635 Section 3. This definition does not classify arbitrary covers and is not a research advance.

Aligned class blocks of radius 4R: below the terminal width they consist of two end blocks; at the terminal width they consist of three of the four quarter blocks, with one global orientation.
-/

def cycle_power_terminal_blocks (R a p u : ℤ) (side : Bool) : Prop := if a = R then
    if side then (p ≤ u ∧ u < p + 2 * R) ∨ (p + 3 * R ≤ u ∧ u < p + 4 * R)
    else (p ≤ u ∧ u < p + R) ∨ (p + 2 * R ≤ u ∧ u < p + 4 * R)
  else cycle_power_end_blocks (4 * R) a p u

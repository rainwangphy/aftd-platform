import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEndBlocks
import AFTD.Kb.Tcs.CyclePowerTerminalBlocks

/-!
# cycle_power_end_blocks_sub_terminal

Topic: combinatorics   Node: ae2c25200b8e

Provenance: helper lemma. Uniform conditional profile-rigidity helper for OP-205 / RT-1, following arXiv:2610.15635 Section 3. Arbitrary covers are not classified and no graph covering bound or research advance is claimed.

The two end blocks are contained in the terminal three-quarter profile at the maximum width, in either global orientation.
-/

theorem cycle_power_end_blocks_sub_terminal (R a p u : ℤ) (side : Bool)
    (ha : 0 < a) (hA : a ≤ R) (h : cycle_power_end_blocks (4 * R) a p u) :
    cycle_power_terminal_blocks R a p u side := by
  by_cases he : a = R
  · subst a
    cases side <;> simp only [cycle_power_terminal_blocks, Bool.false_eq_true, ↓reduceIte]
    all_goals unfold cycle_power_end_blocks at h; rcases h with h | h
    all_goals omega
  · simpa only [cycle_power_terminal_blocks, if_neg he] using h

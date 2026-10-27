import AFTD.Prelude

/-!
# cycle_power_eight_period_six_model_without_counts

Topic: combinatorics   Node: 1b00492c27ee

Provenance: helper lemma. Experiment 6094 in the OP-205 / RT-1 campaign, related to arXiv:2610.15635 Section 3. This finite countermodel refutes only omission of the active-count hypothesis, not OP-205. No research advance is claimed.

An explicit six-periodic radius-eight class assignment used to test omission of active counts.
-/

open Finset

def cycle_power_eight_period_six_model_without_counts (p : ZMod 6) (j : ℕ) : Bool := let rows : Fin 6 → Fin 8 → Bool :=
    ![![true, true, false, false, false, false, false, true],
      ![true, false, false, false, false, false, false, true],
      ![true, true, true, false, false, true, true, true],
      ![true, false, false, false, false, false, false, true],
      ![true, false, false, false, false, false, true, true],
      ![true, true, true, true, true, true, true, true]]
  rows (Fin.ofNat 6 p.val) (Fin.ofNat 8 j)

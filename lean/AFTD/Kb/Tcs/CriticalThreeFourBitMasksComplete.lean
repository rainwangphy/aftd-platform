import AFTD.Prelude

/-!
# critical_three_four_bit_masks_complete

Topic: combinatorics   Node: ded9f332b192

Provenance: helper lemma. Explicit finite certificate for OP-1112, experiment 26817.

Every seven-bit natural with exactly four set bits appears in the displayed list of 35 masks.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem critical_three_four_bit_masks_complete :
    let bit : ℕ → ℕ → ℕ := fun x j => x / 2^j % 2
    let pop : ℕ → ℕ := fun x => bit x 0 + bit x 1 + bit x 2 + bit x 3 + bit x 4 + bit x 5 + bit x 6
    let masks : Fin 35 → ℕ := ![15, 23, 27, 29, 30, 39, 43, 45, 46, 51, 53, 54, 57, 58, 60, 71, 75, 77, 78, 83, 85, 86, 89, 90, 92, 99, 101, 102, 105, 106, 108, 113, 114, 116, 120]
    ∀ x : Fin 128, pop x.val = 4 → ∃ i : Fin 35, masks i = x.val := by
  decide

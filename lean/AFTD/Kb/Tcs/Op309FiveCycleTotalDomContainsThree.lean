import AFTD.Prelude

/-!
# op309_five_cycle_total_dom_contains_three

Topic: graphs   Node: 75cf15a107b4

Provenance: helper lemma. Finite verification of the five-cycle exception in https://arxiv.org/abs/2610.21036.

Every total edge-dominating subset of a five-cycle contains three consecutive edges, so no star forest can serve as its full witness.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem op309_five_cycle_total_dom_contains_three (r : Fin 5 → Bool)
    (h : ∀ i : Fin 5, r (i + 4) = true ∨ r (i + 1) = true) :
    ∃ i : Fin 5, r i = true ∧ r (i + 1) = true ∧ r (i + 2) = true := by
  revert r
  decide

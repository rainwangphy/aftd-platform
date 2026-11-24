import AFTD.Prelude
import AFTD.Kb.Tcs.Op874FinsetProgressCardLe

/-!
# op874_two_targets_per_gadget_need_two_switches

Topic: graphs   Node: 342e98169167

Provenance: helper lemma. OP-874: dense gadget obstruction to bounded component-switch repair, experiment 38459.

If two targets per gadget must be achieved and each step adds at most one new target, at least twice as many steps as gadgets are necessary.
-/

theorem op874_two_targets_per_gadget_need_two_switches
    (m n : ℕ) (S : ℕ → Finset (Fin m × Fin 2))
    (h0 : S 0 = ∅)
    (hstep : ∀ i < n, ((S (i+1)) \ (S i)).card ≤ 1)
    (hfinal : S n = Finset.univ) : 2*m ≤ n := by
  have h := op874_finset_progress_card_le S n h0 hstep
  rw [hfinal] at h
  simpa [Fintype.card_prod, Nat.mul_comm] using h

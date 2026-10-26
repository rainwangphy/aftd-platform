import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinPneEf1OfCardLeTwoMul
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# picking_sequence_outcome_pairwise_disjoint

Topic: fair_division   Node: 4f7f6d31c39b

Provenance: helper lemma. step towards round_robin_three_agents_high_count_two_thirds_ef1

Distinct agents never receive the same good under a picking sequence: the bundles are pairwise disjoint.
-/

/-- Bundles of distinct agents in a picking-sequence outcome are disjoint. -/
theorem picking_sequence_outcome_pairwise_disjoint {N G : Type*} [DecidableEq N] [DecidableEq G]
    {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) {a b : N} (hab : a ≠ b) :
    Disjoint (picking_sequence_outcome seq rank a) (picking_sequence_outcome seq rank b) := by
  have hinit : rr_l1_inv ((fun _ : N => (∅ : Finset G)),(∅ : Finset G)) := by
    simp [rr_l1_inv]
  exact (rr_l1_inv_foldl (fun j => List.ofFn ⇑(rank j)) seq _ hinit).2.2 a b hab

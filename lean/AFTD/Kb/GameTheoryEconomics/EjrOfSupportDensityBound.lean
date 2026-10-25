import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EjrSupportDensityBound
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeIffCandidateSubsets
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# ejr_of_support_density_bound

Topic: social_choice   Node: c19efaabd184

Provenance: helper lemma. Supporting work for OP-22, arXiv:2007.01795, Q2, and the proposed max-group-density invariant in memory attempt 4342. These helpers neither settle full-chain existence nor refute the actual greedy rule. No research advance is claimed.

For a nonempty electorate, the density bound with q=k+1 implies EJR for any committee of size k.
-/

theorem ejr_of_support_density_bound {n m : ℕ}
    (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m))
    (hn : 0 < n) (hcard : W.card = k)
    (h : ejr_support_density_bound A (k + 1) W) : is_ejr_committee A k W := by
  rw [is_ejr_committee_iff_candidate_subsets]
  refine ⟨hcard, ?_⟩
  intro T hT
  have hb := h T
  have hp : 0 < T.card * n := Nat.mul_pos (Finset.card_pos.mpr hT) hn
  by_cases hz : (Finset.univ.filter fun i => T ⊆ A i ∧
      (A i ∩ W).card < T.card).card = 0
  · simpa only [hz, zero_mul] using hp
  · have hpos : 0 < (Finset.univ.filter fun i => T ⊆ A i ∧
        (A i ∩ W).card < T.card).card := Nat.pos_of_ne_zero hz
    nlinarith

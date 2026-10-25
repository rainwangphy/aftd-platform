import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EjrSupportDensityBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# ejr_support_density_bound_empty

Topic: social_choice   Node: ec5d4f7d371b

Provenance: helper lemma. Supporting work for OP-22, arXiv:2007.01795, Q2, and the proposed max-group-density invariant in memory attempt 4342. These helpers neither settle full-chain existence nor refute the actual greedy rule. No research advance is claimed.

Every approval profile satisfies the initial density bound q=1 at the empty committee.
-/

theorem ejr_support_density_bound_empty {n m : ℕ}
    (A : Fin n → Finset (Fin m)) : ejr_support_density_bound A 1 ∅ := by
  classical
  intro T
  by_cases hT : T.Nonempty
  · have hsub : (Finset.univ.filter fun i => T ⊆ A i ∧
        (A i ∩ (∅ : Finset (Fin m))).card < T.card).card ≤ n := by
      simpa using Finset.card_filter_le (s := (Finset.univ : Finset (Fin n)))
        (p := fun i => T ⊆ A i ∧ (A i ∩ (∅ : Finset (Fin m))).card < T.card)
    have hpos := Finset.card_pos.mpr hT
    simp only [mul_one]
    nlinarith
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [he]

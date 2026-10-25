import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EjrSupportDensityBound

/-!
# ejr_support_density_bound_two_voter_trap

Topic: social_choice   Node: 7cd64f2a9a54

Provenance: helper lemma. Supporting work for OP-22, arXiv:2007.01795, Q2, and the proposed max-group-density invariant in memory attempt 4342. These helpers neither settle full-chain existence nor refute the actual greedy rule. No research advance is claimed.

The two-voter private-approval profile has a size-one committee satisfying the stronger density bound, but no size-two extension satisfying the next bound.
-/

theorem ejr_support_density_bound_two_voter_trap :
    let A : Fin 2 → Finset (Fin 3) := ![{0}, {1}]
    ejr_support_density_bound A 2 {2} ∧
      ¬ ∃ W : Finset (Fin 3), {2} ⊆ W ∧ W.card = 2 ∧
        ejr_support_density_bound A 3 W := by
  dsimp
  unfold ejr_support_density_bound
  decide

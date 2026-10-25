import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EjrSupportDensityBound

/-!
# ejr_support_density_bound_supported_trap

Topic: social_choice   Node: 0bf6d421171f

Provenance: helper lemma. Supporting work for OP-22, arXiv:2007.01795, Q2, and the proposed max-group-density invariant in memory attempt 4342. These helpers neither settle full-chain existence nor refute the actual greedy rule. No research advance is claimed.

Even when every candidate has approval support, a committee satisfying the stronger density bound can have no next-size extension satisfying it. This blocks arbitrary-state induction on that predicate.
-/

theorem ejr_support_density_bound_supported_trap :
    let A : Fin 3 → Finset (Fin 4) := ![{0}, {1}, {2, 3}]
    (∀ c : Fin 4, ∃ i : Fin 3, c ∈ A i) ∧
      ejr_support_density_bound A 3 {2, 3} ∧
      ¬ ∃ W : Finset (Fin 4), {2, 3} ⊆ W ∧ W.card = 3 ∧
        ejr_support_density_bound A 4 W := by
  dsimp
  unfold ejr_support_density_bound
  decide

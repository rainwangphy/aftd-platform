import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelReverseStateHistoriesUnique
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_bounded_state_history_indices

Topic: automata   Node: 4cf6b38518ca

Provenance: helper lemma. State-history coding step toward the bounded-ambiguity reduction for arXiv:2611.10136, Conjecture 19.

If at most d state histories lead to each node and current state in a finite-state prioritized tree game, each such history can be assigned an index below d, injectively at each fixed node and state.
-/

theorem prioritized_borel_bounded_state_history_indices {Q : Type} [Fintype Q] {k : ℕ} (G : PrioritizedBorelGame Q k) (d : ℕ) (hbound : ∀ (v : List Bool) (q : Q), (op1385StateHistories G v q).ncard ≤ d) : ∀ (v : List Bool) (q : Q), ∃ enc : (op1385StateHistories G v q) → Fin d, Function.Injective enc := by
  intro v q
  have : Fintype (op1385StateHistories G v q) := Fintype.ofFinite _
  have hcard : Fintype.card (op1385StateHistories G v q) ≤ d := by
    rw [Set.fintypeCard_eq_ncard]
    exact hbound v q
  refine ⟨Fin.castLE hcard ∘ (Fintype.equivFin _), ?_⟩
  exact (Fin.castLE_injective hcard).comp (Equiv.injective _)

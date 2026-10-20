import AFTD.Prelude
import AFTD.Kb.Tcs.MinBipartiteCactusNfaStates
import AFTD.Kb.Tcs.NfaTransitionGraph
import AFTD.Kb.Tcs.SimpleGraphIsCactus
import AFTD.Kb.Tcs.IsBipartiteCactusNfa

/-!
# min_bipartite_cactus_nfa_states_empty

Topic: automata   Node: b0bb3d744468

Provenance: formalization of a published result. Source: arXiv:2610.11717 Lemma 3.3

The empty language over any alphabet has a bipartite cactus NFA with at most one state.
-/

/-- The empty language has a bipartite cactus NFA with at most one state. -/
theorem min_bipartite_cactus_nfa_states_empty (α : Type*) :
    min_bipartite_cactus_nfa_states (0 : Language α) ≤ 1 := by
  have hm : 1 ∈ { k : ℕ | ∃ (σ : Type) (_ : Fintype σ) (A : NFA α σ),
      Fintype.card σ = k ∧ A.accepts = (0 : Language α) ∧ is_bipartite_cactus_nfa A } := by
    refine ⟨Unit, inferInstance, ⟨fun _ _ => ∅, ∅, ∅⟩, Fintype.card_unit, ?_, ?_⟩
    · rw [Language.zero_def]
      ext x
      simp [NFA.accepts]
    · dsimp [is_bipartite_cactus_nfa]
      have hbot : nfa_transition_graph (⟨fun _ _ => ∅, ∅, ∅⟩ : NFA α Unit) = ⊥ := by
        ext a b
        simp [nfa_transition_graph, SimpleGraph.fromRel]
      rw [hbot]
      constructor
      · intro u1 u2 p1 p2 h1 h2 he
        cases p1 with
        | nil => exact False.elim (h1.ne_nil rfl)
        | cons hadj _ => exact False.elim hadj
      · refine ⟨⟨fun _ => 0, fun hadj => False.elim hadj⟩⟩
  exact Nat.sInf_le hm

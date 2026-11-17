import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# prioritized_borel_encoded_arena_forward_deterministic

Topic: automata   Node: 57d945508275

Provenance: helper lemma. Block-encoded phase arena for arXiv:2611.10136, Conjecture 19.

In the phase-state encoded game, any two legal edges from the same state with the same branch direction have the same target state.
-/

theorem prioritized_borel_encoded_arena_forward_deterministic {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) :
    ∀ e ∈ (enc1385Game G).edges, ∀ e' ∈ (enc1385Game G).edges,
      e.source_node = e'.source_node → e.source_state = e'.source_state →
      e.dir = e'.dir → e.target_state = e'.target_state := by
  intro e he e' he' _ hs hd
  change e.target_state = enc1385Step G e.source_state e.dir ∧ _ at he
  change e'.target_state = enc1385Step G e'.source_state e'.dir ∧ _ at he'
  rw [he.1, he'.1, hs, hd]

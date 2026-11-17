import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelGame

/-!
# prioritized_borel_encoding_real_prefix_has_next

Topic: automata   Node: 6c8e1f6fa781

Provenance: helper lemma. Phase-state encoding for arXiv:2611.10136, Conjecture 19.

A proper prefix of the code of a legal edge always admits a real next encoding move at the matching source position.
-/

theorem prioritized_borel_encoding_real_prefix_has_next {Q : Type} [Fintype Q] (G : PrioritizedBorelGame Q 3) (s : Enc1385State Q) (e : TreeGameEdge Q 3) (he : e ∈ G.edges) (hv : e.source_node = s.origNode) (hq : e.source_state = s.origState) (hp : s.pending <+: enc1385Block e) (hlt : s.pending.length < Fintype.card Q + 1) : ∃ bit prio, enc1385Real G s bit prio := by
  classical
  have hb : (enc1385Block e).length = Fintype.card Q + 1 := by
    simp [enc1385Block, enc1385StateCode]
  obtain ⟨tail, ht⟩ := List.prefix_iff_exists_append_eq.mp hp
  cases tail with
  | nil =>
    simp only [List.append_nil] at ht
    rw [← ht] at hb
    omega
  | cons bit rest =>
    have hnext : s.pending ++ [bit] <+: enc1385Block e := by
      apply List.prefix_iff_exists_append_eq.mpr
      refine ⟨rest, ?_⟩
      simpa [List.append_assoc] using ht
    let p : Fin 3 := if (s.pending ++ [bit]).length = Fintype.card Q + 1 then e.prio else 0
    refine ⟨bit, p, e, he, hv, hq, hnext, ?_⟩
    dsimp [p]
    split <;> rfl

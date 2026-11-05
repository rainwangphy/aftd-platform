import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsDegenerate

/-!
# simple_graph_is_degenerate_bot

Topic: graphs   Node: 89eec080726b

Provenance: helper lemma. folklore

The empty graph on any vertex type V is k-degenerate for every natural number k.
-/

/-- The empty graph on any vertex type is k-degenerate for all k. -/
theorem simple_graph_is_degenerate_bot (V : Type*) (k : ℕ) :
    simple_graph_is_degenerate (⊥ : SimpleGraph V) k := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  refine ⟨v, hv, ?_⟩
  simp

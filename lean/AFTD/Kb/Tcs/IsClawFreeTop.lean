import AFTD.Prelude
import AFTD.Kb.Tcs.IsClawFree

/-!
# is_claw_free_top

Topic: graphs   Node: 9f4893bee61d

Provenance: helper lemma. folklore

Every complete graph is claw-free.
-/

/-- The complete graph on any vertex type is claw-free. -/
lemma is_claw_free_top {V : Type*} : IsClawFree (⊤ : SimpleGraph V) := by
  rintro ⟨f⟩
  -- the two leaves `inr 0` and `inr 1` are non-adjacent in K_{1,3}
  have hne : f (Sum.inr (0 : Fin 3)) ≠ f (Sum.inr (1 : Fin 3)) := by
    intro he
    have h2 := RelEmbedding.injective f he
    simp at h2
  -- but they are adjacent in the complete graph
  have hadj : (⊤ : SimpleGraph V).Adj (f (Sum.inr (0 : Fin 3))) (f (Sum.inr (1 : Fin 3))) := hne
  have h3 := (SimpleGraph.Embedding.map_adj_iff f).mp hadj
  simp [completeBipartiteGraph_adj] at h3

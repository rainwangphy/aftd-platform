import AFTD.Prelude
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869ExtendPredecessors
import AFTD.Kb.Tcs.Op869MemExtendPredecessors

/-!
# op869_graph_extend_predecessors

Topic: online_algorithms   Node: 6e0a6682c033

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

The padded predecessor graph is the original graph mapped into the larger vertex universe.
-/

/-- The padded predecessor graph is the original graph mapped into the larger vertex universe. -/
theorem op869_graph_extend_predecessors {n m : ℕ} (h : n ≤ m) (P : Fin n → Finset (Fin n)) :
    op869_graph_from_predecessors (op869_extend_predecessors h P) =
      (op869_graph_from_predecessors P).map (Fin.castLEEmb h) := by
  classical
  ext x y
  rw [SimpleGraph.map_adj]
  change ((x < y ∧ x ∈ op869_extend_predecessors h P y) ∨
    (y < x ∧ y ∈ op869_extend_predecessors h P x)) ↔ _
  constructor
  · rintro (⟨hxy, hmem⟩ | ⟨hyx, hmem⟩)
    · obtain ⟨a,b,hax,hby,hab⟩ := (op869_mem_extend_predecessors h P x y).mp hmem
      refine ⟨a,b, ?_, hax, hby⟩
      left
      constructor
      · rw [← hax, ← hby] at hxy
        exact hxy
      · exact hab
    · obtain ⟨b,a,hby,hax,hba⟩ := (op869_mem_extend_predecessors h P y x).mp hmem
      refine ⟨a,b, ?_, hax, hby⟩
      right
      constructor
      · rw [← hax, ← hby] at hyx
        exact hyx
      · exact hba
  · rintro ⟨a,b,hab,rfl,rfl⟩
    rcases hab with ⟨hab,hmem⟩ | ⟨hba,hmem⟩
    · left
      exact ⟨hab, (op869_mem_extend_predecessors h P _ _).mpr ⟨a,b,rfl,rfl,hmem⟩⟩
    · right
      exact ⟨hba, (op869_mem_extend_predecessors h P _ _).mpr ⟨b,a,rfl,rfl,hmem⟩⟩

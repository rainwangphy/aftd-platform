import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsSemicomplete
import AFTD.Kb.Tcs.DigraphIsCoBipartite

/-!
# digraph_semicomplete_is_co_bipartite

Topic: graphs   Node: 6119302376e6

Provenance: helper lemma. arXiv:2610.36895 Sec. 6

Every semicomplete digraph is co-bipartite.
-/

/-- Every semicomplete digraph is co-bipartite. -/
theorem digraph_semicomplete_is_co_bipartite {V : Type*} (D : Digraph V)
    (h : digraph_is_semicomplete D) : digraph_is_co_bipartite D := by
  obtain ⟨hloop, hsemi⟩ := h
  refine ⟨hloop, Set.univ, ∅, ?_, ?_, ?_, ?_⟩
  · intro v; exact Or.inl trivial
  · simp
  · intro u _ v _ huv; exact hsemi u v huv
  · intro u hu; simp at hu

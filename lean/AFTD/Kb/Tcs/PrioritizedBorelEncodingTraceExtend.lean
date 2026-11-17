import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Trace
import AFTD.Kb.Tcs.Enc1385Game
import AFTD.Kb.Tcs.TreeGameEdge

/-!
# prioritized_borel_encoding_trace_extend

Topic: automata   Node: 3a223e8e781c

Provenance: helper lemma. Phase-state encoding for arXiv:2611.10136, Conjecture 19.

Extending a state history by an edge extends its encoded node by the edge's direction-and-target block.
-/

theorem prioritized_borel_encoding_trace_extend {Q : Type} [Fintype Q] (v : List Bool) (h : Fin (v.length + 1) → Q) (e : TreeGameEdge Q 3) (h' : Fin ((v ++ [e.dir]).length + 1) → Q) (hpre : ∀ i : Fin (v.length + 1), h' ⟨i.val, by simp⟩ = h i) (hlast : h' (Fin.last (v ++ [e.dir]).length) = e.target_state) : enc1385Trace (v ++ [e.dir]) h' = enc1385Trace v h ++ enc1385Block e := by
  dsimp [enc1385Trace, enc1385Block]
  rw [← List.flatten_concat]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    rw [List.getElem_ofFn]
    by_cases hi : i < v.length
    · rw [List.getElem_append_left hi]
      rw [List.getElem_append_left (by simp [hi])]
      rw [List.getElem_ofFn]
      congr 2
      exact hpre ⟨i + 1, Nat.succ_lt_succ hi⟩
    · have hlt : i < v.length + 1 := by
        simpa using hi1
      have hieq : i = v.length := by omega
      subst hieq
      rw [List.getElem_append_right (le_refl _)]
      rw [List.getElem_append_right (by simp)]
      simp only [tsub_self]
      rw [List.getElem_singleton]
      rw [List.getElem_singleton]
      congr 2
      rw [← hlast]
      congr 1
      ext
      simp

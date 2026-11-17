import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelGame
import AFTD.Kb.Tcs.TreeGameEdge
import AFTD.Kb.Tcs.PrioritizedBorelReverseStateHistoriesUnique

/-!
# prioritized_borel_state_history_extend

Topic: automata   Node: 36d4a8fdd775

Provenance: helper lemma. History update in the bounded-state-history reduction for arXiv:2611.10136, Conjecture 19.

Any legal state history to a node and state extends along a legal outgoing edge to a legal state history at the child and target state, retaining all previously recorded states.
-/

theorem prioritized_borel_state_history_extend {Q : Type} {k : ℕ} (G : PrioritizedBorelGame Q k) (v : List Bool) (q : Q) (h : Fin (v.length + 1) → Q) (hh : h ∈ op1385StateHistories G v q) (e : TreeGameEdge Q k) (he : e ∈ G.edges) (hv : e.source_node = v) (hq : e.source_state = q) : ∃ h' ∈ op1385StateHistories G (v ++ [e.dir]) e.target_state, ∀ i : Fin (v.length + 1), h' ⟨i.val, by simp⟩ = h i := by
  let h' : Fin ((v ++ [e.dir]).length + 1) → Q := fun j =>
    if hj : j.val < v.length + 1 then h ⟨j.val, hj⟩ else e.target_state
  have h'_lt : ∀ (j : Fin ((v ++ [e.dir]).length + 1)) (hj : j.val < v.length + 1),
      h' j = h ⟨j.val, hj⟩ := fun j hj => dif_pos hj
  have h'_ge : ∀ (j : Fin ((v ++ [e.dir]).length + 1)) (hj : ¬ (j.val < v.length + 1)),
      h' j = e.target_state := fun j hj => dif_neg hj
  refine ⟨h', ⟨?_h_init, ?_h_last, ?_h_step⟩, ?_h_rest⟩
  case _h_init =>
    rw [h'_lt 0 (Nat.succ_pos _)]
    exact hh.1
  case _h_last =>
    apply h'_ge
    simp
  case _h_rest =>
    intro i
    apply h'_lt ⟨i.val, by simp⟩ i.is_lt
  case _h_step =>
    intro i
    by_cases hi : i.val < v.length
    · let i₀ : Fin v.length := ⟨i.val, hi⟩
      obtain ⟨e', he', hnode, hsrc, hdir, htgt⟩ := hh.2.2 i₀
      refine ⟨e', he', ?_, ?_, ?_, ?_⟩
      · rw [hnode]
        exact (List.take_append_of_le_length (by omega)).symm
      · rw [hsrc]
        have h1 : i.castSucc.val < v.length + 1 := by simp; omega
        rw [h'_lt i.castSucc h1]
        congr 1
      · rw [hdir]
        rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_append_left hi]
      · rw [htgt]
        have h2 : i.succ.val < v.length + 1 := by simp; omega
        rw [h'_lt i.succ h2]
        congr 1
    · have hi_le : i.val ≤ v.length := by
        have := i.is_lt
        simp at this
        exact this
      have hi_eq : i.val = v.length := by omega
      have hi_fin : i = ⟨v.length, by simp⟩ := Fin.ext hi_eq
      subst hi_fin
      refine ⟨e, he, ?_, ?_, ?_, ?_⟩
      · rw [hv]
        simp
      · rw [hq, ← hh.2.1]
        have h1 : (⟨v.length, by simp⟩ : Fin (v ++ [e.dir]).length).castSucc.val < v.length + 1 := by simp
        rw [h'_lt _ h1]
        congr 1
      · simp [List.get_eq_getElem]
      · rw [h'_ge _ (by simp)]

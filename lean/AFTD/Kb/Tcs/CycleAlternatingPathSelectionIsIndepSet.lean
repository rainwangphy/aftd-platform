import AFTD.Prelude
import AFTD.Kb.Tcs.CycleAlternatingPathSelectionIndependent
import AFTD.Kb.Tcs.AlternatingPathSelectedSet

/-!
# cycle_alternating_path_selection_isIndepSet

Topic: graphs   Node: d33d79d296b5

Provenance: helper lemma. arXiv:2611.06985 Lemma 3.3

Let C be a simple graph on vertex type V and ρ : V a vertex such that (C.induce ({ρ}ᶜ : Set V)).IsBipartiteWith A B holds for subsets A, B of the subtype {ρ}ᶜ. For any subset T ⊆ B, the image under Subtype.val of the alternating path selected set alternating_path_selected_set C ρ A T is an independent set in C (that is, C.IsIndepSet (Subtype.val '' alternating_path_selected_set C ρ A T)).
-/

/-- The image of the alternating path selected set S in V is an independent set of C in the sense of SimpleGraph.IsIndepSet. -/
theorem cycle_alternating_path_selection_isIndepSet {V : Type*} (C : SimpleGraph V) (ρ : V)
    (A B : Set ({ρ}ᶜ : Set V))
    (h_bip : (C.induce ({ρ}ᶜ : Set V)).IsBipartiteWith A B)
    (T : Set ({ρ}ᶜ : Set V)) (hT : T ⊆ B) :
    C.IsIndepSet (Subtype.val '' alternating_path_selected_set C ρ A T) := by
  intro x hx y hy hxy
  simp only [Set.mem_image] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact cycle_alternating_path_selection_independent C ρ A B h_bip T hT a ha b hb

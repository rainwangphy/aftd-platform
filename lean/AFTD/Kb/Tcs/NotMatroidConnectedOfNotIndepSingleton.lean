import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidConnected

/-!
# not_matroid_connected_of_not_indep_singleton

Topic: algorithms   Node: 5e81d246ca43

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

A matroid with a loop e (the set {e} is dependent) and another ground element f ≠ e is not connected.
-/

theorem not_matroid_connected_of_not_indep_singleton {α : Type*} (M : Matroid α) (e f : α)
    (he : e ∈ M.E) (hf : f ∈ M.E) (hef : e ≠ f) (hd : ¬ M.Indep {e}) : ¬ matroid_connected M := by
  intro h
  rcases h e he f hf with h | ⟨C, hC, heC, hfC⟩
  · exact hef h
  · have hdep : M.Dep {e} := by
      rw [Matroid.Dep]; exact ⟨hd, by simpa using he⟩
    have hsub : C ⊆ {e} := hC.2 hdep (Set.singleton_subset_iff.2 heC)
    have hfe : f = e := by simpa using hsub hfC
    exact hef hfe.symm

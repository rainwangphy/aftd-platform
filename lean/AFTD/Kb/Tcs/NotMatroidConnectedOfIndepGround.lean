import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidConnected

/-!
# not_matroid_connected_of_indep_ground

Topic: algorithms   Node: 9488e03c04c3

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

A free matroid (its ground set is independent) with two distinct ground elements is not connected.
-/

theorem not_matroid_connected_of_indep_ground {α : Type*} (M : Matroid α) (e f : α)
    (he : e ∈ M.E) (hf : f ∈ M.E) (hef : e ≠ f) (hd : M.Indep M.E) : ¬ matroid_connected M := by
  intro h
  rcases h e he f hf with h | ⟨C, hC, -, -⟩
  · exact hef h
  · exact hC.not_indep (hd.subset hC.subset_ground)

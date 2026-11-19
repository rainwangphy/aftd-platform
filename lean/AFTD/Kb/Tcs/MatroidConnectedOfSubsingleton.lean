import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidConnected

/-!
# matroid_connected_of_subsingleton

Topic: algorithms   Node: 8911405cba1a

Provenance: helper lemma. Sanity lemma / helper for the statements of OP-1998 (arXiv:2611.23624 (Matroid Connectedness and Component Decomposition: Breaking the Quadratic Barrier))

A matroid whose ground set has at most one element is connected.
-/

theorem matroid_connected_of_subsingleton {α : Type*} (M : Matroid α) (h : M.E.Subsingleton) :
    matroid_connected M := by
  intro e he f hf
  exact Or.inl (h he hf)

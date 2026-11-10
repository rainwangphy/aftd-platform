import AFTD.Prelude
import AFTD.Kb.Tcs.IsMutualVisibilitySet

/-!
# mutual_visibility_number

Topic: graphs   Node: 6a8692bd7056

Provenance: formalization of a published result. Source: arXiv:2611.09513, Section 1

The mutual-visibility number of a finite graph G is the maximum size of a mutual-visibility set of vertices in G.
-/

/-- The mutual-visibility number of a finite simple graph is the maximum cardinality of a mutual-visibility set. -/
noncomputable def mutual_visibility_number {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := sSup {n | ∃ s : Finset V, is_mutual_visibility_set G (s : Set V) ∧ s.card = n}

import AFTD.Prelude
import AFTD.Kb.Tcs.IsLinearForest

/-!
# max_induced_linear_forest

Topic: graphs   Node: 66aa3fba9eb7

Provenance: formalization of a published result. Source: arXiv:2611.12781 Section 1

The maximum order of an induced linear forest in a finite simple graph G on a finite vertex type V is the supremum in ℕ of the cardinalities of all vertex subsets s : Finset V such that the induced subgraph on s is a linear forest.
-/

/-- The maximum order of an induced linear forest in a finite graph G. -/
noncomputable def max_induced_linear_forest {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := sSup {n : ℕ | ∃ s : Finset V, is_linear_forest (G.induce (s : Set V)) ∧ s.card = n}

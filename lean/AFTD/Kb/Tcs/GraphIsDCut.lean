import AFTD.Prelude

/-!
# graph_is_d_cut

Topic: graphs   Node: 0294ef678b4f

Provenance: formalization of a published result. Source: arXiv:2611.26556 Section 1

A subset A of vertices is a d-cut of a finite simple graph G if both A and its complement are nonempty, each vertex in A has at most d neighbors outside A, and each vertex outside A has at most d neighbors in A.
-/

/-- A subset of vertices is a d-cut of a simple graph if both parts are nonempty and each vertex has at most d crossing edges. -/
def graph_is_d_cut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) (A : Finset V) : Prop :=
  open scoped Classical in
  A.Nonempty ∧ (Aᶜ : Finset V).Nonempty ∧
  (∀ u ∈ A, (G.neighborFinset u \ A).card ≤ d) ∧
  (∀ v ∈ Aᶜ, (G.neighborFinset v ∩ A).card ≤ d)

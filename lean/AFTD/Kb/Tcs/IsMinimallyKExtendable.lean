import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# is_minimally_k_extendable

Topic: graphs   Node: 1c17067f8de8

Provenance: formalization of a published result. Source: arXiv:2611.22690, Section 2 (definition of minimally k-extendable graphs)

For a finite vertex type V (with [Fintype V]), a simple graph G : SimpleGraph V and k : ℕ, is_minimally_k_extendable G k is the Prop is_k_extendable G k ∧ ∀ e ∈ G.edgeSet, ¬ is_k_extendable (G.deleteEdges {e}) k: G is k-extendable and deleting any single edge e of G gives a graph that is not k-extendable.
-/

/-- G is minimally k-extendable: k-extendable, and G - e is not k-extendable for every edge e. -/
def is_minimally_k_extendable {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  is_k_extendable G k ∧ ∀ e ∈ G.edgeSet, ¬ is_k_extendable (G.deleteEdges {e}) k

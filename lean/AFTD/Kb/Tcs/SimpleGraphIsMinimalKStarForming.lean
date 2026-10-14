import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsKStarForming

/-!
# simple_graph_is_minimal_k_star_forming

Topic: graphs   Node: f3c6a35c401f

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Definition 2.1 (minimality).

A minimal k-star-forming set: a k-star-forming set no proper subset of which is k-star-forming.
-/

/-- A minimal `k`-star-forming set: `k`-star-forming, and no proper subset is. -/
def simple_graph_is_minimal_k_star_forming {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (S : Finset V) : Prop :=
  simple_graph_is_k_star_forming G k S ∧ ∀ T ⊂ S, ¬ simple_graph_is_k_star_forming G k T

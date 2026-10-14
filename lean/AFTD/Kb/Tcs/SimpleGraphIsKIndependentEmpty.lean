import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsKIndependent

/-!
# simple_graph_is_k_independent_empty

Topic: graphs   Node: c58404b7c615

Provenance: helper lemma. Sanity lemma for the definition of k-independence, arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination).

The empty vertex set is k-independent, for every k.
-/

theorem simple_graph_is_k_independent_empty {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    simple_graph_is_k_independent G k ∅ := by
  intro v hv; simp at hv

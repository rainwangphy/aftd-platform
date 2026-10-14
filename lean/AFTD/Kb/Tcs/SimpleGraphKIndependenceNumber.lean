import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsKIndependent

/-!
# simple_graph_k_independence_number

Topic: graphs   Node: 6b086634b64e

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Sec. 1 (β_k).

β_k(G): the maximum cardinality of a k-independent vertex set of G.
-/

/-- `β_k(G)`: the maximum cardinality of a `k`-independent vertex set. -/
noncomputable def simple_graph_k_independence_number {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sSup {n | ∃ I : Finset V, simple_graph_is_k_independent G k I ∧ I.card = n}

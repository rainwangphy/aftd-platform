import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMinimalKStarForming

/-!
# simple_graph_upper_k_star_forming_number

Topic: graphs   Node: 5bdf9e9fb6b0

Provenance: formalization of a published result. Source: arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Definition 2.1 (SF_k).

SF_k(G): the maximum cardinality of a minimal k-star-forming vertex set of G.
-/

/-- `SF_k(G)`: the maximum cardinality of a minimal `k`-star-forming vertex set. -/
noncomputable def simple_graph_upper_k_star_forming_number {V : Type*} (G : SimpleGraph V)
    (k : ℕ) : ℕ :=
  sSup {n | ∃ S : Finset V, simple_graph_is_minimal_k_star_forming G k S ∧ S.card = n}

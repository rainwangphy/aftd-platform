import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsSemisaturating
import AFTD.Kb.Tcs.DigraphEdgeCount

/-!
# digraph_ssat

Topic: graphs   Node: a529f9eb277e

Provenance: formalization of a published result. Source: arXiv:2610.18600 Definition 1.2

For a natural number n and a digraph G : Digraph V on vertex type V, digraph_ssat n G is the infimum of the set of all natural numbers k : ℕ for which there exists a digraph H : Digraph (Fin n) and an instance d : DecidableRel H.Adj such that digraph_is_semisaturating H G holds and digraph_edge_count H = k.
-/

/-- The semisaturation function ssat(n, G) is the minimum number of edges in an n-vertex host graph semisaturating G. -/
noncomputable def digraph_ssat {V : Type*} (n : ℕ) (G : Digraph V) : ℕ := sInf { k : ℕ | ∃ H : Digraph (Fin n), ∃ _ : DecidableRel H.Adj, digraph_is_semisaturating H G ∧ digraph_edge_count H = k }

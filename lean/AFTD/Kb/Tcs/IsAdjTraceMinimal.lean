import AFTD.Prelude
import AFTD.Kb.Tcs.GraphAdjTraceSeq
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# is_adj_trace_minimal

Topic: graphs   Node: f90790864d59

Provenance: formalization of a published result. Source: arXiv:2610.36127 Definition 14

A graph G on a finite vertex set V is trace-minimal in the class of d-regular graphs if G is d-regular and its adjacency trace sequence is lexicographically less than or equal to the adjacency trace sequence of every d-regular graph on V.
-/

open scoped Classical in
/-- A d-regular graph G is trace-minimal if its adjacency trace sequence is lexicographically minimal among all d-regular graphs on the same vertex set. -/
def is_adj_trace_minimal {V : Type*} [Fintype V] (d : ℕ) (G : SimpleGraph V) : Prop :=
  open scoped Classical in
  G.IsRegularOfDegree d ∧
    ∀ H : SimpleGraph V, H.IsRegularOfDegree d →
      toLex (graph_adj_trace_seq G) ≤ toLex (graph_adj_trace_seq H)

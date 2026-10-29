import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLapTraceSeq
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# is_lap_trace_minimal

Topic: graphs   Node: 16476bb8fc7b

Provenance: formalization of a published result. Source: arXiv:2610.36127 Definition 31

A graph G on a finite vertex set V is Laplacian trace-minimal in the class of d-regular graphs if G is d-regular and its Laplacian trace sequence is lexicographically less than or equal to the Laplacian trace sequence of every d-regular graph on V.
-/

open scoped Classical in
/-- A d-regular graph G is Laplacian trace-minimal if its Laplacian trace sequence is lexicographically minimal among all d-regular graphs on the same vertex set. -/
def is_lap_trace_minimal {V : Type*} [Fintype V] (d : ℕ) (G : SimpleGraph V) : Prop :=
  open scoped Classical in
  G.IsRegularOfDegree d ∧
    ∀ H : SimpleGraph V, H.IsRegularOfDegree d →
      toLex (graph_lap_trace_seq G) ≤ toLex (graph_lap_trace_seq H)

import AFTD.Prelude
import AFTD.Kb.Tcs.IsFactorCritical

/-!
# IsMinimalFactorCritical

Topic: graphs   Node: 2431622d3412

Provenance: formalization of a published result. Source: arXiv:2611.09072 Section 1

A simple graph G on a vertex type V is minimal factor-critical if G is factor-critical and for every edge e ∈ G.edgeSet, the graph G.deleteEdges {e} obtained by deleting e is not factor-critical.
-/

/-- A simple graph is minimal factor-critical if it is factor-critical and deleting any edge destroys factor-criticality. -/
def IsMinimalFactorCritical {V : Type*} (G : SimpleGraph V) : Prop := IsFactorCritical G ∧ ∀ e ∈ G.edgeSet, ¬ IsFactorCritical (G.deleteEdges {e})

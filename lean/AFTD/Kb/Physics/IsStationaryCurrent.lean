import AFTD.Prelude
import AFTD.Kb.Physics.SimpleGraphOrientation

/-!
# is_stationary_current

Topic: statistical_mechanics   Node: ef89db022b21

Provenance: formalization of a published result. Source: Bollobás, Modern Graph Theory (1998), Chapter II.1

A current j on the edges of an oriented finite simple graph G is stationary if at every vertex, the sum of currents leaving the vertex minus the sum of currents entering the vertex is zero.
-/

/-- A current on an oriented simple graph is stationary (a circulation) if the net outgoing current at each vertex is zero. -/
def is_stationary_current {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (o : SimpleGraphOrientation G) (j : G.edgeFinset → ℝ) : Prop := ∀ v : V, ∑ e : G.edgeFinset,
    ((if (o.dir e).1 = v then j e else 0) - (if (o.dir e).2 = v then j e else 0)) = 0

import AFTD.Prelude
import AFTD.Kb.Physics.IsStationaryCurrent
import AFTD.Kb.Physics.IsHalfIntegralCurrent
import AFTD.Kb.Physics.SimpleGraphOrientation

/-!
# cubic_half_integral_saturated_edges_min

Topic: statistical_mechanics   Node: 99b817262dc2

Provenance: formalization of a published result. Source: arXiv:2204.00875

For a finite simple graph G with decidable equality and adjacency, and an orientation o of G, the invariant b(G) is the infimum in the natural numbers of the number of edges e with |j(e)| = 1 among all half-integral stationary currents j on G.edgeFinset with sum of |j(e)| equal to the number of vertices.
-/

/-- Minimum number b(G) of saturated edges among half-integral stationary currents with total current n. -/
noncomputable def cubic_half_integral_saturated_edges_min {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (o : SimpleGraphOrientation G) : ℕ := sInf { (∑ e : G.edgeFinset, if |j e| = 1 then (1 : ℕ) else 0) |
    (j : G.edgeFinset → ℝ) (_ : is_stationary_current G o j)
    (_ : is_half_integral_current G j)
    (_ : ∑ e : G.edgeFinset, |j e| = Fintype.card V) }

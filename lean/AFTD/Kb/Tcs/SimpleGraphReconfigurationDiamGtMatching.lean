import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphReconfigurationGraph
import AFTD.Kb.Tcs.GraphMatchingNum

/-!
# simple_graph_reconfiguration_diam_gt_matching

Topic: graphs   Node: 07d3f5b7a2dd

Provenance: formalization of a published result. Source: arXiv:2611.17022 Sec. 8, Question 3

The predicate on a natural number Δ asserting that there exists a finite simple graph G on a finite type V with decidable equality and decidable adjacency such that G has maximum degree equal to Δ and the sum of the cardinality of V (coerced to ℕ∞) and the matching number graph_matching_num G is strictly less than the diameter of the (Δ+2)-colouring reconfiguration graph (simple_graph_reconfiguration_graph G (Δ + 2)).diam.
-/

/-- Predicate on Δ : ℕ asserting existence of a finite graph with maxDegree Δ whose (Δ+2)-recoloring diameter exceeds |V| + μ. -/
def simple_graph_reconfiguration_diam_gt_matching (Δ : ℕ) : Prop := ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    G.maxDegree = Δ ∧
    (Fintype.card V : ℕ∞) + graph_matching_num G < (simple_graph_reconfiguration_graph G (Δ + 2)).diam

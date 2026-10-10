import AFTD.Prelude
import AFTD.Kb.Tcs.GraphLlyCurvature
import AFTD.Kb.Tcs.GraphWassersteinDistComm
import AFTD.Kb.Tcs.GraphOllivierCurvature
import AFTD.Kb.Tcs.GraphWassersteinDist
import AFTD.Kb.Tcs.GraphIdleMeasure

/-!
# graph_lly_curvature_comm

Topic: graphs   Node: 49ada469d5b5

Provenance: helper lemma. Helper for the refutation of OP-165 (arXiv:2610.10559, after Theorem 1.4).

The Lin–Lu–Yau curvature is symmetric: κ_LLY(x, y) = κ_LLY(y, x).
-/

theorem graph_lly_curvature_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    graph_lly_curvature G x y = graph_lly_curvature G y x := by
  unfold graph_lly_curvature graph_ollivier_curvature
  congr 1
  funext α
  rw [graph_wasserstein_dist_comm, SimpleGraph.dist_comm]

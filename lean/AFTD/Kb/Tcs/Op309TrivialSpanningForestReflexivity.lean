import AFTD.Prelude
import AFTD.Kb.Tcs.MaxDegreeLeTwoExistsRichNeighborFiveColoring
import AFTD.Kb.Tcs.SimpleGraphExistsEdgeTailCapacity

/-!
# op309_trivial_spanning_forest_reflexivity

Topic: graphs   Node: 57985825f319

Provenance: helper lemma. OP-309 reconfiguration barrier, IN-1099; independent-center high-girth factor experiment 36601.

The selected edge set equals itself; this is a tautology and does not assert rigidity of two forests.
-/

/-- Tautological self-equality retained after correcting an unfaithful auxiliary statement. -/
theorem op309_trivial_spanning_forest_reflexivity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htriangle : ∀ u v w, G.Adj u v → G.Adj v w → ¬ G.Adj w u)
    (R R' : Finset G.edgeSet)
    (hspan : ∀ v : V, (R.filter fun e => v ∈ e.1).Nonempty)
    (hspan' : ∀ v : V, (R'.filter fun e => v ∈ e.1).Nonempty)
    (hpair : ∀ e ∈ R, (R.filter fun f => G.lineGraph.Adj e f).card = 1)
    (hpair' : ∀ e ∈ R', (R'.filter fun f => G.lineGraph.Adj e f).card = 1)
    (hdel : (R \ R').card ≤ 1) (hadd : (R' \ R).card ≤ 1) : R = R := by rfl

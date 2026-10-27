import AFTD.Prelude
import AFTD.Kb.Tcs.WiringDiagramPair
import AFTD.Kb.Tcs.BruhatOrderThreeGraph
import AFTD.Kb.Tcs.OrderedTriple
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.IsRankThreeSignotope
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# wiring_diagram_zero_excess

Topic: np_completeness   Node: e7d86696e3a8

Provenance: formalization of a published result. Source: arXiv:2610.03808 Sec. 2.2

A pair of wiring diagrams (represented as rank-3 signotopes) has braid-move excess 0 if their distance in the higher Bruhat graph B(m, 2) equals their Hamming distance, namely the number of ordered triples where they differ.
-/

/-- A pair of wiring diagrams has braid-move excess 0 if its graph distance in B(m, 2) equals its Hamming distance. -/
def wiring_diagram_zero_excess (inst : WiringDiagramPair) : Prop :=
  (bruhat_order_three_graph (Fin inst.m)).dist ⟨inst.u, inst.hu⟩ ⟨inst.v, inst.hv⟩ =
    {t : OrderedTriple (Fin inst.m) | inst.u t ≠ inst.v t}.ncard

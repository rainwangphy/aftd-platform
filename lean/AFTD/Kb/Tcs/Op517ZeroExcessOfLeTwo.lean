import AFTD.Prelude
import AFTD.Kb.Tcs.Op517ZeroExcessOfEqPair
import AFTD.Kb.Tcs.WiringDiagramPair
import AFTD.Kb.Tcs.OrderedTriple
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.WiringDiagramZeroExcess

/-!
# op_517_zero_excess_of_le_two

Topic: np_completeness   Node: 57441170454c

Provenance: helper lemma. arXiv:2610.03808

For any instance inst of WiringDiagramPair on m pseudolines with m ≤ 2, there are no ordered triples in Fin m, so inst.u = inst.v holds vacuously and therefore inst has braid-move excess 0 (wiring_diagram_zero_excess inst).
-/

/-- Every pair of wiring diagrams on m ≤ 2 wires has braid-move excess 0. -/
theorem op_517_zero_excess_of_le_two (inst : WiringDiagramPair) (h : inst.m ≤ 2) : wiring_diagram_zero_excess inst := by
  apply op_517_zero_excess_of_eq_pair
  ext t
  have : t.a.val < t.b.val := t.ab
  have : t.b.val < t.c.val := t.bc
  have : t.c.val < inst.m := t.c.isLt
  omega

import AFTD.Prelude
import AFTD.Kb.Tcs.WiringDiagramPair
import AFTD.Kb.Tcs.IsRankThreeSignotope
import AFTD.Kb.Tcs.OrderedTriple
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.WiringDiagramZeroExcess
import AFTD.Kb.Tcs.BruhatOrderThreeGraph

/-!
# op_517_zero_excess_of_eq_pair

Topic: np_completeness   Node: 261fde6524e2

Provenance: helper lemma. arXiv:2610.03808

For any instance inst of WiringDiagramPair, if the two signotopes inst.u and inst.v are equal, then inst has braid-move excess 0 (wiring_diagram_zero_excess inst): the distance is 0 and the number of differing triples is 0.
-/

/-- Any pair of identical wiring diagrams has braid-move excess 0. -/
theorem op_517_zero_excess_of_eq_pair (inst : WiringDiagramPair) (h : inst.u = inst.v) : wiring_diagram_zero_excess inst := by
  unfold wiring_diagram_zero_excess
  have h_eq : (⟨inst.u, inst.hu⟩ : { u // is_rank_three_signotope u }) = ⟨inst.v, inst.hv⟩ := Subtype.ext h
  rw [h_eq, SimpleGraph.dist_self]
  have h_set : {t | inst.u t ≠ inst.v t} = ∅ := by
    ext t
    simp [h]
  rw [h_set, Set.ncard_empty]

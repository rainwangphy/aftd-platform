import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedTriple
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.WiringDiagramZeroExcess
import AFTD.Kb.Tcs.IsRankThreeSignotope
import AFTD.Kb.Tcs.WiringDiagramPair
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.DiffersAtOne
import AFTD.Kb.Tcs.BruhatOrderThreeGraph

/-!
# op_517_zero_excess_of_adj

Topic: np_completeness   Node: 5e490aacee03

Provenance: helper lemma. arXiv:2610.03808

If two wiring diagrams (represented as rank-3 signotopes u and v on Fin m) are adjacent in the higher Bruhat graph bruhat_order_three_graph (Fin m), then they have braid-move excess 0: their graph distance is 1, which equals the number of triples on which they differ.
-/

/-- Two wiring diagrams that are adjacent in the higher Bruhat graph differ at exactly one triple, hence have excess 0. -/
theorem op_517_zero_excess_of_adj (inst : WiringDiagramPair) (h : (bruhat_order_three_graph (Fin inst.m)).Adj ⟨inst.u, inst.hu⟩ ⟨inst.v, inst.hv⟩) : wiring_diagram_zero_excess inst := by
  dsimp [wiring_diagram_zero_excess]
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr h]
  have hdiff : differs_at_one inst.u inst.v := h
  obtain ⟨t, ht, hunique⟩ := hdiff
  have heq : {t' : OrderedTriple (Fin inst.m) | inst.u t' ≠ inst.v t'} = {t} := by
    ext y
    exact ⟨fun hy => Set.mem_singleton_iff.mpr (hunique y hy), fun hy => (Set.mem_singleton_iff.mp hy).symm ▸ ht⟩
  rw [heq, Set.ncard_singleton]

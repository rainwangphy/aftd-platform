import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsPlanar
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower
import AFTD.Kb.Tcs.CycleSevenAllPowersWellCovered
import AFTD.Kb.Tcs.CycleSevenDiamEqThree
import AFTD.Kb.Tcs.CycleSevenIsPlanar

/-!
# exists_planar_all_powers_well_covered_diam_eq_three

Topic: graphs   Node: 45aacd8d1b62

Provenance: original. Related work: arXiv:2610.09300 Example 3.8; OP-537

There exists a finite connected simple planar graph G with at least two vertices whose diameter is exactly 3 and such that every positive integer power G^d (for d ≥ 1) is well-covered.
-/

/-- Sharpness of the diameter bound in OP-537: there exists a connected planar graph of diameter 3 with all powers well-covered. -/
theorem exists_planar_all_powers_well_covered_diam_eq_three :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      G.Connected ∧
      simple_graph_is_planar G ∧
      2 ≤ Fintype.card V ∧
      G.diam = 3 ∧
      (∀ d : ℕ, 1 ≤ d → simple_graph_is_well_covered (simple_graph_power G d)) := by
  refine ⟨Fin 7, inferInstance, SimpleGraph.cycleGraph 7, ?_, ?_, ?_, ?_, ?_⟩
  · exact SimpleGraph.cycleGraph_connected
  · exact cycle_seven_is_planar
  · simp
  · exact cycle_seven_diam_eq_three
  · exact cycle_seven_all_powers_well_covered

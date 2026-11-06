import AFTD.Prelude
import AFTD.Kb.Tcs.F2CubicEdgeCondition

/-!
# f2CubicConditionCount

Topic: quantum   Node: 0c176c8fac83

Provenance: helper lemma. step towards op_1254_cubic_hypergraph_fluctuation_mean_zero

The number of pairs (u, y) with u : (Fin 2)^n and y : Fin 4 → (Fin 2)^n satisfying the fourth-moment evenness condition f2CubicEdgeCondition u y.
-/

/-- Count of tuples satisfying the fourth-moment evenness condition. -/
noncomputable def f2CubicConditionCount (n : ℕ) : ℕ := by classical exact ((Finset.univ : Finset ((Fin n → Fin 2) × (Fin 4 → Fin n → Fin 2))).filter (fun (t : (Fin n → Fin 2) × (Fin 4 → Fin n → Fin 2)) => f2CubicEdgeCondition t.1 t.2)).card

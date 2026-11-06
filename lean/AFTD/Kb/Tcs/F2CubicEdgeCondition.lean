import AFTD.Prelude
import AFTD.Kb.Tcs.CubicEdge

/-!
# f2CubicEdgeCondition

Topic: quantum   Node: dae9a0ca0b26

Provenance: helper lemma. step towards op_1254_cubic_hypergraph_fluctuation_mean_zero

The F₂ 'fourth-moment evenness' predicate: given u : (Fin 2)^n and y : Fin 4 → (Fin 2)^n, one has y 3 = y 0 + y 1 + y 2 and, for every 3-subset e of Fin n, the integer ∑_{i : Fin 4} (∏_{j ∈ e} (y i j) + ∏_{j ∈ e} (y i + u) j) is even.
-/

/-- Predicate whose fibre count equals the value of the Pauli fourth-moment integral up to (2^n)^{-3}. -/
noncomputable def f2CubicEdgeCondition {n : ℕ} (u : Fin n → Fin 2) (y : Fin 4 → Fin n → Fin 2) : Prop := y 3 = y 0 + y 1 + y 2 ∧ ∀ e : CubicEdge n, Even (∑ i : Fin 4, ((∏ j ∈ (e : Finset (Fin n)), (y i j).val) + (∏ j ∈ (e : Finset (Fin n)), ((y i + u) j).val)))

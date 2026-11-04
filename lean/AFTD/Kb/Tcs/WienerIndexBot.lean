import AFTD.Prelude
import AFTD.Kb.Tcs.WienerIndex

/-!
# wiener_index_bot

Topic: graphs   Node: f97715ae195b

Provenance: helper lemma. folklore

The Wiener index of the empty graph on any finite vertex type is zero.
-/

/-- The Wiener index of the empty graph (bot) is 0. -/
theorem wiener_index_bot {V : Type*} [Fintype V] :
    wiener_index (⊥ : SimpleGraph V) = 0 := by
  rw [wiener_index]
  apply Finset.sum_eq_zero
  intro e _
  induction e using Sym2.ind with
  | _ u v => simp [SimpleGraph.dist_bot]

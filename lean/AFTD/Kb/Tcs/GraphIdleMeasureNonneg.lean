import AFTD.Prelude
import AFTD.Kb.Tcs.GraphIdleMeasure

/-!
# graph_idle_measure_nonneg

Topic: graphs   Node: 6c81dfe8995e

Provenance: helper lemma. Helper for the refutation of OP-165 (arXiv:2610.10559, after Theorem 1.4).

μ_x^α is nonnegative for 0 ≤ α ≤ 1.
-/

theorem graph_idle_measure_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (x v : V) :
    0 ≤ graph_idle_measure G α x v := by
  unfold graph_idle_measure
  split_ifs
  · exact hα0
  · exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  · exact le_rfl

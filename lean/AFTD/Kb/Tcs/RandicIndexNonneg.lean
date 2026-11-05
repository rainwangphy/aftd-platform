import AFTD.Prelude
import AFTD.Kb.Tcs.RandicIndex

/-!
# randic_index_nonneg

Topic: graphs   Node: 35b40e9adaca

Provenance: helper lemma. arXiv:2611.03879 Lemma 15

For any finite simple graph G on a finite vertex type V, its Randić index is non-negative: 0 ≤ randic_index G.
-/

attribute [local instance] Classical.propDecidable in
/-- The Randić index of any finite simple graph is non-negative. -/
theorem randic_index_nonneg {V : Type*} [Fintype V] (G : SimpleGraph V) :
  0 ≤ randic_index G := by
  unfold randic_index
  apply Finset.sum_nonneg
  intro e _
  induction e using Sym2.inductionOn with
  | hf u v =>
    simp only [Sym2.lift_mk]
    exact one_div_nonneg.mpr (Real.sqrt_nonneg _)

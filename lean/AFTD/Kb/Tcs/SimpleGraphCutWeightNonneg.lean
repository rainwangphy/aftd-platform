import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCutWeight

/-!
# simple_graph_cut_weight_nonneg

Topic: graphs   Node: 9ebc31c896c0

Provenance: helper lemma. folklore

In any simple graph G on a finite type V with decidable equality and decidable adjacency, with edge weighting w : G.edgeSet → ℝ satisfying w e ≥ 0 for all edges e, the cut weight simple_graph_cut_weight G w S is nonnegative for every vertex subset S : Finset V.
-/

/-- Nonnegative edge weights yield a nonnegative cut weight for every vertex set. -/
theorem simple_graph_cut_weight_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : G.edgeSet → ℝ) (hw : ∀ e, 0 ≤ w e) (S : Finset V) :
    0 ≤ simple_graph_cut_weight G w S := by
  unfold simple_graph_cut_weight
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact hw e
  · rfl

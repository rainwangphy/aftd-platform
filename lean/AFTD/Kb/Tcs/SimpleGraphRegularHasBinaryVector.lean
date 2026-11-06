import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphOnesMemRangeImpHasBinaryVector

/-!
# simple_graph_regular_has_binary_vector

Topic: graphs   Node: e10115214e4c

Provenance: original. Related work: arXiv:2611.08244 Thm 2.5

For any nonempty finite simple graph G that is regular of degree d with 0 < d, there exists a non-zero (0,1)-vector in the row space of G.adjMatrix ℝ over ℝ that does not equal any row of G.adjMatrix ℝ.
-/

/-- Every finite regular simple graph with positive degree has a non-zero (0,1)-vector in its adjacency row space that does not occur as a row. -/
theorem simple_graph_regular_has_binary_vector
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hd : 0 < d)
    (hreg : G.IsRegularOfDegree d) :
    ∃ y : V → ℝ, (∀ v : V, y v = 0 ∨ y v = 1) ∧ y ≠ 0 ∧
      y ∈ LinearMap.range (Matrix.toLin' (G.adjMatrix ℝ)) ∧
      ∀ u : V, y ≠ G.adjMatrix ℝ u := by
  apply simple_graph_ones_mem_range_imp_has_binary_vector
  refine ⟨Function.const V ((d : ℝ)⁻¹), ?_⟩
  ext v
  rw [Matrix.toLin'_apply]
  rw [SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (d := d)
    (a := ((d : ℝ)⁻¹)) hreg]
  exact mul_inv_cancel₀ (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hd))

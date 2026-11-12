import AFTD.Prelude
import AFTD.Kb.Tcs.Op223ExampleGraph
import AFTD.Kb.Tcs.AdjacencySpectralRadius
import AFTD.Kb.Tcs.Op223MatrixSpectralLower
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op223_first_replacement_spectral_lower

Topic: graphs   Node: 55072d172f1f

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; experiments 22883 and 22914

Replacing edge 0-1 with 4-2 in the example tree yields a graph whose spectral radius is greater than 209/100.
-/

open Matrix
open scoped ENNReal
open scoped Classical

noncomputable def example_witness_graph : SimpleGraph (Fin 8) :=
  op223_example_graph.deleteEdges {s(0, 1)} ⊔ SimpleGraph.fromEdgeSet {s(4, 2)}

noncomputable def example_witness_vector : Fin 8 → ℝ :=
  ![3505, 2115, 4700, 2115, 6210, 2795, 2795, 1578]

noncomputable def example_witness_matrix : Matrix (Fin 8) (Fin 8) ℝ :=
  ![![0, 0, 0, 0, 1, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 1, 1, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0]]


set_option maxHeartbeats 3000000 in
lemma example_witness_hmat : example_witness_graph.adjMatrix ℝ = example_witness_matrix := by
  ext i j
  simp only [SimpleGraph.adjMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [example_witness_matrix, example_witness_graph, op223_example_graph,
      SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj, Sym2.eq] <;> decide

set_option maxHeartbeats 3000000 in
lemma example_witness_quad : star example_witness_vector ⬝ᵥ
    (((algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ)) (209/100 : ℝ) - example_witness_matrix) *ᵥ example_witness_vector) < 0 := by
  simp only [star_trivial, dotProduct, Matrix.mulVec, vecHead, vecTail, Fin.sum_univ_succ,
    Matrix.sub_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply]
  norm_num [example_witness_vector, example_witness_matrix, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.succ]

theorem op223_first_replacement_spectral_lower : ENNReal.ofReal (209 / 100 : ℝ) < adjacency_spectral_radius (op223_example_graph.deleteEdges {s(0, 1)} ⊔ SimpleGraph.fromEdgeSet {s(4, 2)}) := by
  change ENNReal.ofReal (209/100 : ℝ) < adjacency_spectral_radius example_witness_graph
  unfold adjacency_spectral_radius
  apply op223_matrix_spectral_lower _ (Matrix.isHermitian_iff_isSymm.mpr (SimpleGraph.isSymm_adjMatrix _)) _ (by norm_num) example_witness_vector
  rw [example_witness_hmat]
  exact example_witness_quad

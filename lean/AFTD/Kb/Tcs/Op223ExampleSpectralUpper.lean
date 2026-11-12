import AFTD.Prelude
import AFTD.Kb.Tcs.Op223ExampleGraph
import AFTD.Kb.Tcs.AdjacencySpectralRadius
import AFTD.Kb.Tcs.Op223MatrixSpectralUpper

/-!
# op223_example_spectral_upper

Topic: graphs   Node: 0bc9c08c9014

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; experiments 22883 and 22914

The spectral radius of the eight-vertex example tree is at most 209/100.
-/

open Matrix
open scoped ENNReal
open scoped Classical

noncomputable def example_upper_B : Matrix (Fin 8) (Fin 8) ℝ := ![![1, (-100/209), 0, 0, (-100/209), 0, 0, (-100/209)], ![0, 1, (-20900/33681), 0, (-10000/33681), 0, 0, (-10000/33681)], ![0, 0, 1, (-3368100/4949329), (-1000000/4949329), 0, 0, (-1000000/4949329)], ![0, 0, 0, 1, (-100000000/697599761), 0, 0, (-100000000/697599761)], ![0, 0, 0, 0, 1, (-69759976100/96305060049), (-69759976100/96305060049), (-236810000/460789761)], ![0, 0, 0, 0, 0, 1, (-6975997610000/13151759940241), (-4949329000000/13151759940241)], ![0, 0, 0, 0, 0, 0, 1, (-209000000/260789761)], ![0, 0, 0, 0, 0, 0, 0, 1]]

noncomputable def example_upper_d : Fin 8 → ℝ := ![(209/100), (33681/20900), (4949329/3368100), (697599761/494932900), (96305060049/69759976100), (13151759940241/9630506004900), (1290734327020369/1315175994024100), (5011770049/26078976100)]

set_option maxHeartbeats 2000000 in
lemma example_x_minus_psd : ((algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ)) (209 / 100 : ℝ) -
      op223_example_graph.adjMatrix ℝ).PosSemidef := by
  have hd : ∀ i, 0 ≤ example_upper_d i := by
    intro i; fin_cases i <;> norm_num [example_upper_d, Matrix.cons_val_zero, Matrix.cons_val_succ]
  have hp := (Matrix.posSemidef_diagonal_iff.mpr hd).conjTranspose_mul_mul_same example_upper_B
  have he : ((algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ)) (209 / 100 : ℝ) -
      op223_example_graph.adjMatrix ℝ) = example_upper_Bᴴ * Matrix.diagonal example_upper_d * example_upper_B := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.sub_apply,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply, SimpleGraph.adjMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [example_upper_B, example_upper_d, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.sub_apply,
        Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply,
        SimpleGraph.adjMatrix_apply, op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq] <;> decide
  rw [he]
  exact hp

noncomputable def example_upper_plus_B : Matrix (Fin 8) (Fin 8) ℝ := ![![1, (100/209), 0, 0, (100/209), 0, 0, (100/209)], ![0, 1, (20900/33681), 0, (-10000/33681), 0, 0, (-10000/33681)], ![0, 0, 1, (3368100/4949329), (1000000/4949329), 0, 0, (1000000/4949329)], ![0, 0, 0, 1, (-100000000/697599761), 0, 0, (-100000000/697599761)], ![0, 0, 0, 0, 1, (69759976100/96305060049), (69759976100/96305060049), (-236810000/460789761)], ![0, 0, 0, 0, 0, 1, (-6975997610000/13151759940241), (4949329000000/13151759940241)], ![0, 0, 0, 0, 0, 0, 1, (209000000/260789761)], ![0, 0, 0, 0, 0, 0, 0, 1]]

set_option maxHeartbeats 2000000 in
lemma example_x_plus_psd : ((algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ)) (209 / 100 : ℝ) +
      op223_example_graph.adjMatrix ℝ).PosSemidef := by
  have hd : ∀ i, 0 ≤ example_upper_d i := by
    intro i; fin_cases i <;> norm_num [example_upper_d, Matrix.cons_val_zero, Matrix.cons_val_succ]
  have hp := (Matrix.posSemidef_diagonal_iff.mpr hd).conjTranspose_mul_mul_same example_upper_plus_B
  have he : ((algebraMap ℝ (Matrix (Fin 8) (Fin 8) ℝ)) (209 / 100 : ℝ) +
      op223_example_graph.adjMatrix ℝ) = example_upper_plus_Bᴴ * Matrix.diagonal example_upper_d * example_upper_plus_B := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.add_apply,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply, SimpleGraph.adjMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [example_upper_plus_B, example_upper_d, Matrix.mul_apply, Fin.sum_univ_succ,
        Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.add_apply,
        Algebra.algebraMap_eq_smul_one, Matrix.smul_apply, Matrix.one_apply,
        SimpleGraph.adjMatrix_apply, op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq] <;> decide
  rw [he]
  exact hp

theorem op223_example_spectral_upper :
    adjacency_spectral_radius op223_example_graph ≤ ENNReal.ofReal (209 / 100 : ℝ) := by
  unfold adjacency_spectral_radius
  exact op223_matrix_spectral_upper _ _ example_x_minus_psd example_x_plus_psd

import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonEvalMatrix
import AFTD.Kb.Tcs.ComparisonTriangleKappa
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.ComparisonFeature2
import AFTD.Kb.Tcs.ComparisonEdge
import AFTD.Kb.Tcs.ComparisonFeature1
import AFTD.Kb.Tcs.ComparisonSign
import AFTD.Kb.Tcs.ComparisonTriangle

/-!
# comparison_triangle_kappa_mem_eval_ker

Topic: quantum   Node: 6f470fbd5387

Provenance: helper lemma. Step of arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, Lemma 1 (quadratic_comparison_evaluation_kernel_and_projector)

Each triangle relation vector kappa_abc evaluates to zero on every strict order: d_ab d_ac - d_ab d_bc + d_ac d_bc - 1 = 0.
-/

theorem comparison_triangle_kappa_mem_eval_ker (n : ℕ) (t : comparison_triangle n) :
    Matrix.mulVec (comparison_eval_matrix n) (comparison_triangle_kappa t) = 0 := by
  classical
  obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
  funext x
  simp only [Matrix.mulVec, dotProduct, comparison_eval_matrix, comparison_triangle_kappa,
    Matrix.of_apply, Pi.zero_apply, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, comparison_phi2, comparison_phi1]
  rw [Finset.prod_pair (by simp [Subtype.ext_iff, Prod.ext_iff, (ne_of_lt hbc)]),
    Finset.prod_pair (by simp [Subtype.ext_iff, Prod.ext_iff, (ne_of_lt hab)]),
    Finset.prod_pair (by simp [Subtype.ext_iff, Prod.ext_iff, (ne_of_lt hab)])]
  simp only [comparison_sign]
  have h1 : x a ≠ x b := fun h => (ne_of_lt hab) (x.injective h)
  have h2 : x a ≠ x c := fun h => (ne_of_lt (hab.trans hbc)) (x.injective h)
  have h3 : x b ≠ x c := fun h => (ne_of_lt hbc) (x.injective h)
  rw [Ne, Fin.ext_iff] at h1 h2 h3
  simp only [Fin.lt_def]
  split_ifs <;> norm_num <;> omega

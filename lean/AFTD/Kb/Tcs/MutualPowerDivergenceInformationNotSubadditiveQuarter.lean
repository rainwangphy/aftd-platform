import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformation
import AFTD.Kb.Tcs.PowerDivergenceGenerator
import AFTD.Kb.Tcs.PowerDivergenceQuarterRootBounds

/-!
# mutual_power_divergence_information_not_subadditive_quarter

Topic: information   Node: 6d090fcba3da

Provenance: original. Related work: List entry OP-332, a question proposed here from arXiv:2610.21231 (On the subadditivity of mutual f-information), Theorem 1; the paper does not discuss the power divergences with β ∈ (0, 1). Answered in the negative at β = 1/4.

Subadditivity fails for the power divergence with β = 1/4: there are random variables X, Y, Z on three-element alphabets with Y ← X → Z (p_{XYZ} = p_X p_{Y|X} p_{Z|X}) and Ĩ_{f_{1/4}}(X; YZ) > Ĩ_{f_{1/4}}(X; Y) + Ĩ_{f_{1/4}}(X; Z). Instance: X uniform on Z/3, P(Y = x + 1 | x) = 4/5 and P(Z = −x | x) = 4/5, the other values 1/10.
-/

theorem mutual_power_divergence_information_not_subadditive_quarter :
    ∃ (pX : Fin 3 → ℝ) (PY PZ : Fin 3 → Fin 3 → ℝ),
      (∀ x, 0 ≤ pX x) ∧ ∑ x, pX x = 1 ∧ (∀ x y, 0 ≤ PY x y) ∧ (∀ x, ∑ y, PY x y = 1) ∧
      (∀ x z, 0 ≤ PZ x z) ∧ (∀ x, ∑ z, PZ x z = 1) ∧
      mutual_f_information (power_divergence_generator (1 / 4)) (fun x y => pX x * PY x y) +
          mutual_f_information (power_divergence_generator (1 / 4)) (fun x z => pX x * PZ x z) <
        mutual_f_information (power_divergence_generator (1 / 4))
          (fun x (yz : Fin 3 × Fin 3) => pX x * PY x yz.1 * PZ x yz.2) := by
  refine ⟨fun _ => 1 / 3, ![![1/10, 4/5, 1/10], ![1/10, 1/10, 4/5], ![4/5, 1/10, 1/10]],
    ![![4/5, 1/10, 1/10], ![1/10, 1/10, 4/5], ![1/10, 4/5, 1/10]], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; norm_num
  · norm_num [Fin.sum_univ_three]
  · intro x y; fin_cases x <;> fin_cases y <;> norm_num
  · intro x; fin_cases x <;> simp [Fin.sum_univ_three] <;> norm_num
  · intro x y; fin_cases x <;> fin_cases y <;> norm_num
  · intro x; fin_cases x <;> simp [Fin.sum_univ_three] <;> norm_num
  · obtain ⟨a1, -⟩ := power_divergence_quarter_root_bounds (12 / 5) 1.2446 1.2447 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨a2, -⟩ := power_divergence_quarter_root_bounds (3 / 10) 0.7400 0.7401 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, b1⟩ := power_divergence_quarter_root_bounds (32 / 11) 1.3059 1.3060 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, b2⟩ := power_divergence_quarter_root_bounds (1 / 22) 0.4617 0.4618 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, b3⟩ := power_divergence_quarter_root_bounds (24 / 17) 1.0900 1.0901 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨-, b4⟩ := power_divergence_quarter_root_bounds (3 / 17) 0.6481 0.6482 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simp only [mutual_f_information, power_divergence_generator, Fintype.sum_prod_type,
      Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    norm_num at a1 a2 b1 b2 b3 b4 ⊢
    linarith

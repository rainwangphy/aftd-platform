import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformationAffineEqZero
import AFTD.Kb.Tcs.MutualFInformationSubadditive
import AFTD.Kb.Tcs.MutualFInformationAdd
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_f_information_subadditive_add_affine_iff

Topic: information   Node: 0ccefdf13201

Provenance: helper lemma. Serves OP-331 (arXiv:2610.21231 (On the subadditivity of mutual f-information), Definition 1): the standard invariance of f-divergences between probability distributions under f ↦ f + c(t - 1), carried to subadditivity; any characterization of subadditive generators can only depend on f modulo this term.

For every f : ℝ → ℝ and real c, the generator t ↦ f(t) + c (t - 1) is subadditive for mutual f-information (mutual_f_information_subadditive) if and only if f is.
-/

theorem mutual_f_information_subadditive_add_affine_iff (f : ℝ → ℝ) (c : ℝ) :
    mutual_f_information_subadditive (fun t => f t + c * (t - 1)) ↔
      mutual_f_information_subadditive f := by
  have hmain : ∀ (gen : ℝ → ℝ) (dd : ℝ), mutual_f_information_subadditive gen →
      mutual_f_information_subadditive (fun t => gen t + dd * (t - 1)) := by
    intro gen dd hgen X Y Z _ _ _ pX PY PZ hX0 hX1 hY0 hY1 hZ0 hZ1
    have hineq := hgen X Y Z pX PY PZ hX0 hX1 hY0 hY1 hZ0 hZ1
    have sY : ∑ x, ∑ y, pX x * PY x y = 1 := by
      simp only [← Finset.mul_sum, hY1, mul_one, hX1]
    have sZ : ∑ x, ∑ z, pX x * PZ x z = 1 := by
      simp only [← Finset.mul_sum, hZ1, mul_one, hX1]
    have sYZ : ∑ x, ∑ yz : Y × Z, pX x * PY x yz.1 * PZ x yz.2 = 1 := by
      simp only [Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum, hZ1, hY1, mul_one, hX1]
    rw [mutual_f_information_add gen, mutual_f_information_add gen, mutual_f_information_add gen,
      mutual_f_information_affine_eq_zero dd _ (fun x y => mul_nonneg (hX0 x) (hY0 x y)) sY,
      mutual_f_information_affine_eq_zero dd _ (fun x z => mul_nonneg (hX0 x) (hZ0 x z)) sZ,
      mutual_f_information_affine_eq_zero dd
        (fun x (yz : Y × Z) => pX x * PY x yz.1 * PZ x yz.2)
        (fun x yz => mul_nonneg (mul_nonneg (hX0 x) (hY0 x yz.1)) (hZ0 x yz.2)) sYZ]
    linarith
  refine ⟨fun h => ?_, hmain f c⟩
  have := hmain _ (-c) h
  have hineq : (fun t => f t + c * (t - 1) + -c * (t - 1)) = f := by funext t; ring
  rwa [hineq] at this

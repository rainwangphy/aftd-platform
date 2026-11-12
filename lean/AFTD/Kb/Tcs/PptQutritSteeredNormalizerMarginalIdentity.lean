import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritBellState
import AFTD.Kb.Tcs.PptQutritSteeredNormalizer
import AFTD.Kb.Tcs.PptQutritBellVector

/-!
# ppt_qutrit_steered_normalizer_marginal_identity

Topic: quantum   Node: f8081a59c63e

Provenance: helper lemma. Source-normalization helper for OP-693; see https://arxiv.org/abs/1405.4502.

The explicit inverse-square-root filter normalizes the reduced source state to the identity.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
private lemma in767_marginalproof_source_second_marginal :
    (fun x y : Fin 3 => ∑ i : Fin 3, ppt_qutrit_bell_state (i,x) (i,y)) =
      Matrix.diagonal ![(3437/6884 : ℂ), 3437/6884, 5/3442] := by
  have h2 : (Real.sqrt 2 : ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have h3 : (Real.sqrt 3 : ℂ)^2=3 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have h131 : (Real.sqrt (131 : ℝ) : ℂ)^2=131 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤131 by norm_num)
  have hn2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)))
  have hn3 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3)))
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [ppt_qutrit_bell_state, ppt_qutrit_bell_vector, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Fin.sum_univ_three, Fin.sum_univ_four, Matrix.diagonal_apply,
      Complex.real_smul, map_ofNat] <;>
    field_simp [hn2,hn3] <;> ring_nf <;> simp [h2,h3,h131] <;> norm_num

private lemma in767_marginalproof_source_normalizer_marginal :
    let M : Matrix (Fin 3) (Fin 3) ℂ := fun x y => ∑ i : Fin 3, ppt_qutrit_bell_state (i,x) (i,y)
    ppt_qutrit_steered_normalizer * M * ppt_qutrit_steered_normalizer = 1 := by
  dsimp only
  rw [in767_marginalproof_source_second_marginal]
  have h6884 : (Real.sqrt 6884 : ℂ)^2=6884 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤6884 by norm_num)
  have h3437 : (Real.sqrt 3437 : ℂ)^2=3437 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤3437 by norm_num)
  have h3442 : (Real.sqrt 3442 : ℂ)^2=3442 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤3442 by norm_num)
  have h5 : (Real.sqrt 5 : ℂ)^2=5 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
  have hn3437 : (Real.sqrt 3437 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3437)))
  have hn5 : (Real.sqrt 5 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<5)))
  have hs0 : (Real.sqrt 6884 : ℂ) / (Real.sqrt 3437 : ℂ) * (3437/6884) *
      ((Real.sqrt 6884 : ℂ) / (Real.sqrt 3437 : ℂ)) = 1 := by
    field_simp [hn3437]
    linear_combination 3437*h6884-6884*h3437
  have hs2 : (Real.sqrt 3442 : ℂ) / (Real.sqrt 5 : ℂ) * (5/3442) *
      ((Real.sqrt 3442 : ℂ) / (Real.sqrt 5 : ℂ)) = 1 := by
    field_simp [hn5]
    linear_combination 5*h3442-3442*h5
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [ppt_qutrit_steered_normalizer, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    norm_num <;> first | exact hs0 | simpa [mul_comm,mul_left_comm,mul_assoc] using hs0 | exact hs2

theorem ppt_qutrit_steered_normalizer_marginal_identity :
  let marginal : Matrix (Fin 3) (Fin 3) ℂ :=
    fun x y => ∑ a : Fin 3, ppt_qutrit_bell_state (a,x) (a,y)
  ppt_qutrit_steered_normalizer * marginal * ppt_qutrit_steered_normalizer = 1 := by
  exact in767_marginalproof_source_normalizer_marginal

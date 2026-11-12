import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritSteeredEffect
import AFTD.Kb.Tcs.BipartiteConditionalOperator
import AFTD.Kb.Tcs.PptQutritBellSetting
import AFTD.Kb.Tcs.PptQutritBellState
import AFTD.Kb.Tcs.PptQutritBellVector
import AFTD.Kb.Tcs.PptQutritSteeredNormalizer

/-!
# ppt_qutrit_steered_effect_is_valid

Topic: quantum   Node: 689c31dd8e27

Provenance: helper lemma. Helper for OP-693; construction from arXiv:1405.4502, and steering normalization in arXiv:2010.04048, Appendix A.

Each of the three normalized steered operators and its complement is positive semidefinite.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
private lemma in767_effectvalidproof_alice_setting_unit (j : Fin 3) :
    star (ppt_qutrit_bell_setting j) ⬝ᵥ ppt_qutrit_bell_setting j = 1 := by
  have h3 : (Real.sqrt 3 : ℂ)^2 = 3 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h21 : (Real.sqrt 21 : ℂ)^2 = 21 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 21 by norm_num)
  fin_cases j <;> simp [ppt_qutrit_bell_setting, dotProduct, Fin.sum_univ_three] <;>
    ring_nf <;> simp [h3,h21, map_ofNat] <;> norm_num

private lemma in767_effectvalidproof_alice_settings_valid (j : Fin 3) :
    let A : Matrix (Fin 3) (Fin 3) ℂ :=
      vecMulVec (ppt_qutrit_bell_setting j) (star (ppt_qutrit_bell_setting j))
    A.PosSemidef ∧ (1-A).PosSemidef := by
  let v := ppt_qutrit_bell_setting j
  let A : Matrix (Fin 3) (Fin 3) ℂ := vecMulVec v (star v)
  have hA : A.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have hAsq : A*A=A := by
    dsimp [A]
    rw [Matrix.vecMulVec_mul_vecMulVec, in767_effectvalidproof_alice_setting_unit j, one_smul]
  have hQherm : (1-A).IsHermitian := Matrix.isHermitian_one.sub hA.isHermitian
  have hQsq : (1-A)*(1-A)=1-A := by
    calc
      (1-A)*(1-A) = 1-A-A+A*A := by noncomm_ring
      _ = 1-A := by rw [hAsq]; abel
  have hQ := Matrix.posSemidef_conjTranspose_mul_self (1-A)
  rw [hQherm.eq, hQsq] at hQ
  exact ⟨hA,hQ⟩

private lemma in767_effectvalidproof_source_second_marginal :
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

private lemma in767_effectvalidproof_source_normalizer_marginal :
    let M : Matrix (Fin 3) (Fin 3) ℂ := fun x y => ∑ i : Fin 3, ppt_qutrit_bell_state (i,x) (i,y)
    ppt_qutrit_steered_normalizer * M * ppt_qutrit_steered_normalizer = 1 := by
  dsimp only
  rw [in767_effectvalidproof_source_second_marginal]
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

private lemma in767_effectvalidproof_normalizer_hermitian : ppt_qutrit_steered_normalizerᴴ = ppt_qutrit_steered_normalizer := by
  ext i j
  by_cases h : i = j
  · subst j
    by_cases hi : i = 2 <;> simp [ppt_qutrit_steered_normalizer, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hi]
  · simp [ppt_qutrit_steered_normalizer, Matrix.conjTranspose_apply, Matrix.diagonal_apply, h, Ne.symm h]

private lemma in767_effectvalidproof_positive_steering_from_four_vectors
    (v : Fin 4 → Fin 3 × Fin 3 → ℂ) (lam : Fin 4 → ℝ)
    (hlam : ∀ t, 0 ≤ lam t) (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : A.PosSemidef) :
    Matrix.PosSemidef (show Matrix (Fin 3) (Fin 3) ℂ from fun x y => ∑ i : Fin 3, ∑ j : Fin 3,
      (∑ t : Fin 4, (lam t : ℂ) * v t (i,x) * star (v t (j,y))) * A j i) := by
  let B : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ := fun t x i => v t (i,x)
  have hterm (t : Fin 4) : (B t * A.transpose * (B t)ᴴ).PosSemidef :=
    (Matrix.posSemidef_transpose_iff.mpr hA).mul_mul_conjTranspose_same (B t)
  have hsum : (∑ t, lam t • (B t * A.transpose * (B t)ᴴ)).PosSemidef := by
    have H (T : Finset (Fin 4)) : (∑ t ∈ T, lam t • (B t * A.transpose * (B t)ᴴ)).PosSemidef := by
      induction T using Finset.induction_on with
      | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin 3) (Fin 3) ℂ).PosSemidef)
      | @insert t T ht ih =>
        rw [Finset.sum_insert ht]
        exact ((hterm t).smul (hlam t)).add ih
    exact H Finset.univ
  have heq : (fun x y : Fin 3 => ∑ i : Fin 3, ∑ j : Fin 3,
      (∑ t : Fin 4, (lam t : ℂ) * v t (i,x) * star (v t (j,y))) * A j i) =
      ∑ t, lam t • (B t * A.transpose * (B t)ᴴ) := by
    ext x y
    simp [B, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three, Fin.sum_univ_four]
    ring
  rw [heq]
  exact hsum

private lemma in767_effectvalidproof_actual_steered_effects_valid (j : Fin 3) :
    (ppt_qutrit_steered_effect j).PosSemidef ∧ (1-ppt_qutrit_steered_effect j).PosSemidef := by
  let lam : Fin 4 → ℝ := fun t => if t = 0 then 3257/6884 else if t = 3 then 27/6884 else 450/1721
  let ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := fun ax cy =>
    ∑ t : Fin 4, (lam t : ℂ) * ppt_qutrit_bell_vector t ax * star (ppt_qutrit_bell_vector t cy)
  have hlam : ∀ t, 0 ≤ lam t := by intro t; dsimp [lam]; split_ifs <;> norm_num
  have hρ : ρ = ppt_qutrit_bell_state := by
    ext ax cy
    simp [ρ, ppt_qutrit_bell_state, lam, Fin.sum_univ_four, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, Complex.real_smul, mul_assoc]
  let S (B : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun x y =>
    ∑ i : Fin 3, ∑ k : Fin 3, ppt_qutrit_bell_state (i,x) (k,y) * B k i
  let M : Matrix (Fin 3) (Fin 3) ℂ := fun x y => ∑ i : Fin 3, ppt_qutrit_bell_state (i,x) (i,y)
  let A : Matrix (Fin 3) (Fin 3) ℂ := vecMulVec (ppt_qutrit_bell_setting j) (star (ppt_qutrit_bell_setting j))
  let N := ppt_qutrit_steered_normalizer
  have hA : A.PosSemidef ∧ (1-A).PosSemidef := in767_effectvalidproof_alice_settings_valid j
  have hS (B : Matrix (Fin 3) (Fin 3) ℂ) (hB : B.PosSemidef) : (S B).PosSemidef := by
    have hh := in767_effectvalidproof_positive_steering_from_four_vectors ppt_qutrit_bell_vector lam hlam B hB
    change Matrix.PosSemidef (show Matrix (Fin 3) (Fin 3) ℂ from fun x y =>
      ∑ i : Fin 3, ∑ k : Fin 3, ρ (i,x) (k,y) * B k i) at hh
    rw [hρ] at hh
    exact hh
  have hlin : S (1-A)=M-S A := by
    ext x y
    simp [S, M, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_three]
    ring
  have hpos : (N * S A * N).PosSemidef := by
    have hh := (hS A hA.1).mul_mul_conjTranspose_same N
    rw [in767_effectvalidproof_normalizer_hermitian] at hh
    exact hh
  have hneg : (N * S (1-A) * N).PosSemidef := by
    have hh := (hS (1-A) hA.2).mul_mul_conjTranspose_same N
    rw [in767_effectvalidproof_normalizer_hermitian] at hh
    exact hh
  have heq : N*S (1-A)*N = 1-N*S A*N := by
    rw [hlin, Matrix.mul_sub, Matrix.sub_mul, in767_effectvalidproof_source_normalizer_marginal]
  rw [heq] at hneg
  exact ⟨hpos,hneg⟩

theorem ppt_qutrit_steered_effect_is_valid : ∀ j : Fin 3, (ppt_qutrit_steered_effect j).PosSemidef ∧ (1 - ppt_qutrit_steered_effect j).PosSemidef := by
  intro j
  exact in767_effectvalidproof_actual_steered_effects_valid j

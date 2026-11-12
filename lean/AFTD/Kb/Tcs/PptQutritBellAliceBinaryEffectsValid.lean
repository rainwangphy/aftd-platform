import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritBellSetting

/-!
# ppt_qutrit_bell_alice_binary_effects_valid

Topic: quantum   Node: 06e615d53fe8

Provenance: helper lemma. Source-specific helper for OP-693; see https://arxiv.org/abs/1405.4502.

The three first-qutrit projectors used to steer the explicit source are valid binary effects.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
private lemma in767_aliceproof_alice_setting_unit (j : Fin 3) :
    star (ppt_qutrit_bell_setting j) ⬝ᵥ ppt_qutrit_bell_setting j = 1 := by
  have h3 : (Real.sqrt 3 : ℂ)^2 = 3 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h21 : (Real.sqrt 21 : ℂ)^2 = 21 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ 21 by norm_num)
  fin_cases j <;> simp [ppt_qutrit_bell_setting, dotProduct, Fin.sum_univ_three] <;>
    ring_nf <;> simp [h3,h21, map_ofNat] <;> norm_num

private lemma in767_aliceproof_alice_settings_valid (j : Fin 3) :
    let A : Matrix (Fin 3) (Fin 3) ℂ :=
      vecMulVec (ppt_qutrit_bell_setting j) (star (ppt_qutrit_bell_setting j))
    A.PosSemidef ∧ (1-A).PosSemidef := by
  let v := ppt_qutrit_bell_setting j
  let A : Matrix (Fin 3) (Fin 3) ℂ := vecMulVec v (star v)
  have hA : A.PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have hAsq : A*A=A := by
    dsimp [A]
    rw [Matrix.vecMulVec_mul_vecMulVec, in767_aliceproof_alice_setting_unit j, one_smul]
  have hQherm : (1-A).IsHermitian := Matrix.isHermitian_one.sub hA.isHermitian
  have hQsq : (1-A)*(1-A)=1-A := by
    calc
      (1-A)*(1-A) = 1-A-A+A*A := by noncomm_ring
      _ = 1-A := by rw [hAsq]; abel
  have hQ := Matrix.posSemidef_conjTranspose_mul_self (1-A)
  rw [hQherm.eq, hQsq] at hQ
  exact ⟨hA,hQ⟩

theorem ppt_qutrit_bell_alice_binary_effects_valid :
  ∀ j : Fin 3,
    let A : Matrix (Fin 3) (Fin 3) ℂ :=
      vecMulVec (ppt_qutrit_bell_setting j) (star (ppt_qutrit_bell_setting j))
    A.PosSemidef ∧ (1-A).PosSemidef := by
  intro j
  exact in767_aliceproof_alice_settings_valid j

import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritBellState
import AFTD.Kb.Tcs.PptQutritBellVector

/-!
# ppt_qutrit_bell_state_partial_transpose_invariant

Topic: quantum   Node: cecf7b4d38ff

Provenance: helper lemma. Source-state helper for OP-693; see https://arxiv.org/abs/1405.4502.

The explicit rank-four two-qutrit source is invariant under partial transpose on its first qutrit.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
private lemma in767_sourceptproof_source_partial_transpose :
    ∀ a b c d : Fin 3,
      ppt_qutrit_bell_state (a,b) (c,d) = ppt_qutrit_bell_state (c,b) (a,d) := by
  have h2 : (Real.sqrt 2 : ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have h3 : (Real.sqrt 3 : ℂ)^2=3 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have h131 : (Real.sqrt (131 : ℝ) : ℂ)^2=131 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤131 by norm_num)
  have hn2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)))
  have hn3 : (Real.sqrt 3 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3)))
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [ppt_qutrit_bell_state, ppt_qutrit_bell_vector, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Fin.sum_univ_four, Complex.real_smul, map_ofNat] <;>
    field_simp [hn2,hn3] <;> ring_nf <;> simp [h2,h3,h131] <;> norm_num

theorem ppt_qutrit_bell_state_partial_transpose_invariant :
  ∀ a b c d : Fin 3,
    ppt_qutrit_bell_state (a,b) (c,d) = ppt_qutrit_bell_state (c,b) (a,d) := by
  exact in767_sourceptproof_source_partial_transpose

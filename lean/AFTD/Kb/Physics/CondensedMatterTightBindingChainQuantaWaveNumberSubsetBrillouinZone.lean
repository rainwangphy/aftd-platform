import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterTightBindingChain
import AFTD.Kb.Physics.CondensedMatterTightBindingChainQuantaWaveNumber
import AFTD.Kb.Physics.CondensedMatterTightBindingChainBrillouinZone

/-!
# CondensedMatter.TightBindingChain.quantaWaveNumber_subset_brillouinZone

Topic: condensed_matter   Node: 6f8f98342c2a

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.TightBindingChain.quantaWaveNumber_subset_brillouinZone`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/TightBindingChain/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The quantized wavenumbers form a subset of the `BrillouinZone`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open CondensedMatter CondensedMatter.TightBindingChain in
open InnerProductSpace in
variable (T : TightBindingChain) in
/-- The quantized wavenumbers form a subset of the `BrillouinZone`. -/
lemma CondensedMatter.TightBindingChain.quantaWaveNumber_subset_brillouinZone : T.QuantaWaveNumber ⊆ T.BrillouinZone := by
  rintro _ ⟨n, rfl⟩
  have hT := T.a_pos
  have hNpos : 0 < T.N := lt_of_le_of_lt (Nat.zero_le _) n.isLt
  simp only [BrillouinZone, Set.mem_Ico]
  generalize T.N = x at *
  generalize T.a = a at *
  have hx : (0 : ℝ) < x := by exact_mod_cast hNpos
  have hn : (n : ℝ) + 1 ≤ x := by exact_mod_cast n.isLt
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hx2 : 2 * ((x / 2 : ℕ) : ℝ) ≤ x := by exact_mod_cast (by omega : 2 * (x / 2) ≤ x)
  have hx2' : (x : ℝ) ≤ 2 * ((x / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : x ≤ 2 * (x / 2) + 1)
  refine ⟨?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_div_iff₀ hT (mul_pos hT hx)]
    nlinarith [hx2, hn0, mul_pos Real.pi_pos hT]
  · rw [div_mul_eq_mul_div, div_lt_div_iff₀ (mul_pos hT hx) hT]
    nlinarith [hn, hx2', mul_pos Real.pi_pos hT]

import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterTightBindingChain
import AFTD.Kb.Physics.CondensedMatterTightBindingChainQuantaWaveNumber
import AFTD.Kb.Physics.CondensedMatterTightBindingChainInstNeZeroNatN

/-!
# CondensedMatter.TightBindingChain.quantaWaveNumber_exp_N

Topic: condensed_matter   Node: e4fc18d2192f

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_N`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/TightBindingChain/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CondensedMatter.TightBindingChain.quantaWaveNumber_exp_N
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open CondensedMatter CondensedMatter.TightBindingChain in
open InnerProductSpace in
variable (T : TightBindingChain) in
lemma CondensedMatter.TightBindingChain.quantaWaveNumber_exp_N (n : ℕ) (k : T.QuantaWaveNumber) :
    Complex.exp (Complex.I * k * n * T.N * T.a) = 1 := by
  refine Complex.exp_eq_one_iff.mpr ?_
  obtain ⟨_, m, rfl⟩ := k
  use ((m : Int) - (T.N / 2 : ℕ)) * (n : ℤ)
  have hpp : (T.N : ℂ) ≠ 0 := by simp [Ne.symm (NeZero.ne' T.N)]
  have hT' : (T.a : ℂ) ≠ 0 := Complex.ne_zero_of_re_pos T.a_pos
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_natCast,
    Complex.ofReal_sub, Int.cast_mul, Int.cast_sub, Int.cast_natCast]
  field_simp

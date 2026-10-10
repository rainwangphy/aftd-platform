import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterTightBindingChain
import AFTD.Kb.Physics.CondensedMatterTightBindingChainQuantaWaveNumber
import AFTD.Kb.Physics.CondensedMatterTightBindingChainInstNeZeroNatN
import AFTD.Kb.Physics.CondensedMatterTightBindingChainQuantaWaveNumberExpSubOne

/-!
# CondensedMatter.TightBindingChain.quantaWaveNumber_exp_add_one

Topic: condensed_matter   Node: c4ea8fefdf06

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.TightBindingChain.quantaWaveNumber_exp_add_one`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/TightBindingChain/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

CondensedMatter.TightBindingChain.quantaWaveNumber_exp_add_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open CondensedMatter CondensedMatter.TightBindingChain in
open InnerProductSpace in
variable (T : TightBindingChain) in
lemma CondensedMatter.TightBindingChain.quantaWaveNumber_exp_add_one (n : Fin T.N) (k : T.QuantaWaveNumber) :
    Complex.exp (Complex.I * k * (n + 1).val * T.a) =
    Complex.exp (Complex.I * k * n * T.a) * Complex.exp (Complex.I * k * T.a) := by
  conv_rhs =>
    rw [show n = (n + 1) - 1 from (add_sub_cancel_right n 1).symm,
      quantaWaveNumber_exp_sub_one, mul_assoc, ← Complex.exp_add]
    simp

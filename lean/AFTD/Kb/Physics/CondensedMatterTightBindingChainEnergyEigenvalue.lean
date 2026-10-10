import AFTD.Prelude
import AFTD.Kb.Physics.CondensedMatterTightBindingChain
import AFTD.Kb.Physics.CondensedMatterTightBindingChainQuantaWaveNumber

/-!
# CondensedMatter.TightBindingChain.energyEigenvalue

Topic: condensed_matter   Node: e042aae85a50

Provenance: formalization of a published result. Source: Physlib, `CondensedMatter.TightBindingChain.energyEigenvalue`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/CondensedMatter/TightBindingChain/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The energy eigenvalue of the tight binding chain for a `k` in `QuantaWaveNumber` is `E0 - 2 * t * Real.cos (k * T.a)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open CondensedMatter CondensedMatter.TightBindingChain in
open InnerProductSpace in
variable (T : TightBindingChain) in
/-- The energy eigenvalue of the tight binding chain for a `k` in `QuantaWaveNumber` is `E0 - 2 * t * Real.cos (k * T.a)`. -/
noncomputable def CondensedMatter.TightBindingChain.energyEigenvalue (k : T.QuantaWaveNumber) : ℝ :=
  T.E0 - 2 * T.t * Real.cos (k * T.a)

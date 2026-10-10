import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibDistributionPowOneMul
import AFTD.Kb.Physics.PhyslibDistribution

/-!
# Physlib.Distribution.powOneMul_apply

Topic: classical_mechanics   Node: cd695f1e4e5e

Provenance: formalization of a published result. Source: Physlib, `Physlib.Distribution.powOneMul_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Distribution/PowMul.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.Distribution.powOneMul_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Distribution in
open SchwartzMap NNReal in
variable (𝕜 : Type) {E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F] in
variable [NormedSpace ℝ E] in
open ContDiff in
open MeasureTheory in
lemma Physlib.Distribution.powOneMul_apply (ψ : 𝓢(ℝ, 𝕜)) (x : ℝ) :
    powOneMul 𝕜 ψ x = x * ψ x := rfl

import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1ChiralColor

/-!
# SUSY.N1.ChiralColor.tau

Topic: quantum_field_theory   Node: bd3901b36f87

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.ChiralColor.tau`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The dual colour: flips variance and preserves holomorphy. Two indices may contract exactly when their colours are `τ`-related, so `V^I` pairs only with `V_I` (same holomorphy, opposite variance) and never with a conjugate index.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
/-- The dual colour: flips variance and preserves holomorphy. Two indices may contract exactly when their colours are `τ`-related, so `V^I` pairs only with `V_I` (same holomorphy, opposite variance) and never with a conjugate index. -/
noncomputable def SUSY.N1.ChiralColor.tau : ChiralColor → ChiralColor
  | chiralUp => chiralDown
  | chiralDown => chiralUp
  | antiUp => antiDown
  | antiDown => antiUp

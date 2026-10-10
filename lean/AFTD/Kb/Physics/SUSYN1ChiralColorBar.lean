import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1ChiralColor

/-!
# SUSY.N1.ChiralColor.bar

Topic: quantum_field_theory   Node: ffc2603ebd32

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.ChiralColor.bar`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The conjugate colour: flips holomorphy (`chiral`↔`anti`) and preserves variance. Complex conjugation sends an index to its conjugate carrier, so `bar` swaps `chiral*` with `anti*`. Distinct from the variance dual `tau`; the two commute (`bar_tau`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
/-- The conjugate colour: flips holomorphy (`chiral`↔`anti`) and preserves variance. Complex conjugation sends an index to its conjugate carrier, so `bar` swaps `chiral*` with `anti*`. Distinct from the variance dual `tau`; the two commute (`bar_tau`). -/
noncomputable def SUSY.N1.ChiralColor.bar : ChiralColor → ChiralColor
  | chiralUp => antiUp
  | antiUp => chiralUp
  | chiralDown => antiDown
  | antiDown => chiralDown

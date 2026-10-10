import AFTD.Prelude

/-!
# Option.powerset

Topic: quantum_field_theory   Node: d717f33a222e

Provenance: formalization of a published result. Source: Physlib, `Option.powerset`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/SU5/ChargeSpectrum/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The powerset of `x : Option 𝓩` defined as `{none}` if `x` is `none` and `{none, some y}` is `x` is `some y`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓩 : Type} in
variable [DecidableEq 𝓩] in
/-- The powerset of `x : Option 𝓩` defined as `{none}` if `x` is `none` and `{none, some y}` is `x` is `some y`. -/
def Option.powerset (x : Option 𝓩) : Finset (Option 𝓩) :=
  match x with
  | none => {none}
  | some x => {none, some x}

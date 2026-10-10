import AFTD.Prelude

/-!
# SUSY.N1.ChiralScalarConfiguration

Topic: quantum_field_theory   Node: df303423dd93

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.ChiralScalarConfiguration`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The chiral scalar configuration: a complex value for each chiral label. This is the sector's only field data. Declared as an `abbrev` so that unification sees through it to `ChiralIndexingType → ℂ` and applies Mathlib's function-space calculus lemmas directly.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorProduct Module ComplexConjugate in
/-- The chiral scalar configuration: a complex value for each chiral label. This is the sector's only field data. Declared as an `abbrev` so that unification sees through it to `ChiralIndexingType → ℂ` and applies Mathlib's function-space calculus lemmas directly. -/
noncomputable abbrev SUSY.N1.ChiralScalarConfiguration (ChiralIndexingType : Type*) := ChiralIndexingType → ℂ

import AFTD.Prelude

/-!
# Cslib.Logic.InferenceSystem.Default

Topic: proof_theory   Node: a9b6116538e4

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.InferenceSystem.Default`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/InferenceSystem.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Default tag for inference system instances. `⇓a` is short for `Default⇓a`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Default tag for inference system instances. `⇓a` is short for `Default⇓a`. -/
opaque Cslib.Logic.InferenceSystem.Default : Type := Empty

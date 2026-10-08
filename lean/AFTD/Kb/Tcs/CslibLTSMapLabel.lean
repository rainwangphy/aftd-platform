import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.mapLabel

Topic: computability   Node: 880ab7de278c

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.mapLabel`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/MapLabel.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Constructs an LTS by mapping its labels into those of an existing LTS.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Constructs an LTS by mapping its labels into those of an existing LTS. -/
def Cslib.LTS.mapLabel (lts : LTS State Label₁) (f : Label₂ → Label₁) : LTS State Label₂ where
  Tr s μ s' := lts.Tr s (f μ) s'

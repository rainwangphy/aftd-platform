import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMapLabel

/-!
# Cslib.LTS.mapLabel_tr

Topic: computability   Node: 3b5fc3f3cc57

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.mapLabel_tr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/MapLabel.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.LTS.mapLabel_tr
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
theorem Cslib.LTS.mapLabel_tr {lts : LTS State Label₁} :
    (lts.mapLabel f).Tr s μ s' ↔ lts.Tr s (f μ) s' := by rfl

import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSSetImage
import AFTD.Kb.Tcs.CslibLTSImage

/-!
# Cslib.LTS.mem_setImage

Topic: computability   Node: ba771e6419eb

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.mem_setImage`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Characterisation of `setImage` wrt `Tr`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Characterisation of `setImage` wrt `Tr`. -/
@[grind =]
theorem Cslib.LTS.mem_setImage {lts : LTS State Label} :
  s' ∈ lts.setImage S μ ↔ ∃ s ∈ S, lts.Tr s μ s' := by
  simp only [setImage, Set.mem_iUnion, exists_prop]
  grind

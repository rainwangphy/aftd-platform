import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSSetImageMultistep
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSImageMultistep
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.mem_setImageMultistep

Topic: computability   Node: caa346e615d0

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.mem_setImageMultistep`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Characterisation of `setImageMultistep` with `MTr`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- Characterisation of `setImageMultistep` with `MTr`. -/
@[grind =]
theorem Cslib.LTS.mem_setImageMultistep {lts : LTS State Label} :
  s' ∈ lts.setImageMultistep S μs ↔ ∃ s ∈ S, lts.MTr s μs s' := by
  simp only [setImageMultistep, Set.mem_iUnion, exists_prop]
  grind

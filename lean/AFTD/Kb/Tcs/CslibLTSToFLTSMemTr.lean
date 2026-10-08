import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibFLTS
import AFTD.Kb.Tcs.CslibLTSToFLTS
import AFTD.Kb.Tcs.CslibLTSImage
import AFTD.Kb.Tcs.CslibLTSSetImage
import AFTD.Kb.Tcs.CslibFLTSMtrNilEq
import AFTD.Kb.Tcs.CslibFLTSMtrConcatEq

/-!
# Cslib.LTS.toFLTS_mem_tr

Topic: computability   Node: ae86ae55f5c5

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.toFLTS_mem_tr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/FLTS/LTSToFLTS.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Characterisation of transitions in `LTS.toFLTS` wrt transitions in the original `LTS`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} in
/-- Characterisation of transitions in `LTS.toFLTS` wrt transitions in the original `LTS`. -/
@[grind =]
theorem Cslib.LTS.toFLTS_mem_tr {lts : LTS State Label} {S : Set State} {s' : State} {μ : Label} :
  s' ∈ lts.toFLTS.tr S μ ↔ ∃ s ∈ S, lts.Tr s μ s' := by
  simp only [LTS.toFLTS, LTS.setImage, Set.mem_iUnion, exists_prop]
  grind

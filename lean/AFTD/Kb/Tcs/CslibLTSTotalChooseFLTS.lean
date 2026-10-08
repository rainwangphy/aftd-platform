import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSTotal
import AFTD.Kb.Tcs.CslibFLTS
import AFTD.Kb.Tcs.CslibLTSChooseFLTS
import AFTD.Kb.Tcs.CslibFLTSMtrNilEq
import AFTD.Kb.Tcs.CslibFLTSMtrConcatEq

/-!
# Cslib.LTS.Total.chooseFLTS

Topic: computability   Node: 4d3d921bbc01

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Total.chooseFLTS`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Total.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The FLTS chosen by `chooseFLTS` always provides legal transitions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- The FLTS chosen by `chooseFLTS` always provides legal transitions. -/
theorem Cslib.LTS.Total.chooseFLTS (lts : LTS State Label) [h : lts.Total] (s : State) (μ : Label) :
    lts.Tr s μ (lts.chooseFLTS.tr s μ) :=
  Classical.choose_spec <| h.total s μ

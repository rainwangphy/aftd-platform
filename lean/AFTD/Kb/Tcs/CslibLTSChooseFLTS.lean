import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSTotal
import AFTD.Kb.Tcs.CslibFLTS
import AFTD.Kb.Tcs.CslibFLTSMtrNilEq
import AFTD.Kb.Tcs.CslibFLTSMtrConcatEq

/-!
# Cslib.LTS.chooseFLTS

Topic: computability   Node: b0d20e3060d7

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.chooseFLTS`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Total.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Choose an FLTS that is a "sub-LTS" of a total LTS.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
variable {State Label : Type*} {lts : LTS State Label} in
/-- Choose an FLTS that is a "sub-LTS" of a total LTS. -/
noncomputable def Cslib.LTS.chooseFLTS (lts : LTS State Label) [h : lts.Total] : FLTS State Label where
  tr s μ := Classical.choose <| h.total s μ

import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCCSAct
import AFTD.Kb.Tcs.CslibCCSActCo

/-!
# Cslib.CCS.Act.Co.symm

Topic: distributed   Node: 572fe846116c

Provenance: formalization of a published result. Source: CSLib, `Cslib.CCS.Act.Co.symm`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CCS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`Act.Co` is symmetric.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- `Act.Co` is symmetric. -/
@[scoped grind →, symm]
theorem Cslib.CCS.Act.Co.symm (h : Act.Co μ μ') : Act.Co μ' μ := by grind

import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCCSAct

/-!
# Cslib.CCS.Process

Topic: distributed   Node: 24938c879002

Provenance: formalization of a published result. Source: CSLib, `Cslib.CCS.Process`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CCS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Processes.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- Processes. -/
inductive Cslib.CCS.Process (Name : Type u) (Constant : Type v) : Type (max u v) where
  | nil
  | pre (μ : Act Name) (p : Process Name Constant)
  | par (p q : Process Name Constant)
  | choice (p q : Process Name Constant)
  | res (a : Name) (p : Process Name Constant)
  | const (c : Constant)
deriving DecidableEq

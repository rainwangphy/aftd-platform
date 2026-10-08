import AFTD.Prelude

/-!
# Cslib.Logic.CLL.MLL

Topic: proof_theory   Node: 4cd3c71c5a2d

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.MLL`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/MLL.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Tag for the MLL inference system.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Tag for the MLL inference system. -/
opaque Cslib.Logic.CLL.MLL : Type := Empty

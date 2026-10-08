import AFTD.Prelude

/-!
# Cslib.FLP.ZeroFaultAlg.S

Topic: distributed   Node: b541996ec2ca

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLP.ZeroFaultAlg.S`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Distributed/FLP/ZeroConsensus.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The local state of a process is trivial.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Sum Option Multiset in
/-- The local state of a process is trivial. -/
abbrev Cslib.FLP.ZeroFaultAlg.S := Unit

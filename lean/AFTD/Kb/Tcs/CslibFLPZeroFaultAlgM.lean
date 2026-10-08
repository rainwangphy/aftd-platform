import AFTD.Prelude

/-!
# Cslib.FLP.ZeroFaultAlg.M

Topic: distributed   Node: a665a6c05ed0

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLP.ZeroFaultAlg.M`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Distributed/FLP/ZeroConsensus.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The payload of a message is of type `Bool ⊕ Bool`, where `inl b` denotes an input value `b` and `inr b` denotes a value `b` sent by process 0 to all processes (including itself).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set Sum Option Multiset in
/-- The payload of a message is of type `Bool ⊕ Bool`, where `inl b` denotes an input value `b` and `inr b` denotes a value `b` sent by process 0 to all processes (including itself). -/
abbrev Cslib.FLP.ZeroFaultAlg.M := Bool

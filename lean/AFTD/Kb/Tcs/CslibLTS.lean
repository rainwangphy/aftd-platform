import AFTD.Prelude

/-!
# Cslib.LTS

Topic: computability   Node: d53203c32e65

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Labelled Transition System (LTS) for a type of states (`State`) and a type of transition labels (`Label`) consists of a labelled transition relation (`Tr`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- A Labelled Transition System (LTS) for a type of states (`State`) and a type of transition labels (`Label`) consists of a labelled transition relation (`Tr`). -/
@[ext]
structure Cslib.LTS (State : Type u) (Label : Type v) where
  /-- The transition relation. -/
  Tr : State → Label → State → Prop

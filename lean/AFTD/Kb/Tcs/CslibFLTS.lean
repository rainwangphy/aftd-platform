import AFTD.Prelude

/-!
# Cslib.FLTS

Topic: computability   Node: d299d15cb83b

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLTS`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/FLTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A Functional Labelled Transition System (`FLTS`) for a type of states (`State`) and a type of transition labels (`Label`) consists of a labelled transition function (`tr`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A Functional Labelled Transition System (`FLTS`) for a type of states (`State`) and a type of transition labels (`Label`) consists of a labelled transition function (`tr`). -/
structure Cslib.FLTS (State Label : Type*) where
  /-- The transition function. -/
  tr : State → Label → State

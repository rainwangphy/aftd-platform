import AFTD.Prelude

/-!
# Cslib.Logic.HML.Proposition

Topic: distributed   Node: fd160aa73f1d

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HML.Proposition`. Lean proof by Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/HML/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Propositions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Propositions. -/
inductive Cslib.Logic.HML.Proposition (Label : Type u) : Type u where
  /-- Truth. -/
  | true
  /-- Conjunction. -/
  | and (φ₁ φ₂ : Proposition Label)
  /-- Negation. -/
  | not (φ : Proposition Label)
  /-- Possibility (dynamic diamond modality). -/
  | diamond (μ : Label) (φ : Proposition Label)
